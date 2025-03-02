#!/usr/bin/env python3
# -*- coding: utf8

# buildings2osm
# Converts buildings from Lantmäteriet to geosjon file for import to OSM.
# Usage: buildings2osm.py <municipality name> [geojson or gpkg input filename] [-heritage] [-split] [-original] [-verify] [-debug] [-noheritage]
# Creates geojson file with name "byggnader_2181_Sandviken.geojson" etc.


import sys
import time
import copy
import math
import statistics
import csv
import json
import os
import io
import base64
import urllib.request, urllib.error
import zipfile
import subprocess


version = "0.10.0"

debug = False				# Add debugging / testing information
verify = False				# Add tags for users to verify
original = False			# Output polygons as in original data (no rectification/simplification)

precision = 7				# Number of decimals in coordinate output

snap_margin = 0.20 			# Max margin for connecting building nodes/edges (meters)

angle_margin = 8.0 			# Max margin around angle limits, for example around 90 degrees corners (degrees)
short_margin = 0.15			# Min length of short wall which will be removed if on "straight" line (meters)
corner_margin = 0.5			# Max length of short wall which will be rectified even if corner is outside of 90 +/- angle_margin (meters)
rectify_margin = 0.3		# Max relocation distance for nodes during rectification before producing information tag (meters)

simplify_curve_margin = 0.03	# Minimum tolerance for buildings with curves in simplification (meters)
simplify_line_margin = 0.05 	# Minimum tolerance for buildings with lines in simplification (meters)

curve_margin_max = 40		# Max angle for a curve (degrees)
curve_margin_min = 0.3		# Min angle for a curve (degrees)
curve_margin_nodes = 3		# At least three nodes in a curve (number of nodes)

spike_margin = 170			# Max angle/bearing for spikes (degrees)

token_filename = "geotorget_token.txt"	# Stored Geotorget credentials
token_folder = "~/downloads/"			# Folder where token is stored, if not in current folder



# Output message to console

def message (text):

	sys.stderr.write(text)
	sys.stderr.flush()



# Format time

def timeformat (sec):

	if sec > 3600:
		return "%i:%02i:%02i hours" % (sec / 3600, (sec % 3600) / 60, sec % 60)
	elif sec > 60:
		return "%i:%02i minutes" % (sec / 60, sec % 60)
	else:
		return "%i seconds" % sec



# Format decimal number

def format_decimal(number):

	if number:
		number = "%.1f" % float(number)
		return number.rstrip("0").rstrip(".")
	else:
		return ""



# Compute approximation of distance between two coordinates, (lat,lon), in meters
# Works for short distances

def distance (point1, point2):

	lon1, lat1, lon2, lat2 = map(math.radians, [point1[0], point1[1], point2[0], point2[1]])
	x = (lon2 - lon1) * math.cos( 0.5*(lat2+lat1) )
	y = lat2 - lat1
	return 6371000.0 * math.sqrt( x*x + y*y )  # Metres



# Calculate coordinate area of polygon in square meters
# Simple conversion to planar projection, works for small areas
# < 0: Clockwise
# > 0: Counter-clockwise
# = 0: Polygon not closed

def polygon_area (polygon):

	if polygon[0] == polygon[-1]:
		lat_dist = math.pi * 6371000.0 / 180.0

		coord = []
		for node in polygon:
			y = node[1] * lat_dist
			x = node[0] * lat_dist * math.cos(math.radians(node[1]))
			coord.append((x,y))

		area = 0.0
		for i in range(len(coord) - 1):
			area += (coord[i+1][0] - coord[i][0]) * (coord[i+1][1] + coord[i][1])  # (x2-x1)(y2+y1)

		return int(area / 2.0)
	else:
		return 0



# Calculate centre of polygon, or of list of nodes

def polygon_centre (polygon):

	length = len(polygon)
	if polygon[0] == polygon[-1]:
		length -= 1

	x = 0
	y = 0
	for node in polygon[:length]:
		x += node[0]
		y += node[1]
	return (x / length, y / length)



# Return bearing in degrees of line between two points (longitude, latitude)

def bearing (point1, point2):

	lon1, lat1, lon2, lat2 = map(math.radians, [point1[0], point1[1], point2[0], point2[1]])
	dLon = lon2 - lon1
	y = math.sin(dLon) * math.cos(lat2)
	x = math.cos(lat1) * math.sin(lat2) - math.sin(lat1) * math.cos(lat2) * math.cos(dLon)
	angle = (math.degrees(math.atan2(y, x)) + 360) % 360
	return angle



# Return the difference between two bearings.
# Negative degrees to the left, positive to the right.

def bearing_difference (bearing1, bearing2):

	delta = (bearing2 - bearing1 + 360) % 360

	if delta > 180:
		delta = delta - 360

	return delta



# Return the shift in bearing at a junction.
# Negative degrees to the left, positive to the right. 

def bearing_turn (point1, point2, point3):

	bearing1 = bearing(point1, point2)
	bearing2 = bearing(point2, point3)

	return bearing_difference(bearing1, bearing2)



# Rotate point with specified angle around axis point.
# https://gis.stackexchange.com/questions/246258/transforming-data-from-a-rotated-pole-lat-lon-grid-into-regular-lat-lon-coordina

def rotate_node (axis, r_angle, point):

	r_radians = math.radians(r_angle)  # *(math.pi/180)

	tr_y = point[1] - axis[1]
	tr_x = (point[0] - axis[0]) * math.cos(math.radians(axis[1]))

	xrot = tr_x * math.cos(r_radians) - tr_y * math.sin(r_radians)  
	yrot = tr_x * math.sin(r_radians) + tr_y * math.cos(r_radians)

	xnew = xrot / math.cos(math.radians(axis[1])) + axis[0]
	ynew = yrot + axis[1]

	return (xnew, ynew)



# Compute closest distance from point p3 to line segment [s1, s2].
# Works for short distances.

def line_distance(s1, s2, p3, get_point=False):

	x1, y1, x2, y2, x3, y3 = map(math.radians, [s1[0], s1[1], s2[0], s2[1], p3[0], p3[1]])

	# Simplified reprojection of latitude
	x1 = x1 * math.cos( y1 )
	x2 = x2 * math.cos( y2 )
	x3 = x3 * math.cos( y3 )

	A = x3 - x1
	B = y3 - y1
	dx = x2 - x1
	dy = y2 - y1

	dot = (x3 - x1)*dx + (y3 - y1)*dy
	len_sq = dx*dx + dy*dy

	if len_sq != 0:  # in case of zero length line
		param = dot / len_sq
	else:
		param = -1

	if param < 0:
		x4 = x1
		y4 = y1
	elif param > 1:
		x4 = x2
		y4 = y2
	else:
		x4 = x1 + param * dx
		y4 = y1 + param * dy

	# Also compute distance from p to segment

	x = x4 - x3
	y = y4 - y3
	distance = 6371000 * math.sqrt( x*x + y*y )  # In meters

	if not get_point:
		return distance

	# Project back to longitude/latitude

	x4 = x4 / math.cos(y4)

	lon = math.degrees(x4)
	lat = math.degrees(y4)

	return (lon, lat), distance



# Generate coordinates for circle with n nodes

def generate_circle(centre, radius, n):

	cy = math.radians(centre[1])
	cx = math.radians(centre[0]) * math.cos( cy )
	r = radius / 6371000.0
	polygon = []

	for t in range(n + 1):
		y = cy + r * math.sin(t * 2 * math.pi / n)
		x = (cx + r * math.cos(t * 2 * math.pi / n))
		lat = math.degrees(y)
		lon = math.degrees(x / math.cos(cy))
		polygon.append( ( round(lon, precision), round(lat, precision) ) )

	return polygon



# Calculate Hausdorff distance, including reverse.
# Abdel Aziz Taha and Allan Hanbury: "An Efficient Algorithm for Calculating the Exact Hausdorff Distance"
# https://publik.tuwien.ac.at/files/PubDat_247739.pdf

def hausdorff_distance (p1, p2):

	N1 = len(p1) - 1
	N2 = len(p2) - 1

# Shuffling for small lists disabled
#	random.shuffle(p1)
#	random.shuffle(p2)

	cmax = 0
	for i in range(N1):
		no_break = True
		cmin = 999999.9  # Dummy

		for j in range(N2):

			d = line_distance(p2[j], p2[j+1], p1[i])
    
			if d < cmax: 
				no_break = False
				break

			if d < cmin:
				cmin = d

		if cmin < 999999.9 and cmin > cmax and no_break:
			cmax = cmin

#	return cmax

	for i in range(N2):
		no_break = True
		cmin = 999999.9  # Dummy

		for j in range(N1):

			d = line_distance(p1[j], p1[j+1], p2[i])
    
			if d < cmax:
				no_break = False
				break

			if d < cmin:
				cmin = d

		if cmin < 999999.9 and cmin > cmax and no_break:
			cmax = cmin

	return cmax



# Simplify polygon, i.e. reduce nodes within epsilon distance.
# Ramer-Douglas-Peucker method: https://en.wikipedia.org/wiki/Ramer–Douglas–Peucker_algorithm

def simplify_polygon(polygon, epsilon):

	dmax = 0.0
	index = 0
	for i in range(1, len(polygon) - 1):
		d = line_distance(polygon[0], polygon[-1], polygon[i])
		if d > dmax:
			index = i
			dmax = d

	if dmax >= epsilon:
		new_polygon = simplify_polygon(polygon[:index+1], epsilon)[:-1] + simplify_polygon(polygon[index:], epsilon)
	else:
		new_polygon = [polygon[0], polygon[-1]]

	return new_polygon



# Calculate new node with given distance offset in meters
# Works over short distances

def coordinate_offset (node, distance):

	m = (1 / ((math.pi / 180.0) * 6378137.0))  # Degrees per meter

	latitude = node[1] + (distance * m)
	longitude = node[0] + (distance * m) / math.cos( math.radians(node[1]) )

	return (longitude, latitude)



# Produce bbox for polygon

def get_bbox(polygon):

	min_bbox = (min([ node[0] for node in polygon ]), min([ node[1] for node in polygon ]))
	max_bbox = (max([ node[0] for node in polygon ]), max([ node[1] for node in polygon ]))
	return min_bbox, max_bbox



# Determine overlap between bbox

def bbox_overlap(min_bbox1, max_bbox1, min_bbox2, max_bbox2):

	return (min_bbox1[0] <= max_bbox2[0] and max_bbox1[0] >= min_bbox2[0]
			and min_bbox1[1] <= max_bbox2[1] and max_bbox1[1] >= min_bbox2[1])



# Load dict of all municipalities

def load_municipalities():

	url = "https://catalog.skl.se/rowstore/dataset/4c544014-8e8f-4832-ab8e-6e787d383752/json?_limit=400"
	try:
		file = urllib.request.urlopen(url)
	except urllib.error.HTTPError as e:
		sys.exit("\t*** Failed to load municiaplity names, HTTP error %i: %s\n\n" % (e.code, e.reason))
	data = json.load(file)
	file.close()

	municipalities['00'] = "Sverige"
	for municipality in data['results']:
		ref = municipality['kommunkod']
		if len(ref) < 4:
			ref = "0" + ref
		municipalities[ ref ] = municipality['kommun']



# Identify municipality name, unless more than one hit.
# Returns municipality number.

def get_municipality (parameter):

	if parameter.isdigit() and parameter in municipalities:
		return parameter
	else:
		found_ids = []
		for mun_id, mun_name in iter(municipalities.items()):
			if parameter.lower() == mun_name.lower():
				return mun_id
			elif parameter.lower() in mun_name.lower():
				found_ids.append(mun_id)

		if len(found_ids) == 1:
			return found_ids[0]
		elif not found_ids:
			sys.exit("*** Municipality '%s' not found\n\n" % parameter)
		else:
			mun_list = [ "%s %s" % (mun_id, municipalities[ mun_id ]) for mun_id in found_ids ]
			sys.exit("*** Multiple municipalities found for '%s' - please use full name:\n%s\n\n" % (parameter, ", ".join(mun_list)))



# Get stored Geotorget token or ask for credentials

def get_token():

	filename = token_filename

	if not os.path.isfile(filename):
		test_filename = os.path.expanduser(token_folder + filename)
		if os.path.isfile(test_filename):
			filename = test_filename

	if os.path.isfile(filename):		
		message ("Loading Geotorget credentials from file '%s'\n\n" % filename)
		file = open(filename)
		token = file.read()
		file.close()
	else:
		message ("Please provide Geotorget login (you need approval for 'Byggnad Nedladdning, vektor') ...\n")
		username = input("\tUser name: ")
		password = input("\tPassword:  ")
		token = username + ":" + password
		token = base64.b64encode(token.encode()).decode()
		file = open(filename, "w")
		file.write(token)
		file.close()
		message ("\tStoring credentials in file '%s'\n\n" % filename)

	return token



# Load conversion json table from GitHub for tagging building types.

def load_building_types():

	url = "https://raw.githubusercontent.com/NKAmapper/building2osm-Sweden/main/building_tags.json"
	try:
		file = urllib.request.urlopen(url)
	except urllib.error.HTTPError as e:
		sys.exit("\t*** Failed to load building types, HTTP error %i: %s\n\n" % (e.code, e.reason))
	data = json.load(file)
	file.close()

	for row in data:
		name = row['purpose']
		if name == "Ospecificerad":
			name += " " + row['object_type'].lower()
		if not name:
			name = row['object_type']

		osm_tags = { 'building': 'yes' }
		osm_tags.update(row['tags'])

		building_types[ row['object_type'] + ";" + row['purpose'] ] = {
			'name': name,
			'tags': osm_tags
		}



# Load heritage buildings

def load_heritage_buildings(save_heritage=False):

	# Internal functions for converting upper case name to titled name using Swedish dictionary

	def swedish_title(name):

		# Deliver next word with proper capitlization and update word usage stats

		def next_word(first, word):
			if first or (word.lower() not in dictionary and "kyrk" not in word.lower() and "kapell" not in word.lower()):
				if not first:
					if word.lower() not in words:
						words[ word.lower() ] = 0
					words [ word.lower() ] += 1  # Update stats
				return word.title()
			else:
				return word.lower()			


		# Identify each word and capitalize first character if not found in dictionary

		new_name = ""
		word = ""
		first = True
		for i, ch in enumerate(name):
			if ch.isalpha():
				word += ch
			else:
				if word:
					new_name += next_word(first, word)
					word = ""
					first = False
				new_name += ch
				if ch in [";", "(", ")", ",", ".", "-", "/"]:
					first = True

		if word:
			new_name += next_word(first, word)

		new_name = new_name.replace("- Och ", "- och ").replace("  ", " ").strip()
		return new_name


	# Import GeoPandas for Geopackage loading

	from geopandas import gpd
	import warnings

	warnings.filterwarnings(
	    action="ignore",
	    message=".*has GPKG application_id, but non conformant file extension.*"
	)

	message ("Loading heritage buildings from Riksantikvarieämbetet ...\n")

	# Load Swedish dictionary to get upper/lowercase right (MIT license)

	dictionary = set()
	url = "https://raw.githubusercontent.com/martinlindhe/wordlist_swedish/refs/heads/master/swe_wordlist"
#	url = "https://raw.githubusercontent.com/LordGurr/SwedishDictionary/refs/heads/main/en-US_User.dic"
	try:
		file = urllib.request.urlopen(url)
	except urllib.error.HTTPError as e:
		sys.exit("\t*** Failed to load Swedish dictionary, HTTP error %i: %s\n\n" % (e.code, e.reason))

	for line in io.TextIOWrapper(file, encoding='utf-8'):
		word = line.strip()
		if word: # and word.lower() == word:
			dictionary.add(word.lower())
	file.close()

	# Additional words not found in dictionary
	dictionary.update(["de", "militärläger", "gravkoret", "vagnslider", "lave", "anten", "fiskeläge", "flygelbyggnaden",
						"tygstationen", "mölla", "gravkor", "kungsgård", "byggningen", "fyrplats", "landsförsamlings",
						"tröskvandring", "migrering", "tröskhus"])

	if debug or verify:
		message ("\tLoaded %i dictionary entries\n" % len(dictionary))

	# Load hertiage buildings from Swedish National Heritage Board

	url = "https://pub.raa.se/nedladdning/datauttag/bebyggelse/byggnader_kulthist_inv/byggnader_sverige.gpkg"
	try:
		gdf = gpd.read_file(url, layer="byggnader_sverige_point")
	except urllib.error.HTTPError as e:
		sys.exit("\t*** Failed to load heritage buildings, HTTP error %i: %s\n\n" % (e.code, e.reason))

	gdf = gdf.to_crs("EPSG:4326")  # Transform projection from EPSG:3006
	gdf['senast_andrad'] = gdf['senast_andrad'].dt.strftime("%Y-%m-%d")  # Fix type

	features = []
	words = {}

	for feature in gdf.iterfeatures(na="drop", drop_id=True):	
		if "lagskydd_id" in feature['properties'] and "fast_byg_uuid" in feature['properties']:
			if "namn" in feature['properties'] and feature['properties']['namn'].strip():
				name = swedish_title(feature['properties']['namn'])
				heritage_buildings[ feature['properties']['fast_byg_uuid'] ] = name  # Store name/description only
				feature['properties']['name'] = name
			else:
				heritage_buildings[ feature['properties']['fast_byg_uuid'] ] = ""				

			if save_heritage:
				features.append(feature)

	message ("\tLoaded %i heritage buildings for Sweden\n\n" % len(heritage_buildings))

	if save_heritage:
		feature_collection = {
			'type': 'FeatureCollection',
			'features': features
		}

		filename = "heritage_sweden.geojson",
		file = open(filename, "w")
		json.dump(feature_collection, file, indent=2, ensure_ascii=False)
		file.close()

		if debug:
			file = open("heritage_words_sweden.txt", "w")
			for word in sorted(words.items(), key=lambda item: item[1], reverse=True):
				file.write("%3i %s\n" % (word[1], word[0]))
			file.close()

		message ("\tSaved building points in file '%s'\n" % filename)



# Load building polygons from Lantmäteriet Geotorget or from local file.
# Tag for OSM and include heritage information.

def load_buildings(municipality_id, filename=""):

	message ("Load building polygons ...\n")

	# Load GeoJSON file

	if filename and ".geojson" in filename:

		message ("\tLoading from file '%s' ...\n" % filename)

		file = open(filename)
		data = json.load(file)
		file.close()

		# Standardise geometry to Polygon

		for feature in data['features']:
			if feature['geometry']['type'] == "MultiPolygon":
				coordinates = feature['geometry']['coordinates'][0]  # One outer area only
			elif feature['geometry']['type'] == "Polygon":
				coordinates = feature['geometry']['coordinates']
			elif feature['geometry']['type'] == "LineString":
				coordinates = [ feature['geometry']['coordinates'] ]
			else:
				coordinates = []

			if coordinates and len(coordinates[0]) > 3:
				for i, polygon in enumerate(coordinates):
					coordinates[ i ] = [ tuple(( round(node[0], precision), round(node[1], precision) )) for node in polygon ]

				feature['geometry']['type'] = "Polygon"
				feature['geometry']['coordinates'] = coordinates
				buildings.append(feature)

	# Load GeoPackage file

	else:
		# Import GeoPandas for Geopackage loading

		from geopandas import gpd
		import warnings

		warnings.filterwarnings(
		    action="ignore",
		    message=".*has GPKG application_id, but non conformant file extension.*"
		)

		if filename:
			# Load local GeoPackage file

			message ("\tLoading file '%s' ...\n" % filename)
			gdf = gpd.read_file(filename)

		else:
			# Load from Geotorget

			message ("\tLoading from Lantmäteriet ...\n")

			header = { 'Authorization': 'Basic ' +  token }
			url = "https://dl1.lantmateriet.se/byggnadsverk/byggnad_kn%s.zip" % municipality_id
			filename = "byggnad_kn%s.gpkg" % municipality_id
			request = urllib.request.Request(url, headers = header)

			try:
				file_in = urllib.request.urlopen(request)
			except urllib.error.HTTPError as e:
				message ("\t*** HTTP error %i: %s\n" % (e.code, e.reason))
				if e.code == 401:  # Unauthorized
					message ("\t*** Wrong username (email) or password, or you need approval for 'Byggnad nedladdning, direkt' at Geotorget\n\n")
					os.remove(token_filename)
					sys.exit()
				elif e.code == 403:  # Blocked
					sys.exit()
				else:
					return

			zip_file = zipfile.ZipFile(io.BytesIO(file_in.read()))
			file = zip_file.open(filename)

			gdf = gpd.read_file(file)

			file.close()
			zip_file.close()
			file_in.close()

		# Transform to GeoJSON format

		gdf = gdf.to_crs("EPSG:4326")  # Transform projection from EPSG:3006
		gdf['versiongiltigfran'] = gdf['versiongiltigfran'].dt.strftime("%Y-%m-%d")  # Fix type

		for feature in gdf.iterfeatures(na="drop", drop_id=True):
			if isinstance(feature['geometry']['coordinates'][0][0], float):  # LineString
				coordinates = [ feature['geometry']['coordinates'] ]
			elif isinstance(feature['geometry']['coordinates'][0][0][0], float):  # Polygon
				coordinates = feature['geometry']['coordinates']
			elif isinstance(feature['geometry']['coordinates'][0][0][0][0], float):  # Multipolygon
				coordinates = feature['geometry']['coordinates'][0]
			else:
				coordinates = []

			if coordinates and len(coordinates[0]) > 3:
				feature['geometry']['coordinates'] = [ [ (round(node[0], precision), round(node[1], precision))
														for node  in polygon ] for polygon in coordinates ]
				feature['geometry']['type'] = "Polygon"
				buildings.append(feature)

	# Iterate all buildings and assign tags

	building_refs = {}  # Index - list of buildings with same ref
	not_found = []  # Purpose in dataset not defined

	for building in buildings:
		properties = building['properties']
		tags = {}

		# Get identifier, unique if house number added

		ref = properties['objektidentitet']
		tags['ref:lantmateriet:byggnad'] = ref

#		house_ref = ""
#		if "husnummer" in properties and properties['husnummer']:
#			house_ref = str(int(properties['husnummer']))
#			tags['ref:lantmateriet:byggnad'] += ":" + house_ref

		# Determine building type and add building tag

		building_type_list = []

		for purpose in ['andamal1', 'andamal2' , 'andamal3', 'andamal4']:
			if purpose in properties and properties[ purpose ]:
				building_type = properties[ purpose ]
				building_type_list.append(building_type)
				if building_type not in building_types and building_type not in not_found:
					not_found.append(building_type)

			if not building_type_list and "objekttyp" in properties and properties['objekttyp']:
				building_type = ( properties['objekttyp'] + ";" )
				building_type_list = [ building_type ]
				if building_type not in building_types and building_type not in not_found:
					not_found.append(building_type)

		tags['building'] = "yes"
		if building_type_list:
			for building_type in building_type_list:
				if building_type in building_types:
					tags.update(building_types[ building_type ]['tags'])
					break

			type_description = ", ".join([ building_types[ building_type ]['name']
											for building_type in building_type_list if building_type in building_types ] )
			if type_description:
				tags['BTYPE'] = type_description

		# Adjust building=* based on size

		if (building['geometry']['type'] == "Polygon"
				and "BTYPE" in tags
				and tags['BTYPE'] in ["Småhus radhus", "Ekonomibyggnad", "Komplementbyggnad"]):

			area = abs(polygon_area(building['geometry']['coordinates'][0]))
			if tags['BTYPE'] in ["Ekonomibyggnad", "Komplementbyggnad"] and area < 15:
				tags['building'] = "shed"

			elif tags['BTYPE'] == "Ekonomibyggnad" and area > 100:
				tags['building'] = "barn"

			elif tags['BTYPE'] == "Småhus radhus" and area > 250:
				tags['building'] = "terrace"

		# Add extra information

		names = []
		for tag in ["byggnadsnamn1", "byggnadsnamn2", "byggnadsnamn3"]:
			if tag in properties and properties[ tag ].strip():
				name = properties[ tag ].replace("  ", " ").strip()
				names.append(name)

				name = name.lower()
				if tags['building'] == "religious":
					if "kyrka" in name:
						tags['building'] = "church"
					elif "kapell" in name:
						tags['building'] = "chapel"

		if names:
			tags['name'] = names[0]
			if len(names) > 1:
				tags['alt_name'] = ";".join(names[1:])

		if "versiongiltigfran" in properties and properties['versiongiltigfran']:
			tags['DATE'] = properties['versiongiltigfran'][:10]
			if "objektversion" in properties and properties['objektversion']:
				tags['DATE'] += " v" + str(properties['objektversion'])

#		if "ursprunglig_organisation" in properties and properties['ursprunglig_organisation']:
#			tags['SOURCE'] = properties['ursprunglig_organisation'][0].upper() + properties['ursprunglig_organisation'][1:]

#		if "huvudbyggnad" in properties and properties['huvudbyggnad'] == "Ja":
#			tags['MAIN'] = "yes"

		# Add heritage tags

		if ref in heritage_buildings:
			tags['heritage'] = "yes"
			name = heritage_buildings[ ref ].lower()
			if (name
					and not ("name" in tags and name == tags['name'].lower())
					and not ("alt_name" in tags and name == tags['alt_name'].lower())):
				tags['description'] = heritage_buildings[ ref ]
				if tags['building'] == "religious":
					if "kyrka" in name:
						tags['building'] = "church"
					elif "kapell" in name:
						tags['building'] = "chapel"
				if "klockstapel" in name or "klocktorn" in name:
					tags['building'] = "bell_tower"

		building['properties'] = tags

		# Mark if multiple buildings have same ref

		if ref in building_refs:
			if len(building_refs[ ref ]) == 1:
				building_refs[ ref ][0]['properties']['MULTI'] = "yes"
			building['properties']['MULTI'] = "yes"
			building_refs[ ref ].append(building)

		else:
			building_refs[ ref ] = [ building ]

	count_polygons = sum((building['geometry']['type'] == "Polygon") for building in buildings)
	message ("\tLoaded %i building polygons\n" % count_polygons)
	if not_found:
		message ("\t*** Building type(s) not found: %s\n" % (", ".join(sorted([ purpose for purpose in not_found ]))))

	verify_building_geometry()



# Check for duplicate nodes, "spike" nodes (sharp angles) and segments

def verify_building_geometry(check_short_segments=False):

	# 1. Check for duplicate nodes

	count_nodes = 0
	for building in buildings:
		for i, polygon in enumerate(building['geometry']['coordinates']):
			if len(polygon) != len(set(polygon)) + 1:
				new_polygon = []
				last_node = None
				for node in polygon:
					if node != last_node:
						new_polygon.append(node)
					last_node = node
				if new_polygon != polygon:
					building['geometry']['coordinates'][ i ] = new_polygon
					count_nodes += 1

	# 2. Check for duplicate segments

	count_segments = 0
	for building in buildings:
		for i, polygon in enumerate(building['geometry']['coordinates']):	
			if len(polygon) != len(set(polygon)) + 1:
				found = True
				new_polygon = polygon[1:]
				while found and len(new_polygon) > 2:   # Iterate until no adjustment

					found = False
					for j in range(1, len(new_polygon) - 1):
						if new_polygon[ j - 1 ] == new_polygon[ j + 1 ]:
							removed_nodes.add(new_polygon[ j ])
							new_polygon = new_polygon[ : j - 1 ] + new_polygon[ j + 1 : ]
							found = True
							break

					if not found:
						# Special case: Duplicate segment wrapped around start/end of polygon
						if new_polygon[-1] == new_polygon[1]:
							removed_nodes.add(new_polygon[0])
							new_polygon = new_polygon[1:-1]
							found = True
						elif new_polygon[-2] == new_polygon[0]:
							removed_nodes.add(new_polygon[-1])
							new_polygon = new_polygon[:-2]
							found = True

				if new_polygon:
					new_polygon = [ new_polygon[-1] ] + new_polygon

				if new_polygon != polygon:
					building['geometry']['coordinates'][ i ] = new_polygon
					count_segments += 1

	# 3. Check for sharp angles ("spike" nodes)

	count_spikes = 0
	for building in buildings:
		for i, polygon in enumerate(building['geometry']['coordinates']):
			found = True
			new_polygon = polygon[1:]
			while found and len(new_polygon) > 2:  # Iterate until no adjustment

				found = False
				for j in range(1, len(new_polygon) - 1):
					if abs(bearing_turn(new_polygon[ j - 1 ], new_polygon[ j ], new_polygon[ j + 1 ])) > spike_margin:
						removed_nodes.add(new_polygon[ j ])
						new_polygon = new_polygon[ : j ] + new_polygon[ j + 1 : ]
						found = True
						break

				if not found:
					# Special case: Spike wrapped around start/end of polygon
					if abs(bearing_turn(new_polygon[-1], new_polygon[0], new_polygon[1])) > spike_margin:
						removed_nodes.add(new_polygon[0])
						new_polygon = new_polygon[1:]
						found = True
					elif abs(bearing_turn(new_polygon[-2], new_polygon[-1], new_polygon[0])) > spike_margin:
						removed_nodes.add(new_polygon[-1])
						new_polygon = new_polygon[:-1]
						found = True

			if new_polygon:
				new_polygon = [ new_polygon[-1] ] + new_polygon

			if new_polygon != polygon:
				building['geometry']['coordinates'][ i ] = new_polygon
				building['properties']['VERIFY_SPIKE'] = "1"
				count_spikes += 1

	# 4. Check for short self-inersecting corners ("spike" corners)

	count_corners = 0
	for building in buildings:
		for i, polygon in enumerate(building['geometry']['coordinates']):
			found = True
			new_polygon = polygon[1:]
			while found and len(new_polygon) > 3:  # Iterate until no adjustment

				found = False
				for j in range(2, len(new_polygon) - 1):
					if new_polygon[ j - 2 ] == new_polygon[ j + 1 ] and distance(new_polygon[ j - 1 ], new_polygon[ j ]) < short_margin*2:
						removed_nodes.update([ new_polygon[ j - 1 ], new_polygon[ j ] ])
						new_polygon = new_polygon[ : j - 2 ] + new_polygon[ j + 1 : ]
						found = True
						break

				if not found:
					# Special case: Spike wrapped around start/end of polygon
					if new_polygon[-1] == new_polygon[2] and distance(new_polygon[0], new_polygon[1]) < 2 * short_margin:
						removed_nodes.update([ new_polygon[0], new_polygon[1] ])
						new_polygon = new_polygon[2:-1]
						found = True
					elif new_polygon[-2] == new_polygon[1] and distance(new_polygon[-1], new_polygon[0]) < 2 * short_margin:
						removed_nodes.update([ new_polygon[-1], new_polygon[0] ])
						new_polygon = new_polygon[1:-2]
						found = True
					elif new_polygon[-3] == new_polygon[0] and distance(new_polygon[-2], new_polygon[-1]) < 2 * short_margin:
						removed_nodes.update([ new_polygon[-2], new_polygon[-1] ])
						new_polygon = new_polygon[:-3]
						found = True

			if new_polygon:
				new_polygon = [ new_polygon[-1] ] + new_polygon

			if new_polygon != polygon:
				building['geometry']['coordinates'][ i ] = new_polygon
				building['properties']['VERIFY_SPIKE'] = "2"
				count_corners += 1

	# 5. Remove very short segments

	count_short = 0
	if check_short_segments:

		# Produce inventory of nodes
		nodes = {}
		for building in buildings:
			for polygon in building['geometry']['coordinates']:
				for node in polygon[:-1]:  # No double counting for first/last node
					if node not in nodes:
						nodes[ node ] = 0
					nodes[ node ] += 1

		# Identify and remove very short segments
		for building in buildings:
			if "curved" in building:
				continue

			for i, polygon in enumerate(building['geometry']['coordinates']):
				found = True
				new_polygon = polygon[1:]
				while found and len(new_polygon) > 2:   # Iterate until no adjustment

					found = False
					for j in range(len(new_polygon) - 1):
						if distance(new_polygon[ j ], new_polygon[ j + 1 ]) < simplify_line_margin:
							if nodes[ new_polygon[ j ] ] <= 1:
								removed_nodes.add(new_polygon[ j ])
								found = True
								new_polygon.pop(j)
							elif nodes[ new_polygon[ j + 1 ] ] <= 1:
								removed_nodes.add(new_polygon[ j + 1 ])
								new_polygon.pop(j + 1)
								found = True
							break

					if not found:
						# Special case: Segment wrapped around start/end of polygon
						if distance(new_polygon[-1], new_polygon[0]) < simplify_line_margin:
							if nodes[ new_polygon[-1] ] <= 1:
								removed_nodes.add(new_polygon[-1])
								new_polygon.pop(-1)
								found = True
							elif nodes[ new_polygon[0] ] <= 1:
								removed_nodes.add(new_polygon[0])
								new_polygon.pop(0)
								found = True
							break

				if new_polygon and new_polygon[0] != new_polygon[-1]:
					new_polygon = [ new_polygon[-1] ] + new_polygon

				if new_polygon != polygon:
					building['geometry']['coordinates'][ i ] = new_polygon
					building['properties']['VERIFY_SHORT_SEGMENT'] = "yes"
					count_short += 1
	
	# 6. Check if polygons are not conform

	count_remove = 0
	for building in buildings[:]:
		for polygon in building['geometry']['coordinates'][:]:
			if len(polygon) < 4:
				building['geometry']['coordinates'].remove(polygon)
		if not building['geometry']['coordinates']:
			buildings.remove(building)
			count_remove += 1
		else:
			for polygon in building['geometry']['coordinates']:
				if polygon[0] != polygon[-1]:
					print (str(building))

	if debug or verify:
		message ("\tRemoved %i duplicate nodes, %i duplicate segments, %i short segments, %i 'spike' nodes, %i self-intersecting corners and %i buildings\n"
					% (count_nodes, count_segments, count_short, count_spikes, count_corners, count_remove))



# Connect building edges which are partly connected or very close

def connect_buildings():

	# Internal function which identifies connection points and produces connection

	def connect_buildings_in_box(min_bbox, max_bbox):

		nonlocal count_down

		# Internal function which updates node after connection, including for all buildings which share that node

		def update_node(old_node, new_node):

			nodes[ old_node ] -= 1
			if new_node not in nodes:
				nodes[ new_node ] = 0
			nodes[ new_node ] += 1

			if nodes[ old_node ] > 0:
				for building in box_buildings:
					for polygon in building['geometry']['coordinates']:
						if old_node in polygon:
							for i, node in enumerate(polygon):
								if node == old_node:
									polygon[ i ] = new_node
									nodes[ old_node ] -= 1
									nodes[ new_node ] += 1

		# Start of connect_buildings_in_box
		# First identify all buildings overlapping with bbox

		min_bbox = coordinate_offset(min_bbox, -1)  # Capture adjacent buildings
		max_bbox = coordinate_offset(max_bbox, +1)

		count = 0
		box_buildings = []
		for building in buildings:
			if (building['geometry']['type'] == "Polygon"
					and bbox_overlap(min_bbox, max_bbox, building['min_bbox'], building['max_bbox'])):
				box_buildings.append(building)

		# Iterate over potential building pairs which may need connection.
		# Only outer ways.

		for i1, building1 in enumerate(box_buildings):
			count_down -= 1
			if count_down > 0:
				message ("\r\t%i " % count_down)

			for polygon1 in building1['geometry']['coordinates']:
				for i2, building2 in enumerate(box_buildings):
					if i1 == i2:
						continue

					for polygon2 in building2['geometry']['coordinates']:
						if not bbox_overlap(building1['min_bbox'], building1['max_bbox'], building2['min_bbox'], building2['max_bbox']):
							continue

						# Iterate over nodes of both buildings to identify potential connection points

						for n1 in range(len(polygon1) - 1):
							node1 = polygon1[ n1 ]
							if node1 not in polygon2:

								# Find closest edge

								best_dist = snap_margin
								for n2 in range(len(polygon2) - 1):
									new_node, dist = line_distance(polygon2[ n2 ], polygon2[ n2 + 1 ], node1, get_point=True)
									if dist < best_dist:
										best_n2 = n2
										best_dist = dist
										best_node = new_node

								# Connect point to edge of the other building

								if best_dist < snap_margin:
									count += 1
									n2 = best_n2
									new_node = ( round(best_node[0], precision), round(best_node[1], precision) )

									if distance(node1, polygon2[ n2 ]) < snap_margin:  # Snap to close edge node 1
										polygon1[ n1 ] = polygon2[ n2 ]
										update_node(node1, polygon2[ n2 ])

									elif distance(node1, polygon2[ n2 + 1 ]) < snap_margin:  # Snap to close edge node 2
										polygon1[ n1 ] = polygon2[ n2 + 1 ]
										update_node(node1, polygon2[ n2 + 1 ])

									else:
										polygon1[ n1 ] = new_node  # Could be existing node or new node
										update_node(node1, new_node)
										if new_node not in polygon2:
											polygon2.insert(n2 + 1, new_node)
											nodes[ new_node ] += 1

		return count


	# Inner recursive function which gradually splits bbox until number of buildings inside is sufficiently small

	def connect_box(min_bbox, max_bbox, level):

		# Determine number of buildings inside box

		inside_box = 0
		for building in buildings:
			if bbox_overlap(min_bbox, max_bbox, building['min_bbox'], building['max_bbox']):
				inside_box += 1

		# Stop recurse if count is sufficiently small

		if inside_box <= 1000:
			return connect_buildings_in_box(min_bbox, max_bbox)

		# Recurse to get fewer buildings per box. Split along longest axis (x or y) and recurse

		else:
			if distance((min_bbox[0], max_bbox[1]), max_bbox) > distance(min_bbox, (min_bbox[0], max_bbox[1])):  # x longer than y
				# Split x axis
				half_x = 0.5 * (max_bbox[0] + min_bbox[0])
				return connect_box(min_bbox, (half_x, max_bbox[1]), level + 1) + connect_box((half_x, min_bbox[1]), max_bbox, level + 1)
			else:
				# Split y axis
				half_y = 0.5 * (max_bbox[1] + min_bbox[1])
				return connect_box(min_bbox, (max_bbox[0], half_y), level + 1) + connect_box((min_bbox[0], half_y), max_bbox, level + 1)


	# Start of main function

	message ("Connect close polygons ...\n")
#	message ("\tMinimum distance: %.2f m\n" % snap_margin)

	# Make dict of all nodes with count of usage + get building centre

	count_down = 0
	nodes = {}
	for building in buildings:
		if building['geometry']['type'] == "Polygon":
			count_down += 1
			building['min_bbox'], building['max_bbox'] = get_bbox(building['geometry']['coordinates'][0])
			for polygon in building['geometry']['coordinates']:
				for node in polygon:
					if node not in nodes:
						nodes[ node ] = 1
					else:
						nodes[ node ] += 1
		else:
			message (str(building))

	min_bbox = (min([ building['min_bbox'][0] for building in buildings ]),
				min([ building['min_bbox'][1] for building in buildings ]))
	max_bbox = (max([ building['max_bbox'][0] for building in buildings ]),
				max([ building['max_bbox'][1] for building in buildings ]))

	# Start recursive partitioning of buildings into smaller boxes

	count = connect_box (min_bbox, max_bbox, 0)

	# Check if sheds are stand-alone

	for building in buildings:
		if (building['geometry']['type'] == "Polygon"
				and "building" in building['properties']
				and building['properties']['building'] == "shed"
				and (any(nodes[ node ] > 1 for polygon in building['geometry']['coordinates'] for node in polygon[1:-1])
					or any(nodes[ polygon[0] ] > 2 for polygon in building['geometry']['coordinates']))):
			building['properties']['building'] = "yes"

	message ("\r\tConnected %i building edges\n" % count)

	verify_building_geometry()



# Upddate corner dict

def update_corner(corners, wall, node, used):

	if node not in corners:
		corners[node] = {
			'used': 0,
			'walls': []
		}

	if wall:
		wall['nodes'].append(node)
		corners[node]['used'] += used
		corners[node]['walls'].append(wall)



# Make square corners if possible.
# Based on method used by JOSM:
#   https://josm.openstreetmap.de/browser/trunk/src/org/openstreetmap/josm/actions/OrthogonalizeAction.java
# The only input data required is the building dict, where each member is a standard geojson feature member.
# Supports single polygons, multipolygons (outer/inner) and group of connected buildings.

def rectify_buildings():

	message ("Rectify building polygons ...\n")
#	message ("\tThreshold for square corners: 90 +/- %i degrees\n" % angle_margin)
#	message ("\tMinimum length of wall: %.2f meters\n" % short_margin)

	# Create dict of building list to get view

	buildings_index = {}
	for i, building in enumerate(buildings):
		buildings_index[ i ] = building

	# First identify nodes used by more than one way (usage > 1)

	count = 0
	nodes = {}
	for ref, building in iter(buildings_index.items()):
		if building['geometry']['type'] == "Polygon":
			for polygon in building['geometry']['coordinates']:
				for node in polygon[:-1]:
					if node not in nodes:
						nodes[ node ] = {
							'use': 1,
							'parents': [ ref ]
						}
					else:
						nodes[ node ]['use'] += 1
						if ref not in nodes[ node ]['parents']:
							nodes[ node ]['parents'].append( ref)
						count += 1
			building['neighbours'] = [ ref ]

	# Add list of neighbours to each building (other buildings which share one or more node)

	for node in nodes.values():
		if node['use'] > 1:
			for parent in node['parents']:
				for neighbour in node['parents']:
					if neighbour not in buildings_index[ parent ]['neighbours']:
						buildings_index[ parent ]['neighbours'].append(neighbour)  # Including self

#	message ("\t%i nodes used by more than one building\n" % count)

	# Then loop buildings and rectify where possible.

	count_rectify = 0
	count_not_rectify = 0
	count_remove = 0
	count = len(buildings)

	for ref, building_test in iter(buildings_index.items()):

		count -= 1
		message ("\r\t%i " % count)

		if (building_test['geometry']['type'] != "Polygon"
				or "rectified" in building_test
				or "curved" in building_test
				or "circle" in building_test):
			continue

		# 1. First identify buildings which are connected and must be rectified as a group

		building_group = []
		check_neighbours = building_test['neighbours']  # includes self
		while check_neighbours:
			for neighbour in buildings_index[ check_neighbours[0] ]['neighbours']:
				if neighbour not in building_group and neighbour not in check_neighbours:
					check_neighbours.append(neighbour)
			building_group.append(check_neighbours[0])
			check_neighbours.pop(0)

		if len(building_group) > 1:
			building_test['properties']['VERIFY_GROUP'] = str(len(building_group)) 

		# Transform index to building object
		building_group = [ buildings_index[ i ] for i in building_group ]

		# 2. Then build data structure for rectification process.
		# "walls" will contain all (almost) straight segments of the polygons in the group.
		# "corners" will contain all the intersection points between walls.

		corners = {}
		walls = []
		conform = True  # Will be set to False if rectification is not possible

		for building in building_group:

			building['ways'] = []
			angles = []

			# Loop each patch (outer/inner polygon) of building separately
			for patch, polygon in enumerate(building['geometry']['coordinates']):

				if len(polygon) < 5 or polygon[0] != polygon[-1]:
					conform = False
					building['properties']['DEBUG_NORECTIFY'] = "No, only %i walls" % len(polygon)
					break

				# Build list of polygon with only square corners

				patch_walls = []
				wall = { 'nodes': [] }
				count_corners = 0
				last_corner = polygon[-2]  # Wrap polygon for first test

				for i in range(len(polygon) - 1):

					last_count = count_corners

					test_corner = bearing_turn(last_corner, polygon[i], polygon[i+1])
					angles.append("%i" % test_corner)
					short_length = min(distance(last_corner, polygon[i]), distance(polygon[i], polygon[i+1])) # Test short walls

					# Remove short wall if on (almost) straight line
					if (distance(polygon[i], polygon[i+1]) < short_margin
							and abs(test_corner + bearing_turn(polygon[i], polygon[i+1], polygon[(i+2) % (len(polygon)-1)])) < 0.5 * angle_margin
							and nodes[ polygon[i] ]['use'] == 1):

						update_corner(corners, None, polygon[i], 0)
						building['properties']['VERIFY_SHORT_REMOVE'] = "%.2f" % distance(polygon[i], polygon[i+1])

					# Identify (almost) 90 degree corner and start new wall
					elif (90 - angle_margin < abs(test_corner) < 90 + angle_margin
							or short_length < corner_margin and 60 < abs(test_corner) < 120 and nodes[ polygon[i] ]['use'] == 1):
#							 45 - angle_margin < abs(test_corner) < 45 + angle_margin or

						update_corner(corners, wall, polygon[i], 1)
						patch_walls.append(wall)  # End of previous wall, store it

						if short_length < 1 and not (90 - angle_margin < abs(test_corner) < 90 + angle_margin):
							building['properties']['VERIFY_SHORT_CORNER'] = "%.1f" % abs(test_corner)

						wall = { 'nodes': [] }  # Start new wall
						update_corner(corners, wall, polygon[i], 1)
						last_corner = polygon[i]
						count_corners += 1

					# Not possible to rectify if wall is other than (almost) straight line
					elif abs(test_corner) > 0.5 * angle_margin:
						conform = False
						building['properties']['DEBUG_NORECTIFY'] = "No, %i degree angle" % test_corner
						last_corner = polygon[i]

					# Keep node if used by another building or patch
					elif nodes[ polygon[i] ]['use'] > 1: 
						update_corner(corners, wall, polygon[i], 0)
						last_corner = polygon[i]

					# Else throw away node (redundant node on (almost) straight line)
					else:
						update_corner(corners, None, polygon[i], 0)  # Node on "straight" line, will not be used

					# For debugging, mark cases where a slightly larger margin would have produced a rectified polygon
					if count_corners != last_count and not conform and 90 - angle_margin + 2 < abs(test_corner) < 90 + angle_margin + 2:
						building['properties']['DEBUG_MISSED_CORNER'] = str(int(abs(test_corner)))

				building['properties']['DEBUG_ANGLES'] = " ".join(angles)

				if count_corners % 2 == 1:  # Must be even number of corners
					conform = False
					building['properties']['DEBUG_NORECTIFY'] = "No, odd number %i" % count_corners

				elif conform:

					# Wrap from end to start
					patch_walls[0]['nodes'] = wall['nodes'] + patch_walls[0]['nodes']
					for node in wall['nodes']:
						wall_index = len(corners[node]['walls']) - corners[node]['walls'][::-1].index(wall) - 1  # Find last occurrence
						corners[node]['walls'].pop(wall_index)  # remove(wall)
						if patch_walls[0] not in corners[node]['walls']:
							corners[node]['walls'].append(patch_walls[0])

					walls.append(patch_walls)

			if not conform and "DEBUG_NORECTIFY" not in building['properties']:
				building['properties']['DEBUG_NORECTIFY'] = "No"

		if not conform:
			for building in building_group:
				count_not_rectify += 1
				building['rectified'] = "no"  # Do not test again
			continue

		# 3. Remove unused nodes

		for node in list(corners.keys()):
			if corners[node]['used'] == 0:
				for patch in walls:
					for wall in patch:
						if node in wall['nodes']:
							wall['nodes'].remove(node)
				removed_nodes.add(node)
				del corners[node]
				count_remove += 1

		# 4. Get average bearing of all ways

		bearings = []
		group_bearing = 90.0  # For first patch in group, corresponding to axis 1
		group_axis = 1

		for patch in walls:
			start_axis = None

			for i, wall in enumerate(patch):

				wall_bearing = bearing(wall['nodes'][0], wall['nodes'][-1])

				# Get axis for first wall, synced with group
				if start_axis is None:
					diff = (wall_bearing - group_bearing + 180) % 180
					if diff > 90:
						diff = diff - 180

					if abs(diff) < 45 and group_axis == 0:
						start_axis = group_axis  # Axis 1 (y axis)
					else:
						start_axis = 1 - group_axis  # Axis 0 (x axis)

					if not bearings:
						group_axis = start_axis

				wall['axis'] = (i + start_axis) % 2

				if wall['axis'] == 0:					
					wall_bearing = wall_bearing % 180  # X axis
				else:
					wall_bearing = (wall_bearing + 90) % 180  # Turn Y axis 90 degrees 

				wall['bearing'] = wall_bearing
				bearings.append(wall_bearing)

			group_bearing = statistics.median_low(bearings)

		# Compute centre for rotation, average of all corner nodes in cluster of buildings
		axis = polygon_centre(list(corners.keys()))

		# Compute median bearing, by which buildings will be rotated

		if max(bearings) - min(bearings) > 90:
			for i, wall in enumerate(bearings):
				if 0 <= wall < 90:
					bearings[i] = wall + 180  # Fix wrap-around problem at 180

		avg_bearing = statistics.median_low(bearings)  # Use median to get dominant bearings

		building['properties']['DEBUG_BEARINGS'] = str([int(degree) for degree in bearings])
		building['properties']['DEBUG_AXIS'] = str([wall['axis'] for patch in walls for wall in patch ])
		building['properties']['DEBUG_BEARING'] = "%.1f" % avg_bearing

		# 5. Combine connected walls with same axis
		# After this section, the wall list in corners is no longer accurate

		walls = [wall for patch in walls for wall in patch]  # Flatten walls

		combine_walls = []  # List will contain all combinations of walls in group which can be combined

		for wall in walls:
			if any(wall in w for w in combine_walls):  # Avoid walls which are already combined
				continue

			# Identify connected walls with same axis
			connected_walls = []
			check_neighbours = [ wall ]  # includes self
			while check_neighbours:
				if check_neighbours[0]['axis'] == wall['axis']:
					for node in check_neighbours[0]['nodes']:
						for check_wall in corners[ node ]['walls']:
							if check_wall['axis'] == wall['axis'] and check_wall not in check_neighbours and check_wall not in connected_walls:
								check_neighbours.append(check_wall)
					connected_walls.append(check_neighbours[0])
					check_neighbours.pop(0)

			if len(connected_walls) > 1:
				combine_walls.append(connected_walls)

		if combine_walls:
			building_test['properties']['DEBUG_COMBINE'] = str([len(l) for l in combine_walls])

		# Combine nodes of connected walls into one remaining wall
		for combination in combine_walls:
			main_wall = combination[0]
			for wall in combination[1:]:
				main_wall['nodes'].extend(list(set(wall['nodes']) - set(main_wall['nodes'])))

		# 6. Rotate by average bearing

		for node, corner in iter(corners.items()):
			corner['new_node'] = rotate_node(axis, avg_bearing, node)

		# 7. Rectify nodes

		for wall in walls:

#			# Skip 45 degree walls
#			if 45 - 2 * angle_margin < (wall['bearing'] - avg_bearing) % 90 <  45 + 2 * angle_margin:  # 45 degree wall
#				building_test['properties']['TEST_45'] = "%.1f" % (wall['bearing'] - avg_bearing)
#				continue

			# Calculate x and y means of all nodes in wall
			x = statistics.mean([ corners[node]['new_node'][0] for node in wall['nodes'] ])
			y = statistics.mean([ corners[node]['new_node'][1] for node in wall['nodes'] ])

			# Align y and x coordinate for y and x axis, respectively
			for node in wall['nodes']:  
				if wall['axis'] == 1:
					corners[ node ]['new_node'] = ( corners[ node ]['new_node'][0], y)
				else:
					corners[ node ]['new_node'] = ( x, corners[ node ]['new_node'][1])

		# 8. Rotate back

		for node, corner in iter(corners.items()):
			corner['new_node'] = rotate_node(axis, - avg_bearing, corner['new_node'])
			corner['new_node'] = ( round(corner['new_node'][0], precision), round(corner['new_node'][1], precision) )

		# 9. Construct new polygons

		# Check if relocated nodes are off
		relocated = 0
		for building in building_group:
			for i, polygon in enumerate(building['geometry']['coordinates']):
				for node in polygon:
					if node in corners:
						relocated = max(relocated, distance(node, corners[node]['new_node']))

		if relocated  < rectify_margin:

			# Construct new polygons

			for building in building_group:
				relocated = 0
				for i, polygon in enumerate(building['geometry']['coordinates']):
					new_polygon = []
					for node in polygon:
						if node in corners:
							new_polygon.append(corners[node]['new_node'])
							relocated = max(relocated, distance(node, corners[node]['new_node']))
 
					if new_polygon[0] != new_polygon[-1]:  # First + last node were removed
						new_polygon.append(new_polygon[0])

					building['geometry']['coordinates'][i] = new_polygon

				building['rectified'] = "done"  # Do not test again
				building['properties']['DEBUG_RECTIFY'] = "%.2f" % relocated
				count_rectify += 1

				if relocated  > 0.5 * rectify_margin:
					building['properties']['VERIFY_RECTIFY'] = "%.1f" % relocated

		else:
			building_test['properties']['DEBUG_NORECTIFY'] = "Node relocated %.1f m" % relocated
			for building in building_group:
				building['rectified'] = "no"  # Do not test again

	message ("\r\tRemoved %i redundant nodes in buildings\n" % count_remove)
	message ("\t%i buildings rectified\n" % count_rectify)
	message ("\t%i buildings could not be rectified\n" % count_not_rectify)

	verify_building_geometry()



# Identify full circles and replace polygon with evenly and apropriatly spaced nodes.
# Do not touch partial circles.

def simplify_circle(building, nodes):

	if "circle" in building:
		return True

	if (len(building['geometry']['coordinates']) > 1
			or len(building['geometry']['coordinates'][0]) < 6
			or any(nodes[ node ] > 1 for node in building['geometry']['coordinates'][0][1:-1])
			or nodes[ building['geometry']['coordinates'][0][0] ] > 2):
		return False

	# Get mid point and radius

	centre = polygon_centre(building['geometry']['coordinates'][0])
	nodes_radius = [ distance(centre, node) for node in building['geometry']['coordinates'][0] ]
	radius = sum(nodes_radius) / len(nodes_radius)

	if max(nodes_radius) - min(nodes_radius) > 0.3:  # Check real circle
		return False

	# Decide number of nodes in circle

	n = min(round(radius * math.pi), 90)
	if n < 36:
		n = round(6 + n * 30 / 36) 

	new_polygon = generate_circle(centre, radius, n)

	hausdorff = hausdorff_distance(new_polygon, building['geometry']['coordinates'][0])  # Check real circle
	if hausdorff > 0.2:
		return False

	# Consider tagging, knowing that building is circular

	building['geometry']['coordinates'][0] = new_polygon
	building['properties']['VERIFY_CIRCLE'] = "%.2f" % hausdorff
	building['circle'] = True
	if "building" in building['properties']:
		if building['properties']['building'] == "shed":
			building['properties']['building'] = "yes"
		elif building['properties']['building'] == "civic":
			building['properties']['building'] = "service"

	return True



# Simplify building polygons.
# Remove redundant nodes, i.e. nodes on (almost) staight lines.

def simplify_buildings(extra_pass=False):

	message ("Simplify polygons ...\n")
#	message ("\tSimplification factor: %.2f m (curve), %.2f m (line)\n" % (simplify_curve_margin, simplify_line_margin))

	# Make dict of all nodes with count of usage

	count = 0
	nodes = {}
	for building in buildings:
		if building['geometry']['type'] == "Polygon":
			for polygon in building['geometry']['coordinates']:
				for node in polygon:
					if node not in nodes:
						nodes[ node ] = 1
					else:
						nodes[ node ] += 1
						count += 1

#	message ("\t%i nodes used by more than one building\n" % count)

	# Identify redundant nodes, i.e. nodes on an (almost) straight line

	count = 0
	count_circle = 0

	for building in buildings:
		if (building['geometry']['type'] != "Polygon" or "circle" in building):
			continue

		for polygon in building['geometry']['coordinates']:

			# First discover curved walls, to keep more detail

			curves = set()
			curve = set()
			last_bearing = 0

			for i in range(1, len(polygon) - 1):
				new_bearing = bearing_turn(polygon[i-1], polygon[i], polygon[i+1])

				if math.copysign(1, last_bearing) == math.copysign(1, new_bearing) and curve_margin_min < abs(new_bearing) < curve_margin_max:
					curve.add(i - 1)
					curve.add(i)
					curve.add(i + 1)
				else:
					if len(curve) > curve_margin_nodes + 1:
						curves = curves.union(curve)
					curve = set()
				last_bearing = new_bearing

			if len(curve) > curve_margin_nodes + 1:
				curves = curves.union(curve)

			if curves:
				building['curved'] = True
				building['properties']['VERIFY_CURVE'] = str(len(curves))
				count += 1

			# Simplify polygon

			if curves:
				# Light simplification for curved buildings

				if len(curves) > len(polygon) * 0.5 and simplify_circle(building, nodes):  # Swap coordinates with perfect circle
					count_circle += 1
					continue

				new_polygon = simplify_polygon(polygon, simplify_curve_margin)

				# Check if start node could be simplified
				if line_distance(new_polygon[-2], new_polygon[1], new_polygon[0]) < simplify_curve_margin:
					new_polygon = new_polygon[1:-1] + [ new_polygon[1] ]

				if len(new_polygon) < len(polygon):
					building['properties']['VERIFY_SIMPLIFY_CURVE'] = str(len(polygon) - len(new_polygon))
					for node in polygon:
						if node not in new_polygon:
							nodes[ node ] -= 1

			# Simplification for buildings without curves

			else:
				new_polygon = simplify_polygon(polygon, simplify_line_margin)
				if line_distance(new_polygon[-2], new_polygon[1], new_polygon[0]) <  2 * simplify_line_margin:
					new_polygon = new_polygon[1:-1] + [ new_polygon[1] ]

				if len(new_polygon) < len(polygon):
					modify = False
					for node in polygon:
						if node not in new_polygon:
							nodes[ node ] -= 1
							if nodes[ node ] == 0:
								modify = True
					if modify:
						building['properties']['VERIFY_SIMPLIFY_LINE'] = str(len(polygon) - len(new_polygon))
					
	if debug or verify:
		message ("\tIdentified %i buildings with curved walls, %i circles\n" % (count, count_circle))

	# Create set of nodes which may be deleted without conflicts

	remove_nodes = set()
	for node in nodes:
		if nodes[ node ] == 0:
			remove_nodes.add(node)

	# Remove nodes from polygons

	count_building = 0
	count_remove = 0
	for building in buildings:
		if building['geometry']['type'] == "Polygon":
			for i, polygon in enumerate(building['geometry']['coordinates']):
				new_polygon = []
				for node in polygon:
					if node not in remove_nodes:
						new_polygon.append(node)
					else:
						count_remove += 1

				if new_polygon and new_polygon[0] != new_polygon[-1]:
					new_polygon.append(new_polygon[0])
				if new_polygon != polygon:
					building['geometry']['coordinates'][i] = new_polygon
					count_building += 1

	removed_nodes.update(remove_nodes)

	message ("\tRemoved %i redundant nodes in %i buildings\n" % (count_remove, count_building))

	# Establish set of building parents for each node, for checking duplicate buildings below

	nodes = {}
	remove_buildings = []

	for i, building in enumerate(buildings):
		for polygon in building['geometry']['coordinates']:
			for node in polygon:
				if node not in nodes:
					nodes[ node ] = set()
				nodes[ node ].add(i)

	# Remove duplicate buildings

	for i, building1 in enumerate(buildings):
		if building1 not in remove_buildings and building1['geometry']['coordinates'][0]:
			nodes1 = set(node for polygon in building1['geometry']['coordinates'] for node in polygon)

			# Identify buildings which share all nodes in building1
			overlapping_buildings = set.intersection(*[nodes[ node ] for node in nodes1])  # Building indexes

			if len(overlapping_buildings) > 1:
				for j in overlapping_buildings:
					if j != i and buildings[ j ] not in remove_buildings:
						building2 = buildings[ j ]
						nodes2 = set(node for polygon in building2['geometry']['coordinates'] for node in polygon)

						# Mark oldest building as duplicate if identical nodes
						if nodes1 == nodes2:
							if ("DATE" in building1['properties']
										and "DATE" in building2['properties']
										and building1['properties']['DATE'] > building2['properties']['DATE']
									or building1 in remove_buildings):
								if building2 not in remove_buildings:
									remove_buildings.append(building2)
							else:
								remove_buildings.append(building1)
								nodes1 = nodes2

	for building in remove_buildings:
		buildings.remove(building)  # Remove duplicate buildings

	if len(remove_buildings) > 0:
		message ("\tRemoved %i duplicate buildings\n" % len(remove_buildings))

	verify_building_geometry(check_short_segments=True)



# Output resulting geojson file with OSM tagging

def save_buildings(filename):

	if debug:
		filename = filename.replace(".geojson", "_debug.geojson")
	elif verify:
		filename = filename.replace(".geojson", "_verify.geojson")
	elif original:
		filename = filename.replace(".geojson", "_original.geojson")

	message ("Saving buildings ...\n")
	message ("\tFilename: '%s'\n" % filename)

	features = {
		"type": "FeatureCollection",
		"features": []
	}

	# Prepare buildings to fit geosjon data structure

	count = 0
	for building in buildings:
		if building['geometry']['coordinates'] and len(set(building['geometry']['coordinates'][0])) > 2:
			count += 1

			# Delete temporary data
			for key in list(building.keys()):
				if key not in ['type', 'geometry', 'properties']:
					del building[key]

			# Delete upper case debug tags		
			if not debug or not verify:
				for key in list(building['properties'].keys()):
					if key == key.upper() and (not verify and "VERIFY_" in key or not debug and "DEBUG_" in key): 
#							and key not in ['BTYPE', 'DATE', 'MAIN']
						del building['properties'][key]
			features['features'].append(building)

	# Add removed nodes, for debugging

	if debug or verify:
		for node in removed_nodes:
			feature = {
				'type': 'Feature',
				'geometry': {
					'type': 'Point',
					'coordinates': node
				},
				'properties': {
					'REMOVE': 'yes'
				}
			}
			features['features'].append(feature)

	file_out = open(filename, "w")
	json.dump(features, file_out, ensure_ascii=False)  # indent=1
	file_out.close()

	message ("\tSaved %i buildings\n" % count)



# Main function for processing one municipality

def process_municipality(municipality_id, input_filename=""):

	mun_start_time = time.time()
	message ("Municipality: %s %s\n\n" % (municipality_id, municipalities[ municipality_id ]))

	buildings.clear()  # Enable repeated calls
	removed_nodes.clear()

	load_buildings(municipality_id, input_filename)

	if len(buildings) > 0:
		if not original:
			connect_buildings()
			simplify_buildings()
			rectify_buildings()
			simplify_buildings(extra_pass=True)

		filename = "byggnader_%s_%s.geojson" % (municipality_id, municipalities[ municipality_id ].replace(" ", "_"))
		save_buildings(filename)

		message("Done in %s\n\n\n" % timeformat(time.time() - mun_start_time))

	else:
		failed_runs.append("#%s %s" % (municipality_id, municipalities[ municipality_id ]))



# Main program

if __name__ == '__main__':

	start_time = time.time()
	message ("\n*** building2osm v%s ***\n\n" % version)

	municipalities = {}		# All municipalities + 00 Sverige
	building_types = {}		# Default tagging per building type
	heritage_buildings = {}	# Heritage buildings from Riksantikvarämbetet
	buildings = []			# List of all buildings
	removed_nodes = set()	# For verification/debugging
	failed_runs = []		# Municipalities which did not complete

	# Parse parameters

	if len(sys.argv) < 2:
		message ("Please provide municipality number or name\n")
		message ("Main options: -split, -original\n\n")
		sys.exit()

	if "-debug" in sys.argv:
		debug = True

	if "-verify" in sys.argv:
		verify = True

	if "-original" in sys.argv:
		original = True

	if "-heritage" in sys.argv:
		load_heritage_buildings(save_heritage=True)
		sys.exit("\n")

	# Get selected municipality

	load_municipalities()

	municipality_query = sys.argv[1]
	municipality_id = get_municipality(municipality_query)

	start_municipality = ""
	if len(sys.argv) > 2 and sys.argv[2].isdigit():
		start_municipality = sys.argv[2]

	input_filename = ""
	if len(sys.argv) > 2 and (".geojson" in sys.argv[2] or ".gpkg" in sys.argv[2]):
		input_filename = sys.argv[2]
		if not os.path.isfile(input_filename):
			sys.exit("\t*** File '%s' not found\n\n" % input_filename)

	# Get Geotorget login details

	if not input_filename:
		token = get_token()

	if (not input_filename or ".gpkg" in input_filename) and "-noheritage" not in sys.argv and "-original" not in sys.argv:
		load_heritage_buildings()

	# Process

	load_building_types()

	if municipality_id == "00":  # Sweden
		message ("Generating building files for all municipalities in %s\n\n" % municipalities[ municipality_id ])
		for mun_id in sorted(municipalities.keys()):
			if mun_id >= start_municipality and mun_id != "00":
				process_municipality(mun_id)
		message("%s done in %s\n\n" % (municipalities[ municipality_id ], timeformat(time.time() - start_time)))
		if failed_runs:
			message ("*** Failed runs: %s\n\n" % (", ".join(failed_runs)))
	else:
		process_municipality(municipality_id,  input_filename=input_filename)

		if "-split" in sys.argv:
			message("Start splitting...\n\n")
			subprocess.run(['python', "building_split.py", municipality_id])
