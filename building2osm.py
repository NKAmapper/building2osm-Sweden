#!/usr/bin/env python3
# -*- coding: utf8

# buildings2osm
# Converts buildings from Lantmäteriet to geosjon file for import to OSM.
# Usage: buildings2osm.py <municipality name> [geojson or gpkg input filename] [-original] [-verify] [-debug]
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


version = "0.9.1"

debug = False				# Add debugging / testing information
verify = False				# Add tags for users to verify
original = False			# Output polygons as in original data (no rectification/simplification)

precision = 7				# Number of decimals in coordinate output

snap_margin = 0.2 			# Max margin for connecting building nodes/edges (meters)

angle_margin = 8.0			# Max margin around angle limits, for example around 90 degrees corners (degrees)
short_margin = 0.3			# Min length of short wall which will be removed if on "straight" line (meters)
corner_margin = 1.0			# Max length of short wall which will be rectified even if corner is outside of 90 +/- angle_margin (meters)
rectify_margin = 0.3		# Max relocation distance for nodes during rectification before producing information tag (meters)

simplify_margin = 0.03		# Minimum tolerance for buildings with curves in simplification (meters)

curve_margin_max = 40		# Max angle for a curve (degrees)
curve_margin_min = 0.3		# Min angle for a curve (degrees)
curve_margin_nodes = 3		# At least three nodes in a curve (number of nodes)

spike_margin = 170			# Max angle/bearing for spikes (degrees)

token_filename = "geotorget_token.txt"  # Stored Geotorget credentials


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
	file = urllib.request.urlopen(url)
	data = json.load(file)
	file.close()

	municipalities['00'] = "Sverige"
	for municipality in data['results']:
		ref = municipality['kommunkod']
		if len(ref) < 4:
			ref = "0" + ref
		municipalities[ ref ] = municipality['kommun']



# Identify municipality name, unless more than one hit
# Returns municipality number, or input parameter if not found

def get_municipality (parameter):

	if parameter.isdigit():
		return parameter

	else:
		parameter = parameter
		found_id = ""
		duplicate = False
		for mun_id, mun_name in iter(municipalities.items()):
			if parameter.lower() == mun_name.lower():
				return mun_id
			elif parameter.lower() in mun_name.lower():
				if found_id:
					duplicate = True
				else:
					found_id = mun_id

		if found_id and not duplicate:
			return found_id
		else:
			return parameter



# Get stored Geotorget token or ask for credentials

def get_token():

	if os.path.isfile(token_filename):
		message ("Loading Geotorget credentials from file '%s'\n\n" % token_filename)
		file = open(token_filename)
		token = file.read()
		file.close()
	else:
		message ("Please provide Geotorget login (you need approval for 'Byggnad Nedladdning, vektor') ...\n")
		username = input("\tUser name: ")
		password = input("\tPassword:  ")
		token = username + ":" + password
		token = base64.b64encode(token.encode()).decode()
		file = open(token_filename, "w")
		file.write(token)
		file.close()
		message ("\tStoring credentials in file '%s'\n\n" % token_filename)

	return token



# Load conversion CSV table for tagging building types.

def load_building_types():

	url = "https://raw.githubusercontent.com/NKAmapper/building2osm-Sweden/main/building_tags.json"
	file = urllib.request.urlopen(url)
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



# Get municipality BBOX and kick off recursive splitting into smaller BBOX quadrants

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

		if "byggnadsnamn1" in properties and properties['byggnadsnamn1']:
			tags['name'] = properties['byggnadsnamn1']
		if "byggnadsnamn2" in properties and properties['byggnadsnamn2']:
			tags['alt_name'] = properties['byggnadsnamn2']
			if "byggnadsnamn3" in properties and properties['byggnadsnamn3']:
				tags['alt_name'] += ";" + properties['byggnadsnamn3']

		if "versiongiltigfran" in properties and properties['versiongiltigfran']:
			tags['DATE'] = properties['versiongiltigfran'][:10]
			if "objektversion" in properties and properties['objektversion']:
				tags['DATE'] += " v" + str(properties['objektversion'])

#		if "ursprunglig_organisation" in properties and properties['ursprunglig_organisation']:
#			tags['SOURCE'] = properties['ursprunglig_organisation'][0].upper() + properties['ursprunglig_organisation'][1:]

#		if "huvudbyggnad" in properties and properties['huvudbyggnad'] == "Ja":
#			tags['MAIN'] = "yes"

		building['properties'] = tags

		# Mark if multiple buildings have same ref

		if ref in building_refs:
			if len(building_refs[ ref ]) == 1:
				building_refs[ ref ][0]['properties']['MULTI'] = "yes"
			building['properties']['MULTI'] = "yes"
			building_refs[ ref ].append(building)

		else:
			building_refs[ ref ] = [ building ]

	# Check for duplicate nodes
	verify_building_geometry()

	count_polygons = sum((building['geometry']['type'] == "Polygon") for building in buildings)
	message ("\tLoaded %i building polygons\n" % count_polygons)
	if not_found:
		message ("\t*** Building type(s) not found: %s\n" % (", ".join(sorted([ purpose for purpose in not_found ]))))



# Check for duplicate nodes, "spike" nodes (sharp angles) and segments

def verify_building_geometry():

	# Check for duplicate nodes

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

	# Check for duplicate segments

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
							remove_nodes.add(new_polygon[ j ])
							new_polygon = new_polygon[ : j - 1 ] + new_polygon[ j + 1 : ]
							found = True
							break

					if not found:
						# Special case: Duplicate segment wrapped around start/end of polygon
						if new_polygon[-1] == new_polygon[1]:
							remove_nodes.add(new_polygon[0])
							new_polygon = new_polygon[1:-1]
							found = True
						elif new_polygon[-2] == new_polygon[0]:
							remove_nodes.add(new_polygon[-1])
							new_polygon = new_polygon[:-2]
							found = True

				if new_polygon:
					new_polygon = [ new_polygon[-1] ] + new_polygon

				if new_polygon != polygon:
					building['geometry']['coordinates'][ i ] = new_polygon
					count_segments += 1

	# Check for sharp angles ("spike" nodes)

	count_spikes = 0
	for building in buildings:
		for i, polygon in enumerate(building['geometry']['coordinates']):
			found = True
			new_polygon = polygon[1:]
			while found and len(new_polygon) > 2:  # Iterate until no adjustment

				found = False
				for j in range(1, len(new_polygon) - 1):
					if abs(bearing_turn(new_polygon[ j - 1 ], new_polygon[ j ], new_polygon[ j + 1 ])) > spike_margin:
						remove_nodes.add(new_polygon[ j ])
						new_polygon = new_polygon[ : j ] + new_polygon[ j + 1 : ]
						found = True
						break

				if not found:
					# Special case: Spike wrapped around start/end of polygon
					if abs(bearing_turn(new_polygon[-1], new_polygon[0], new_polygon[1])) > spike_margin:
						remove_nodes.add(new_polygon[0])
						new_polygon = new_polygon[1:]
						found = True
					elif abs(bearing_turn(new_polygon[-2], new_polygon[-1], new_polygon[0])) > spike_margin:
						remove_nodes.add(new_polygon[-1])
						new_polygon = new_polygon[:-1]
						found = True

			if new_polygon:
				new_polygon = [ new_polygon[-1] ] + new_polygon

			if new_polygon != polygon:
				building['geometry']['coordinates'][ i ] = new_polygon
				count_spikes += 1

	# Check if polygons are not conform

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

#	message ("\tRemoved %i duplicate nodes, %i duplicate segments and %i 'spike' corners\n" % (count_nodes, count_segments, count_spikes))
#	if count_remove > 0:
#		message ("\tRemoved %i buildings\n" % count_remove)



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

		# Start of connect_buildings_in_box
		# First identify all buildings overlapping with bbox

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

			polygon1 = building1['geometry']['coordinates'][0]
			for i2, building2 in enumerate(box_buildings):
				if i1 == i2:
					continue

				polygon2 = building2['geometry']['coordinates'][0]

				if bbox_overlap(building1['min_bbox'], building1['max_bbox'], building2['min_bbox'], building2['max_bbox']):

					# Iterate over nodes of both buildings to identify potential connection points

					for n1 in range(len(polygon1) - 1):
						node1 = polygon1[ n1 ]
						if node1 not in polygon2:
							for n2 in range(len(polygon2) - 1):

								# Connect point to edge of the other building

								new_node, dist = line_distance(polygon2[ n2 ], polygon2[ n2 + 1 ], node1, get_point=True)
								if dist < snap_margin:
									count += 1
									new_node = ( round(new_node[0], precision), round(new_node[1], precision) )

									if new_node in nodes:  # Reuse node already existing at that point
										polygon1[ n1 ] = new_node
										if new_node not in polygon2:
											polygon2.insert(n2 + 1, new_node)
										update_node(node1, new_node)

									elif distance(node1, polygon2[ n2 ]) < snap_margin:  # Snap to close edge node 1
										polygon1[ n1 ] = polygon2[ n2 ]
										update_node(node1, polygon2[ n2 ])

									elif distance(node1, polygon2[ n2 + 1 ]) < snap_margin:  # Snap to close edge node 2
										polygon1[ n1 ] = polygon2[ n2 + 1 ]
										update_node(node1, polygon2[ n2 + 1 ])

									else:
										polygon1[ n1 ] = new_node  # Create new node
										polygon2.insert(n2 + 1, new_node)
										update_node(node1, new_node)
									break
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
	message ("\tMinimum distance: %.2f m\n" % snap_margin)

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
	message ("\tThreshold for square corners: 90 +/- %i degrees\n" % angle_margin)
	message ("\tMinimum length of wall: %.2f meters\n" % short_margin)

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

		if building_test['geometry']['type'] != "Polygon" or "rectified" in building_test:
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
					if distance(polygon[i], polygon[i+1]) < short_margin and \
							abs(test_corner + bearing_turn(polygon[i], polygon[i+1], polygon[(i+2) % (len(polygon)-1)])) < angle_margin and \
							nodes[ polygon[i] ]['use'] == 1:

						update_corner(corners, None, polygon[i], 0)
						building['properties']['VERIFY_SHORT_REMOVE'] = "%.2f" % distance(polygon[i], polygon[i+1])

					# Identify (almost) 90 degree corner and start new wall
					elif 90 - angle_margin < abs(test_corner) < 90 + angle_margin or \
							 short_length < corner_margin and 60 < abs(test_corner) < 120 and nodes[ polygon[i] ]['use'] == 1:
#							 45 - angle_margin < abs(test_corner) < 45 + angle_margin or \

						update_corner(corners, wall, polygon[i], 1)
						patch_walls.append(wall)  # End of previous wall, store it

						if short_length < 1 and not (90 - angle_margin < abs(test_corner) < 90 + angle_margin):
							building['properties']['VERIFY_SHORT_CORNER'] = "%.1f" % abs(test_corner)

						wall = { 'nodes': [] }  # Start new wall
						update_corner(corners, wall, polygon[i], 1)
						last_corner = polygon[i]
						count_corners += 1

					# Not possible to rectify if wall is other than (almost) straight line
					elif abs(test_corner) > angle_margin:
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
				remove_nodes.add(node)
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


# Simplify polygon
# Remove redundant nodes, i.e. nodes on (almost) staight lines

def simplify_buildings():

	message ("Simplify polygons ...\n")
	message ("\tSimplification factor: %.2f m (curve), %i degrees (line)\n" % (simplify_margin, angle_margin))

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
	for building in buildings:
		if building['geometry']['type'] == "Polygon" and ("rectified" not in building or building['rectified'] == "no"):

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
					building['properties']['VERIFY_CURVE'] = str(len(curves))
					count += 1

				# Then simplify polygon

				if curves:
					# Light simplification for curved buildings

					new_polygon = simplify_polygon(polygon, simplify_margin)

					# Check if start node could be simplified
					if line_distance(new_polygon[-2], new_polygon[1], new_polygon[0]) < simplify_margin:
						new_polygon = new_polygon[1:-1] + [ new_polygon[1] ]
#						building['properties']['VERIFY_SIMPLIFY_FIRST'] = "yes"

					if len(new_polygon) < len(polygon):
						building['properties']['VERIFY_SIMPLIFY_CURVE'] = str(len(polygon) - len(new_polygon))
						for node in polygon:
							if node not in new_polygon:
								nodes[ node ] -= 1
				else:
					# Simplification for buildings without curves

					last_node = polygon[-2]
					for i in range(len(polygon) - 1):
						angle = bearing_turn(last_node, polygon[i], polygon[i+1])
						length = distance(polygon[i], polygon[i+1])

						if (abs(angle) < angle_margin or \
							length < short_margin and \
								(abs(angle) < 40 or \
								abs(angle + bearing_turn(polygon[i], polygon[i+1], polygon[(i+2) % (len(polygon)-1)])) < angle_margin) or \
							length < corner_margin and abs(angle) < 2 * angle_margin):

							nodes[ polygon[i] ] -= 1
							if angle > angle_margin - 2:
								building['properties']['VERIFY_SIMPLIFY_LINE'] = "%.1f" % abs(angle)
						else:
							last_node = polygon[i]
					
	if debug or verify:
		message ("\tIdentified %i buildings with curved walls\n" % count)

	# Create set of nodes which may be deleted without conflicts

	already_removed = len(remove_nodes)
	for node in nodes:
		if nodes[ node ] == 0:
			remove_nodes.add(node)

	# Remove nodes from polygons

	count_building = 0
	count_remove = 0
	for building in buildings:
		if building['geometry']['type'] == "Polygon":
			removed = False
			for polygon in building['geometry']['coordinates']:
				for node in polygon[:-1]:
					if node in remove_nodes:
						i = polygon.index(node)
						polygon.pop(i)
						count_remove += 1
						removed = True
						if i == 0:
							polygon[-1] = polygon[0]
			if removed:
				count_building += 1

	message ("\tRemoved %i redundant nodes in %i buildings\n" % (count_remove, count_building))



# Output geojson file

def save_buildings(filename):

	verify_building_geometry()

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
		for node in remove_nodes:
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
	json.dump(features, file_out, indent=2, ensure_ascii=False)
	file_out.close()

	message ("\tSaved %i buildings\n" % count)



def process_municipality(municipality_id, input_filename=""):

	mun_start_time = time.time()
	message ("Municipality: %s %s\n\n" % (municipality_id, municipalities[ municipality_id ]))

	buildings.clear()
	remove_nodes.clear()

	load_buildings(municipality_id, input_filename)

	if len(buildings) > 0:
		if not original:
			connect_buildings()
			rectify_buildings()
			simplify_buildings()

		filename = "byggnader_%s_%s.geojson" % (municipality_id, municipalities [ municipality_id ].replace(" ", "_"))
		save_buildings(filename)

		message("Done in %s\n\n\n" % timeformat(time.time() - mun_start_time))

	else:
		failed_runs.append("#%s %s" % (municipality_id, municipalities[ municipality_id ]))



# Main program

if __name__ == '__main__':

	start_time = time.time()
	message ("\n*** building2osm v%s ***\n\n" % version)

	municipalities = {}
	building_types = {}
	buildings = []
	buildings_index = {}
	remove_nodes = set()
	failed_runs = []

	addr = {}

	# Parse parameters

	if len(sys.argv) < 2:
		message ("Please provide municipality number or name\n")
		message ("Options: -original, -verify, -debug\n\n")
		sys.exit()

	if "-debug" in sys.argv:
		debug = True

	if "-verify" in sys.argv:
		verify = True

	if "-original" in sys.argv:
		original = True

	# Get selected municipality

	load_municipalities()

	municipality_query = sys.argv[1]
	municipality_id = get_municipality(municipality_query)
	if municipality_id is None or municipality_id not in municipalities:
		sys.exit("Municipality '%s' not found, or ambiguous\n" % municipality_query)

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

#		if "-split" in sys.argv:
#			message("Start splitting...\n\n")
#			subprocess.run(['python', "building_split.py", municipality_id])

