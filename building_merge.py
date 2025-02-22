#!/usr/bin/env python3
# -*- coding: utf8

# building_merge.py
# Conflates geojson building import file with existing buildings in OSM.
# Usage: building_merge <municipality name> [max Hausdorff distance] [filename.geojson] [-debug].
# geojson file from building2osm must be present in default folder. Other filename is optional parameter.
# Creates OSM file (manual upload to OSM).

import math
import sys
import time
import json
import os.path
import urllib.request, urllib.parse
from xml.etree import ElementTree as ET


version = "0.10.3"

request_header = {"User-Agent": "building2osm"}

overpass_api = "https://overpass-api.de/api/interpreter"  # Overpass endpoint
#overpass_api = "https://overpass.kumi.systems/api/interpreter"

import_folder = "~/Jottacloud/osm/byggnader Sverige/"  # Folder containing import building files (default folder tried first)

margin_hausdorff = 15.0	# Maximum deviation between polygons (meters)
margin_tagged = 7.5		# Maximum deviation between polygons if building is tagged (meters)
margin_area = 0.4       # At least 40% equal building areas

remove_addr = False 	# Remove addr tags from buildings

lm_residential_tags = ["detached", "house", "terrace", "apartments"]  # Will override "residential"

# Group of buildings types within which LM/OSM mismatch should not produce warning
similar_buildings = {
	'residential':	{"residential", "house", "detached", "apartments", "terrace", "allotment_house", "semidetached_house",
					"cabin", "bungalow", "farm", "semi", "hut"},
	'industrial':	{"industrial", "warehouse",  "storage_tank", "manufacture"},
	'commercial':	{"commercial", "retail", "office", "hotel", "supermarket", "kiosk", "roof"},
	'civic':		{"civic", "service", "hospital", "train_station", "parking", "public", "hangar", "dormitory", "toilets", "bunker",
					"government", "transportation", "fire_station", "bridge", "museum", "roof"},
	'school':		{"civic", "school", "kindergarten", "university", "college"},
	'sport':		{"sports_hall", "sports_centre", "riding_hall"},
	'regligious':	{"religious", "church", "chapel", "mosque"},
	'farm':			{"barn", "farm_auxiliary", "greenhouse", "stable", "slurry_tank", "garages", "garage", "carport", "roof", "shed"}
}

debug = False 			# Output extra tags for debugging/testing



# Output message to console

def message (text):

	sys.stderr.write(text)
	sys.stderr.flush()



# Format time

def timeformat (sec):

	if sec >= 3600:
		return "%i:%02i:%02i hours" % (sec / 3600, (sec % 3600) / 60, sec % 60)
	elif sec >= 60:
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

def point_distance (point1, point2):

	lon1, lat1, lon2, lat2 = map(math.radians, [point1[0], point1[1], point2[0], point2[1]])
	x = (lon2 - lon1) * math.cos( 0.5*(lat2+lat1) )
	y = lat2 - lat1
	return 6371000.0 * math.sqrt( x*x + y*y )  # Metres



# Compute closest distance from point p3 to line segment [s1, s2].
# Works for short distances.

def line_distance(s1, s2, p3):

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
	'''
	# Project back to longitude/latitude

	x4 = x4 / math.cos(y4)

	lon = math.degrees(x4)
	lat = math.degrees(y4)

	return (lon, lat, distance)
	'''
	return distance



# Test if line segments s1 and s2 are crossing.
# Segments have two nodes [(start.x, start.y), (end.x, end.y)].
# Source: https://en.wikipedia.org/wiki/Line–line_intersection#Given_two_points_on_each_line_segment

def crossing_lines (s1, s2):

	d1x = s1[1][0] - s1[0][0]  # end1.x - start1.x
	d1y = s1[1][1] - s1[0][1]  # end1.y - start1.y
	d2x = s2[1][0] - s2[0][0]  # end2.x - start2.x
	d2y = s2[1][1] - s2[0][1]  # end2.y - start2.y

	D = d1x * d2y - d1y * d2x

	if abs(D) < 0.0000000001:  # s1 and s2 are parallel
		return False

	A = s1[0][1] - s2[0][1]  # start1.y - start2.y
	B = s1[0][0] - s2[0][0]  # start1.x - start2.x

	r1 = (A * d2x - B * d2y) / D
	r2 = (A * d1x - B * d1y) / D

	if r1 < 0 or r1 > 1 or r2 < 0 or r2 > 1:
		return False
	'''
	# Compute intersection point

	x = s1[0][0] + r1 * d1x
	y = s1[0][1] + r1 * d1y
	intersection = (x, y)
	return (intersection)
	'''
	return True



# Calculate coordinate area of polygon in square meters
# Simple conversion to planar projection, works for small areas
# < 0: Clockwise
# > 0: Counter-clockwise
# = 0: Polygon not closed

def polygon_area (polygon):

	if polygon and polygon[0] == polygon[-1]:
		lat_dist = math.pi * 6371009.0 / 180.0

		coord = []
		for node in polygon:
			y = node[1] * lat_dist
			x = node[0] * lat_dist * math.cos(math.radians(node[1]))
			coord.append((x,y))

		area = 0.0
		for i in range(len(coord) - 1):
			area += (coord[i+1][0] - coord[i][0]) * (coord[i+1][1] + coord[i][1])  # (x2-x1)(y2+y1)

		return area / 2.0
	else:
		return 0



# Calculate center of polygon nodes (simple average method)
# Note: If nodes are skewed to one side, the center will be skewed to the same side

def polygon_center (polygon):

	if len(polygon) == 0:
		return None
	elif len(polygon) == 1:
		return polygon[0]

	length = len(polygon)
	if polygon[0] == polygon[-1]:
		length -= 1

	x = 0
	y = 0
	for node in polygon[:length]:
		x += node[0]
		y += node[1]

	x = x / length
	y = y / length

	return (x, y)



# Calculate centroid of polygon
# Source: https://en.wikipedia.org/wiki/Centroid#Of_a_polygon

def polygon_centroid (polygon):

	if polygon[0] == polygon[-1]:
		x = 0
		y = 0
		det = 0

		for i in range(len(polygon) - 1):
			d = polygon[i][0] * polygon[i+1][1] - polygon[i+1][0] * polygon[i][1]
			det += d
			x += (polygon[i][0] + polygon[i+1][0]) * d  # (x1 + x2) (x1*y2 - x2*y1)
			y += (polygon[i][1] + polygon[i+1][1]) * d  # (y1 + y2) (x1*y2 - x2*y1)

		x = x / (3.0 * det)
		y = y / (3.0 * det)

		return (x, y)

	else:
		return None



# Calculate new node with given distance offset in meters
# Works over short distances

def coordinate_offset (node, distance):

	m = (1 / ((math.pi / 180.0) * 6378137.0))  # Degrees per meter

	latitude = node[1] + (distance * m)
	longitude = node[0] + (distance * m) / math.cos( math.radians(node[1]) )

	return (longitude, latitude)



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



# Tests whether point (x,y) is inside a polygon
# Ray tracing method

def inside_polygon (point, polygon):

	if polygon[0] == polygon[-1]:
		x, y = point
		n = len(polygon)
		inside = False

		p1x, p1y = polygon[0]
		for i in range(n):
			p2x, p2y = polygon[i]
			if y > min(p1y, p2y):
				if y <= max(p1y, p2y):
					if x <= max(p1x, p2x):
						if p1y != p2y:
							xints = (y-p1y) * (p2x-p1x) / (p2y-p1y) + p1x
						if p1x == p2x or x <= xints:
							inside = not inside
			p1x, p1y = p2x, p2y

		return inside

	else:
		return None



# Test if any node of polygon1 is inside polygon2, and vice versa.
# Not used

def polygon_inside_polygon (polygon1, polygon2):

	if polygon1[0] == polygon1[-1] and polygon2[0] == polygon2[-1]:
		for node in polygon1[:-1]:
			if inside_polygon(node, polygon2):
				return True
		for node in polygon2[:-1]:
			if inside_polygon(node, polygon1):
				return True

	return False  # No node found inside the other polygon




# Test if polygon1 and polygon2 are overlapping.
# The polygons are not overlapping if no edges are crossing, and if the polygons are are not contained within each other.
# If a polygon is contained within another polygon, then any one node is contained within the other polygon.

def polygon_overlap (polygon1, polygon2):

#	if polygon1[0] == polygon1[-1] and polygon2[0] == polygon2[-1]:

#		if polygon_inside_polygon(polygon1, polygon2):
#			return True

	for i in range(len(polygon1) - 1):
		for j in range(len(polygon2) - 1):
			if crossing_lines([ polygon1[i], polygon1[i + 1] ], [ polygon2[j], polygon2[j + 1] ]):
				return True

	if inside_polygon(polygon1[0], polygon2) or inside_polygon(polygon2[0], polygon1):
		return True

	return False



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



# Load dict of all municipalities

def load_municipalities():

	url = "https://catalog.skl.se/rowstore/dataset/4c544014-8e8f-4832-ab8e-6e787d383752/json?_limit=400"
	file = urllib.request.urlopen(url)
	data = json.load(file)
	file.close()

	for municipality in data['results']:
		ref = municipality['kommunkod']
		if len(ref) < 4:
			ref = "0" + ref
		municipalities[ ref ] = municipality['kommun']



# Load buildings from geojson file

def load_import_buildings(filename):

	global import_buildings

	message ("Loading import buildings ...\n")
	message ("\tFilename '%s'\n" % filename)

	if not os.path.isfile(filename):
		test_filename = os.path.expanduser(import_folder + filename)
		if os.path.isfile(test_filename):
			filename = test_filename
		else:
			sys.exit("\t*** File not found\n\n")

	file = open(filename)
	data = json.load(file)
	file.close()
	import_buildings = data['features']
	count_no_tag = 0

	# Add polygon center and area

	for building in import_buildings:

		if "properties" not in building or "building" not in building['properties']:
			count_no_tag += 1
#			message("\t*** No building tag: %s\n" % (json.dumps(building, ensure_ascii=False)))
			continue

		if building['geometry']['type'] == "Polygon" and len(building['geometry']['coordinates']) == 1:

			building['center'] = polygon_center( building['geometry']['coordinates'][0] )
			building['area'] = abs(polygon_area( building['geometry']['coordinates'][0] ))
			if debug:
				building['properties']['AREA'] = str(round(building['area']))

		# Remove uppercase import tags
		for tag in list(building['properties']):
			if tag == tag.upper() and tag != "BTYPE":
				del building['properties'][ tag ]

	message ("\t%i buildings loaded\n" % len(import_buildings))
	if count_no_tag > 0:
		message ("\t%i buildings had no building=* tag\n" % count_no_tag)



# Load existing buildings from OSM Overpass

def load_osm_buildings(municipality_id):

	global osm_elements

	message ("Loading existing buildings from OSM ...\n")

	query = '[out:json][timeout:120];(area["ref:scb"=%s][admin_level=7];)->.a;(nwr["building"](area.a););(._;>;<;>;);out center meta;' % (municipality_id)
	request = urllib.request.Request(overpass_api + "?data=" + urllib.parse.quote(query), headers=request_header)
	file = urllib.request.urlopen(request)
	data = json.load(file)
	file.close()
	osm_elements = data['elements']

	if len(osm_elements) == 0:
		sys.exit("\tNo OSM buildings retrieved - please try again\n")

	# Identify members of relations, to exclude from building matching

	relation_members = set()  #  All/any members of relations
	building_relation_members = set()  # All members of relations tagged with building=*
	for element in osm_elements:
		if element['type'] == "relation":
			for member in element['members']:
				relation_members.add(member['ref'])  # OSM id of element
				if "tags" in element and "building" in element['tags']:
					building_relation_members.add(member['ref'])  # OSM id of element

	# Create dict of nodes + list of buildings (ways tagged with building=*)

	for element in osm_elements:
		if element['type'] == "node":
			osm_nodes[ element['id'] ] = element
			element['used'] = 0

		elif element['type'] == "way":
			if ("tags" in element
					and "building" in element['tags']
					and len(element['nodes']) > 2 and element['nodes'][0] == element['nodes'][-1]
					and ("building:part" not in element['tags'] and not element['id'] in relation_members
						or function == "new")):
				osm_buildings.append(element)

			# For the new function, also ways which are members of building relations are kept, even if not a connected polygon

			elif element['id'] in building_relation_members and function == "new":
				osm_buildings.append(element)

			else:
				for node_ref in element['nodes']:
					if node_ref in osm_nodes:
						osm_nodes[ node_ref ]['used'] += 1

	# Add polygon center and area

	tag_count = 0
	for building in osm_buildings:
		if "center" in building:
			building['center'] = (building['center']['lon'], building['center']['lat'])

		if building['type'] == "way":
			line = []
			for node_ref in building['nodes']:
				if node_ref in osm_nodes:
					line.append((osm_nodes[ node_ref ]['lon'], osm_nodes[ node_ref ]['lat']))
					osm_nodes[ node_ref ]['used'] += 1
			building['polygon'] = line
			building['area'] = abs(polygon_area(line))

			if "tags" in building:
				for tag in building['tags']:
					if tag not in ["building", "source", "source:date", "created_by"] and "addr:" not in tag:
						building['tagged'] = True
				if "tagged" in building:
					tag_count += 1

			if debug:
				building['tags']['AREA'] = str(building['area'])

	message ("\t%i buildings loaded (%i elements)\n" % (len(osm_buildings), len(osm_elements)))
	message ("\t%i buildings with tags other than building=*\n" % tag_count)

	# Get top contributors

	users = {}
	for element in osm_elements:
		if "tags" in element and "building" in element['tags']:
			if element['user'] not in users:
				users[ element['user'] ] = 0
			users[ element['user'] ] += 1

	sorted_users = sorted(users.items(), key=lambda x: x[1], reverse=True)

	message ("\tTop contributors:\n")
	for i, user in enumerate(sorted_users):
		if user[1] > 10 and i < 10 or user[1] >= 100:
			message ("\t\t%s (%i)\n" % (user[0], user[1]))



# Create new node element with given tag for OSM

def add_node(node, tag):

	global osm_id

	osm_id -= 1

	node_element = {
		'type': 'node',
		'id': osm_id,
		'lat': node[1],
		'lon': node[0],
		'tags': tag
	}

	osm_elements.append(node_element)
	return node_element



# Create new way element for OSM

def add_way(import_coordinates, osm_element):

	global osm_id

	# Create new way

	if osm_element is None:

		osm_id -= 1
		way_element = {
			'id': osm_id,
			'type': 'way',
			'nodes': [],
			'tags': {}
		}
		osm_elements.append(way_element)

	# Or modify existing way and swap nodes

	else:
		swap_nodes(osm_element['nodes'], import_coordinates)
		way_element = osm_element
		way_element['nodes'] = []

	# Assign nodes in way

	for node in import_coordinates:
		node_tuple = (node[0], node[1])

		# Either reuse node already assigned or create new node

		if node_tuple in import_nodes:
			node_element = import_nodes[ node_tuple ]
		else:
			node_element = add_node(node_tuple, {})
			import_nodes[ node_tuple ] = node_element

		way_element['nodes'].append(node_element['id'])

	return way_element



# Match and merge given list of existing OSM nodes with given list of new imported nodes.

def swap_nodes(osm_way_nodes, import_coordinates):

	# Compile nodes to be swapped in

	new_import_nodes = set()

	for node in import_coordinates:
		node_tuple = (node[0], node[1])
		if node_tuple not in import_nodes:
			new_import_nodes.add(node_tuple)

	# Identify all node swaps within acceptable distance and put into sorted list

	swap_candidates = []
	for node_ref in osm_way_nodes:
		if node_ref in osm_nodes:
			osm_nodes[ node_ref ]['used'] -= 1

			tagged_node = ("tags" in osm_nodes[ node_ref ]
						and any(tag not in ["source", "source:date", "created_by"] for tag in osm_nodes[ node_ref ]['tags']))

			for import_node in new_import_nodes:
				node_distance = point_distance((osm_nodes[ node_ref ]['lon'], osm_nodes[ node_ref ]['lat']), import_node)

				if node_distance == 0 or osm_nodes[ node_ref ]['used'] == 0 and not tagged_node:
					swap = {
						'osm': node_ref,
						'import': import_node,
						'dist': node_distance
					}
					swap_candidates.append(swap)
	
	swap_candidates.sort(key=lambda d: d['dist'])
		
	# Swap nodes starting with the closest until exhausted

	for swap in swap_candidates:
		osm_node = osm_nodes[ swap['osm'] ]
		import_node = swap['import']

		if swap['dist'] == 0 or osm_node['used'] == 0 and import_node not in import_nodes:
			osm_node['used'] += 1

			if swap['dist'] > 0:
				osm_node['lon'] = import_node[0]
				osm_node['lat'] = import_node[1]
				osm_node['action'] = "modify"

			if "tags" in osm_node:
				for tag in ["source", "source:date", "created_by"]:
					if tag in osm_node['tags']:
						del osm_node['tags'][ tag ]
						osm_node['action'] = "modify"

			import_nodes[ import_node ] = osm_node

	# Delete remaining OSM nodes unless still in use or tagged

	for node_ref in osm_way_nodes:
		if (node_ref in osm_nodes and osm_nodes[ node_ref ]['used'] == 0
				and ("tags" not in osm_nodes[ node_ref ]
					 or not any(tag not in ["source", "source:date", "created_by"] for tag in osm_nodes[ node_ref ]['tags']))):
			osm_nodes[ node_ref ]['action'] = "delete"



# Check whether building types belong to same category

def similar_building_type(lm_building, osm_building):

	for category in similar_buildings.values():
		if lm_building in category and osm_building in category:
			return True

	return False



# Add or modify building

def add_building(building, osm_element):

	global osm_id

	if building['geometry']['type'] == "Point":
		return

	# Simple polygon

	elif len(building['geometry']['coordinates']) == 1:
		way_element = add_way(building['geometry']['coordinates'][0], osm_element)

		# Keep information about existing building=* tag + TYPE tag if different category

		if osm_element is not None:

			osm_tags = way_element['tags']
			lm_tags = building['properties']

			# Do not tag LM building description if not needed

			lm_type = ""
			if "BTYPE" in lm_tags:
				lm_type = lm_tags['BTYPE']
				del lm_tags['BTYPE']

			# Update tags

			for key, value in iter(lm_tags.items()):

				if key == "building":

					# LM overrides OSM
					if (osm_tags['building'] == "yes"
							or osm_tags['building'] == "residential" and value in lm_residential_tags
							or osm_tags['building'] == "house" and value == "detached"
							or osm_tags['building'] == "terrace" and value == "house"):
						osm_tags['building'] = value

					# Produce "warning"/tag suggestion
					elif (osm_tags['building'] != value
								and value != "yes"  # Too vague
								and "," not in lm_type
								and not similar_building_type(lm_tags['building'], osm_tags['building'])):
							osm_tags['LM_BUILDING'] = value
							if lm_type:
								osm_tags['BTYPE'] = lm_type

				# Produce information about LM name=* etc not used due to tag conflict
				elif key in osm_tags and osm_tags[ key ] != value:
					osm_tags[ "LM_" + key.upper() ] = value

				else:
					way_element['tags'][ key ] = value

			# Delete certain tags

			delete_tags = ["building:type", "source", "source:date", "created_by"]
			for key in list(osm_tags):
				if key in delete_tags or remove_addr and key[:5] == "addr:":
					del osm_tags[ key ]

		else:
			way_element['tags'].update(building['properties'])

		way_element['center'] = building['center']
		way_element['area'] = building['area']
		
		if osm_element is not None:
			way_element['action'] = "modify"

	# Multipolygon

	else:
		relation_element = {
			'type': 'relation',
			'members': [],
			'tags': building['properties']
		}
		relation_element['tags']['type'] = "multipolygon"

		role = "outer"

		for patch in building['geometry']['coordinates']:
			way_element = add_way(patch, None)
			member = {
				'type': 'way',
				'ref': way_element['id'],
				'role': role
			}
			relation_element['members'].append(member)
			role = "inner"  # Next patch

		osm_id -= 1
		relation_element['id'] = osm_id
		osm_elements.append(relation_element)



# Do reverse match to verify that two buildings are each others' best match

def reverse_match(import_building):

	found_building = None
	best_diff = 9999  # Dummy

	min_bbox = coordinate_offset(import_building['center'], - 2 * margin_hausdorff) #import_building['area'])
	max_bbox = coordinate_offset(import_building['center'], + 2 * margin_hausdorff) #import_building['area'])

	for osm_building in osm_buildings:

		if ("area" in osm_building
				and "ref:lantmateriet:byggnad" not in osm_building['tags']
				and min_bbox[0] < osm_building['center'][0] < max_bbox[0]
				and min_bbox[1] < osm_building['center'][1] < max_bbox[1]):  # and "action" not in osm_building

			diff_haus = hausdorff_distance(import_building['geometry']['coordinates'][0], osm_building['polygon'])
				
			if diff_haus < best_diff:
				found_building = osm_building
				best_diff = diff_haus

	return (found_building, best_diff)



# Merge import with OSM buildings

def merge_buildings():

	global import_buildings

	message ("Merging buildings ...\n")
	message ("\tMaximum Hausdorff difference: %i m (%i m for tagged buildings)\n" % (margin_hausdorff, margin_tagged))
	message ("\tMaximum area difference: %i %%\n" % ((1 - margin_area) * 100))

	count = len(osm_buildings)
	count_merge = 0
	count_ref = 0
	count_identical = 0

	# Remove import buildings which have already been imported

	message ("\tDiscover any earlier import ... ")

	osm_refs = set()
	for osm_element in osm_elements:
		if "tags" in osm_element and "ref:lantmateriet:byggnad" in osm_element['tags']:
			for ref in osm_element['tags']['ref:lantmateriet:byggnad'].split(";"):
				osm_refs.add(ref)

	count_import = len(import_buildings)
	import_buildings = [ building for building in import_buildings
						if "ref:lantmateriet:byggnad" not in building['properties']
							or building['properties']['ref:lantmateriet:byggnad'] not in osm_refs ]
	count_existing = count_import - len(import_buildings)

	message ("%i duplicate 'ref:lantmateriet:byggnad' found\n" % count_existing)

	# Loop osm buildings and attempt to find matching import buildings

	message ("\tMatch buildings ...\n")

	for osm_building in osm_buildings[:]:
		count -= 1
		message ("\r\t%i " % count)
		found_building = None
		best_diff = 9999  # Dummy

		# Skip test if ref:lantmateriet:byggnad exists (building has already been imported)

		if "ref:lantmateriet:byggnad" in osm_building['tags']:
			count_ref += 1
			continue

		# Get bbox for limiting search below

		min_bbox = coordinate_offset(osm_building['center'], - 2 * margin_hausdorff) # osm_building['area'])
		max_bbox = coordinate_offset(osm_building['center'], + 2 * margin_hausdorff) # osm_building['area'])

		for import_building in import_buildings:

			if ("area" in import_building
					and min_bbox[0] < import_building['center'][0] < max_bbox[0]
					and min_bbox[1] < import_building['center'][1] < max_bbox[1]):

				# Calculate Hausdorff distance to identify building with shortest distance
				diff_haus = hausdorff_distance(osm_building['polygon'], import_building['geometry']['coordinates'][0])
	
				if diff_haus < 1.0:
					count_identical += 1
					if debug:
						osm_building['tags']['IDENTICAL'] = " %.2f" % diff_haus

				if diff_haus < best_diff:
					found_building = import_building
					best_diff = diff_haus

		if found_building is not None:
			if debug:
				osm_building['tags']['HAUSDORFF'] = " %.2f" % best_diff

			# Also check if Hausdorff distance is within given limit (shorter limit for tagged buildings)
			if best_diff < margin_hausdorff and "tagged" not in osm_building or best_diff < margin_tagged:

				# Also check if both buildings are each others best match
				found_reverse, reverse_haus = reverse_match(found_building)

				if found_reverse == osm_building and reverse_haus < margin_hausdorff:

					# Compare building size
					if margin_area < osm_building['area'] / found_building['area'] < 1.0 / margin_area:

						add_building(found_building, osm_building)
						import_buildings.remove(found_building)
						count_merge += 1
					elif debug:
						osm_building['tags']['SIZE'] = "%.1f" % (osm_building['area'] / found_building['area'])

	# Add remaining import buildings which were not matched

	count_add = 0
	for building in import_buildings:
		if building['geometry']['type'] == "Polygon" and "building" in building['properties']:
			add_building(building, None)
			count_add += 1

	count_swap = sum(1 for node in import_nodes.values() if node['id'] > 0)

	message ("\r\tMerged %i buildings from OSM (%i%%)\n" % (count_merge, 100.0 * count_merge / len(osm_buildings)))
	message ("\t%i buildings had less than 1 meter offset\n" % count_identical)
	if count_ref > 0:
		message ("\tSkipped %i already imported buildings in OSM (%i%%)\n" % (count_ref, 100.0 * count_ref / len(osm_buildings)))
	message ("\tRemaining %i buildings from OSM not merged (%i%%)\n"
		% (len(osm_buildings) - count_merge - count_ref, 100 - 100.0 * (count_merge + count_ref) / len(osm_buildings)))
	message ("\tAdded %i new buildings from import file\n" % count_add)
#	message ("\t%i nodes swapped (%i%%)\n" % (count_swap, 100.0 * count_swap / len(import_nodes)))



# Identify new import buidings not overlapping with OSM buildings

def extract_new_buildings():

	global import_buildings

	message ("Discover new buildings ...\n")
#	message ("\tMaximum Hausdorff difference: %i m (%i m for tagged buildings)\n" % (margin_hausdorff, margin_tagged))
#	message ("\tMaximum area difference: %i %%\n" % ((1 - margin_area) * 100))

	# Remove import buildings which have already been imported

	message ("\tDiscover any earlier import ... ")

	osm_refs = set()
	for osm_element in osm_elements:
		if "tags" in osm_element and "ref:lantmateriet:byggnad" in osm_element['tags']:
			for ref in osm_element['tags']['ref:lantmateriet:byggnad'].split(";"):
				osm_refs.add(ref)

	count_import = len(import_buildings)
	import_buildings = [ building for building in import_buildings
						if "ref:lantmateriet:byggnad" not in building['properties']
							or building['properties']['ref:lantmateriet:byggnad'] not in osm_refs ]
	count_existing = count_import - len(import_buildings)

	message ("%i duplicate 'ref:lantmateriet:byggnad' found\n" % count_existing)

	# Discover and add non-overlapping new buildings

	if function == "new":

		# Create bbox for each building to spped up later matching

		for osm_building in osm_buildings:
			if "polygon" in osm_building:
				osm_building['min_bbox'] = (min([ node[0] for node in osm_building['polygon'] ]),
											min([ node[1] for node in osm_building['polygon'] ]))

				osm_building['max_bbox'] = (max([ node[0] for node in osm_building['polygon'] ]),
											max([ node[1] for node in osm_building['polygon'] ]))

		# Loop osm buildings and attempt to find matching import buildings

		message ("\tMatch buildings ...\n")

		count = len(import_buildings)
		count_add = 0

		for import_building in import_buildings:

			count -= 1
			message ("\r\t%i " % count)

			# Skip if import building is not polygon

			if import_building['geometry']['type'] != "Polygon" or "building" not in import_building['properties']:
				continue

			# Get bbox for limiting search below

			min_bbox = (min([ node[0] for node in import_building['geometry']['coordinates'][0] ]),
						min([ node[1] for node in import_building['geometry']['coordinates'][0] ]))
			max_bbox = (max([ node[0] for node in import_building['geometry']['coordinates'][0] ]),
						max([ node[1] for node in import_building['geometry']['coordinates'][0] ]))
			new_building = True

			for osm_building in osm_buildings:

				if ("polygon" in osm_building
						and min_bbox[0] < osm_building['max_bbox'][0] and max_bbox[0] > osm_building['min_bbox'][0]
						and min_bbox[1] < osm_building['max_bbox'][1] and max_bbox[1] > osm_building['min_bbox'][1]):
						# and "ref:lantmateriet:byggnad" not in osm_building['tags']:

					if polygon_overlap(import_building['geometry']['coordinates'][0], osm_building['polygon']):
						new_building = False
						break

			if new_building:
				add_building(import_building, None)
				count_add += 1

	# Add any new buildings ("missing" function)

	else:
		count_add = 0
		for building in import_buildings:
			if building['geometry']['type'] != "Point":
				add_building(building, None)
				count_add += 1

	message ("\r\tAdded %i new buildings from import file\n" % count_add)
	message ("\tRemaining %i buildings from OSM not touched\n" % len(osm_buildings))



# Indent XML output

def indent_tree(elem, level=0):
    i = "\n" + level*"  "
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = i + "  "
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
        for elem in elem:
            indent_tree(elem, level+1)
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
    else:
        if level and (not elem.tail or not elem.tail.strip()):
            elem.tail = i



# Generate one osm tag for output

def tag_property (osm_element, tag_key, tag_value):

	tag_value = tag_value.strip()
	if tag_value:
		osm_element.append(ET.Element("tag", k=tag_key, v=tag_value))



# Update element attributes of XML element

def set_attributes (element, data):

	if "user" in data:
		element.set('version', str(data['version']))
		element.set('user', data['user'])
		element.set('uid', str(data['uid']))
		element.set('timestamp', data['timestamp'])
		element.set('changeset', str(data['changeset']))
		element.set('visible', 'true')
		if "action" in data:
			element.set('action', data['action'])
	else:
		element.set('action', 'modify')
		element.set('visible', 'true')



# Output result

def save_file(filename):

	message ("Saving file ...\n")
	message ("\tFilename '%s'\n" % filename)

	count = 0
	osm_root = ET.Element("osm", version="0.6", generator="building_merge", upload="false")

	# First output all start/end nodes

	for element in osm_elements:

		if element['type'] == "node":
			osm_node = ET.Element("node", id=str(element['id']), lat=str(element['lat']), lon=str(element['lon']))
			set_attributes(osm_node, element)
			osm_root.append(osm_node)
			count += 1
			if "tags" in element:
				for key, value in iter(element['tags'].items()):
					tag_property (osm_node, key, value)

		elif element['type'] == "way":
			osm_way = ET.Element("way", id=str(element['id']))
			set_attributes(osm_way, element)
			osm_root.append(osm_way)
			count += 1

			if "tags" in element:
				for key, value in iter(element['tags'].items()):
					tag_property (osm_way, key, value)
		
			for node_ref in element['nodes']:
				osm_way.append(ET.Element("nd", ref=str(node_ref)))

		elif element['type'] == "relation":
			osm_relation = ET.Element("relation", id=str(element['id']))
			set_attributes(osm_relation, element)
			osm_root.append(osm_relation)
			count += 1

			if "tags" in element:
				for key, value in iter(element['tags'].items()):
					tag_property (osm_relation, key, value)

			for member in element['members']:
				osm_relation.append(ET.Element("member", type=member['type'], ref=str(member['ref']), role=member['role']))
		
	# Produce OSM/XML file

	osm_tree = ET.ElementTree(osm_root)
	indent_tree(osm_root)
	osm_tree.write(filename, encoding="utf-8", method="xml", xml_declaration=True)

	message ("\t%i elements saved\n" % count)



# Main program

if __name__ == '__main__':

	start_time = time.time()
	message ("\n*** building_merge %s ***\n\n" % version)

	municipalities = {}
	import_buildings = []
	osm_buildings = []
	osm_elements = []
	import_nodes = {}  # (x,y) index to imported nodes
	osm_nodes = {}
	osm_id = -1000

	# Parse parameters

	if len(sys.argv) < 2:
		sys.exit("Please provide municipality number or name\n")

	if len(sys.argv) > 2 and sys.argv[2].isdigit():
		factor = margin_tagged / margin_hausdorff 
		margin_hausdorff = int(sys.argv[2])
		margin_tagged = margin_hausdorff * factor

	function = "merge"
	if "-new" in sys.argv or "--new" in sys.argv:
		function = "new"

	elif "-missing" in sys.argv or "--missing" in sys.argv:
		function = "missing"

	if "-debug" in sys.argv or "--debug" in sys.argv:
		debug = True

	# Get municipality

	load_municipalities()
	municipality_query = sys.argv[1]
	municipality_id = get_municipality(municipality_query)
	if municipality_id is None or municipality_id not in municipalities:
		sys.exit("Municipality '%s' not found\n" % municipality_query)
	
	message ("Municipality: %s %s\n\n" % (municipality_id, municipalities[ municipality_id ]))

	# Get filename

	filename = "byggnader_%s_%s.geojson" % (municipality_id, municipalities[ municipality_id ].replace(" ", "_"))

	for arg in sys.argv[2:]:
		if ".geojson" in arg:
			filename = arg

	# Process

	load_import_buildings(filename)
	load_osm_buildings(municipality_id)

	if len(import_buildings) > 0 and len(osm_buildings) > 0:
		lap = time.time()

		if function == "merge":
			merge_buildings()
			filename = filename.replace(".geojson", "") + "_merged.osm"
		else:  # "new", "missing"
			extract_new_buildings()
			filename = filename.replace(".geojson", "") + "_new.osm"

		used_time = time.time() - start_time
		message("\tTime: %s\n" % timeformat(used_time))

		filename = filename.rpartition("/")[2]
		save_file(filename)

	used_time = time.time() - start_time
	message("Done in %s (%i buildings per second)\n\n" % (timeformat(used_time), len(osm_buildings) / used_time))
