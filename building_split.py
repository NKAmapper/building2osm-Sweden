#!/usr/bin/env python3
# -*- coding: utf8

# building_split.py
# Splits buildings import file into smaller parts.
# Usage: building_split.py <municipality name> or <filename.geojson> [<split size>] [-tag/-one] [-debug].
# Creates partitioned geojson files.

import math
import sys
import time
import json
import os.path
import urllib.request, urllib.parse


version = "0.3.0"

overpass_api = "https://overpass-api.de/api/interpreter"  # Overpass endpoint
#overpass_api = "https://overpass.kumi.systems/api/interpreter"

import_folder = "~/Jottacloud/OSM/Byggnader Sverige/"  # Folder containing import building files (default folder tried first)

debug = False

max_inside_box = 10000



# Output message to console

def message (text):

	sys.stderr.write(text)
	sys.stderr.flush()



# Compute approximation of distance between two coordinates, (lat,lon), in meters
# Works for short distances

def distance (point1, point2):

	lon1, lat1, lon2, lat2 = map(math.radians, [point1[0], point1[1], point2[0], point2[1]])
	x = (lon2 - lon1) * math.cos( 0.5*(lat2+lat1) )
	y = lat2 - lat1
	return 6371000.0 * math.sqrt( x*x + y*y )  # Metres



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



# Tests whether point (x,y) is inside a polygon
# Ray tracing method
# Not used (useful if boundary polygons are used later)

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



# Test whether point (x,y) is inside a multipolygon, i.e. not inside inner polygons
# Not used (useful if boundary polygons are used later)

def inside_multipolygon (point, multipolygon):

	if type(multipolygon) is list and len(multipolygon) > 0 and type(multipolygon[0]) is list:

		if len(multipolygon[0]) > 0 and type(multipolygon[0][0]) is list:

			for patch in multipolygon:
				if inside_multipolygon(point, patch):
					return True
			return False

		elif multipolygon[0][0] == multipolygon[0][-1]:

			inside = inside_polygon(point, multipolygon[0])
			if inside:
				for patch in multipolygon[1:]:
					inside = (inside and not inside_polygon(point, patch))
					if not inside:
						break

			return inside

		else:
			return None
	else:
		return None



# Load dict of all municipalities

def load_municipalities():

	url = "https://catalog.skl.se/rowstore/dataset/4c544014-8e8f-4832-ab8e-6e787d383752/json?_limit=400"
	try:
		file = urllib.request.urlopen(url)
	except urllib.error.HTTPError as e:
		sys.exit("\t*** Failed to load municipalities, HTTP error %i: %s\n\n" % (e.code, e.reason))
	data = json.load(file)
	file.close()

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



# Load import buildings from geojson file

def load_import_buildings(filename):

	global import_buildings

	message ("Loading import buildings ...\n")

	if not os.path.isfile(filename):
		test_filename = os.path.expanduser(import_folder + filename)
		if os.path.isfile(test_filename):
			filename = test_filename
		else:
			sys.exit("\t*** File not found\n\n")

	message ("\tFilename '%s'\n" % filename)
	file = open(filename)
	data = json.load(file)
	file.close()
	import_buildings = data['features']

	# Add polygon center and area

	for building in import_buildings:

		if "properties" not in building or "building" not in building['properties']:
			continue

		if building['geometry']['type'] == "Polygon" and len(building['geometry']['coordinates']) == 1:
			building['centre'] = polygon_center( building['geometry']['coordinates'][0] )
			buildings.append(building)

	message ("\tLoaded %i buildings\n" % len(buildings))



# Mark buildings with subdivision

def mark_buildings(min_bbox, max_bbox, subdivision):

	# Mark buildings within box

	marked_buildings = set()
	for building in buildings:
		if ("PART" not in building['properties']
				and min_bbox[0] <= building['centre'][0] <  max_bbox[0]
				and min_bbox[1] <= building['centre'][1] <  max_bbox[1]):
			building['properties']['PART'] = str(subdivision)
			if "ref:lantmateriet:byggnad" in building['properties']:
				marked_buildings.add(building['properties']['ref:lantmateriet:byggnad'])

	# Keep buildings with same ref to same box

	for building in buildings:
		if ("PART" not in building['properties']
				and "ref:lantmateriet:byggnad" in building['properties']
				and building['properties']['ref:lantmateriet:byggnad'] in marked_buildings):
			building['properties']['PART'] = str(subdivision)



# Recursively split buildings into smaller boxes until number of buildings is sufficiently small

def split_box(min_bbox, max_bbox, level):

	global subdivision

	# Count buildings inside box

	inside_box = 0
	for building in buildings:
		if min_bbox[0] <= building['centre'][0] <  max_bbox[0] and min_bbox[1] <= building['centre'][1] <  max_bbox[1]:
			inside_box += 1

	# Stop recurse if count is sufficiently small

	if inside_box <= max_inside_box:

		# Do not create new part if count is too small
		if inside_box < max_inside_box * 0.6 and level > 1:
			if debug:
				message ("%sNo save %i\n" % (("\t" * level), inside_box))		
			return 0
		else:		
			# Creeate new part and mark buildings
			subdivision += 1
			mark_buildings(min_bbox, max_bbox, subdivision)
			if debug:
				message ("%sSAVE BOX %i %i\n" % (("\t" * level), subdivision, inside_box))
			return inside_box

	# Recurse to get fewer buildings per box

	else:
		if debug:
			message ("%sSplit box %i\n" % (("\t" * level), inside_box))
		saved = 0

		# Split along longest axis (x or y) and recurse

		if distance((min_bbox[0], max_bbox[1]), max_bbox) > distance(min_bbox, (min_bbox[0], max_bbox[1])):  # x longer than y
			# Split x axis
			half_x = 0.5 * (max_bbox[0] + min_bbox[0])
			saved += split_box(min_bbox, (half_x, max_bbox[1]), level + 1)
			saved += split_box((half_x, min_bbox[1]), max_bbox, level + 1)
		else:
			# Split y axis
			half_y = 0.5 * (max_bbox[1] + min_bbox[1])
			saved += split_box(min_bbox, (max_bbox[0], half_y), level + 1)
			saved += split_box((min_bbox[0], half_y), max_bbox, level + 1)

		# Pick up buildings inside box which were not partitioned during recursion. Save is count is sufficiently high.

		if saved < inside_box and (inside_box - saved >= max_inside_box * 0.25 or level == 1):

			# Create new part and mark buildings
			subdivision += 1
			mark_buildings(min_bbox, max_bbox, subdivision)
			if debug:
				message ("%sSAVE REST %i %i\n" % (("\t" * level), subdivision, inside_box - saved))
			saved = inside_box

		return saved



# Split file into subdivisions and save files

def split_buildings():

	message ("Split file into subdivisions ...\n")

	min_bbox = (min([ building['centre'][0] for building in buildings ]),
				min([ building['centre'][1] for building in buildings ]))
	max_bbox = (max([ building['centre'][0] for building in buildings ]) + 0.0001,
				max([ building['centre'][1] for building in buildings ]) + 0.0001)

	# Start recursive splitting into boxes

	split_box(min_bbox, max_bbox, 1)

	for building in buildings:
		if "centre" in building:
			del building['centre']

	message ("\t%i subdivisions: " % subdivision)

	count_parts = [ str(sum(1 for b in buildings if b['properties']['PART'] == str(part) ))
							for part in range(1, subdivision + 1) ]
	message ("%s\n" % ", ".join(count_parts))



# Save splittedfiles

def save_buildings(filename, one_file):

	if subdivision < 2:
		message ("No saved file\n")
		return

	message ("Saving partitions ...\n")

	out_filename = filename.split("/")[-1]

	# Save to one file with tagged parts

	if one_file:

		collection = {
			'type': 'FeatureCollection',
			'features': buildings
		}

		part_filename = out_filename.replace(".geojson", "") + "_parts.geojson"
		file = open(part_filename, "w")
		json.dump(collection, file, ensure_ascii=False)  # indent=1
		file.close()		

		message ("\tSaved %i buildings to file '%s'\n" % (len(buildings), part_filename))

	# Split and save into several part files

	else:

		for i in range(1, subdivision + 1):
			part_filename = out_filename.replace(".geojson", "_part_%i.geojson" % i)

			features = []
			for building in buildings:
				if "PART" in building['properties'] and building['properties']['PART'] == str(i):
					del building['properties']['PART']
					features.append(building)

			collection = {
				'type': 'FeatureCollection',
				'features': features
			}

			file = open(part_filename, "w")
			json.dump(collection, file, ensure_ascii=False)  # indent=1
			file.close()

			message ("\tSaved %i buildings to file '%s'\n" % (len(features), part_filename))


# Main program

if __name__ == '__main__':

	message ("\n*** building_split %s ***\n\n" % version)

	municipalities = {}
	buildings = []
	subdivision = 0

	if "-debug" in sys.argv:
		debug = True

	# Get municipality

	if len(sys.argv) < 2:
		sys.exit("Please provide name of municipality or geosjon filename\n")

	load_municipalities()

	if ".geojson" in sys.argv[1]:
		filename = sys.argv[1]

	else:
		municipality_query = sys.argv[1]
		municipality_id = get_municipality(municipality_query)
		message ("Municipality: %s %s\n" % (municipality_id, municipalities[ municipality_id ]))
		filename = "byggnader_%s_%s.geojson" % (municipality_id, municipalities[ municipality_id ].replace(" ", "_"))

	if len(sys.argv) > 2 and sys.argv[2].isdigit():
		max_inside_box = int(sys.argv[2])

	message ("Target size:  %i\n\n" % max_inside_box)

	load_import_buildings(filename)

	split_buildings()

	if "-tag" in sys.argv or "-one" in sys.argv:
		save_buildings(filename, one_file=True)
	else:
		save_buildings(filename, one_file=False)

	message ("\n")
