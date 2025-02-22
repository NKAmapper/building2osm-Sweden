# building2osm-sweden
Tools for importing buildings in Sweden to OpenStreetMap

### building2osm

Downloads buildings from Geotorget and generates tagged geojson import file with building footprints.

Usage:
<code>python3 building2osm.py \<municipality\> [\<filename.geosjon\>] [-split] [-original] [-verify] [-debug]</code>

Parameters:
* _municipality_ - Name of the municipality to generate. Output for several municipalities if "Sweden" is given.
* _filename.geojson_ - Optional file containing source data of buildings for municipality, otherwise automatic downloading from Geotorget.
* <code>-split</code> - Also split output file into smaller subdivisions ("bydel", electoral or post districts).
* <code>-original</code> - Produce file without any modifications.
* <code>-verify</code> - Include extra tags for verification of topology modifications.
* <code>-debug</code> - Include extra tags for debugging.

### building_merge

Conflates the geojson import file with existing buildings in OSM and produces an OSM file for manual verification and uploading. First generate the import file with _building2osm.py_ or download from [OSM building import progress](https://wiki.openstreetmap.org/wiki/Import/Catalogue/Sweden_Building_Import/Progress).

Usage:
<code>python3 building_merge.py \<municipality\> [\<max distance\>] [\<filename.geojson\>] [-debug]</code>

Parameters:
* _municipality_ - Name of the municipality to conflate.
* _max distance_ - Optional maximum Hausdorff distance between matched buildings. Default value is 10 metres (5 metres if the building is tagged). Increase if needed for larger offsets.
* _filename.geojson_ - Optional input file in geojson format. If not specified, the import file for the municipality will be loaded (it must be present in the default folder or in a predefined folder).
* <code>-debug</code> - Include extra tags for debugging.

### building_split

Split building import file into smaller subdivisions. Useful is municipality contains more than approx. 10.000 buildings.

usage:
<code>python3 building_split.py \<municipality\> | \<filename.geosjon\> [\<target_size\>] [-tag] [-debug]</code>

Parameters:
* _municipality_ - Either name of the municipality (will produce filename).
* _filename.geosjon_ - Or name of import file to split.
* _target_size_ - Optional target size, i.e. number of buildings per partitioned file (default 10.000).

### Notes
* Source data is from Lantmäteriet. 
* The <code>building=*</code> tag is given a value corresponding to the _building_tags_ translation table in this respository. Please provide feedback if you observe that the tagging should be modified. 
* Certain modifications of the footprint polygons are made to avoid clutter in OSM:
  * Polygons which are almost square are rectified (orthogonalized) to get exact 90 degrees corners. Groups of connected buildings are rectified as a group. Multipolygons are supported. A polygon is not rectified if it would relocate one of its nodes by more than 20 centimeters.
  * Redundant nodes are removed if they are located on an (almost) straight line.
  * Curved walls are only simplified lightly.
* Output is stored in a geosjon file which may be loaded into JOSM when the OpenData plugin has been installed. Please read the [import plan](https://wiki.openstreetmap.org/wiki/Import/Catalogue/Sweden_Building_Import) for guiding on how to do the import.
* The _building_merge.py_ program conflates the import buildings with existing buildings in OSM.
  * New buildings are loaded from the geojson import file. You may split the import file into smaller parts using _municipality_split.py_ or manually.
  * Existing buildings are loaded from OSM.
  * New and existing buildings which are each other's best match within the given maximum Hausdorff distance (default 10 metres) are automatically conflated. They also need to have similar size (default up to 50% difference).
  * The <code>OSM_BUILDING=*</code> tag will show which building tag was used by the existing building, unless they are in similar residential/commercial/farm categories.
  * Use the To-do plugin in JOSM to:
    1) Resolve _Overlapping buildings_ warnings. 
    2) Resolve _Building within buildings_ warnings.
    3) Check <code>LM_BUILDING=*</code> for considering manual retagging of building types.
    4) Check untouched existing OSM buildings (search for <code>building=* -modified -parent modified</code>).
    5) Check if entrances or other tagged nodes needs to be reconnected to the new buildings (search for <code>type:node ways:0 -untagged</code>).
  * Consider using _Edit->Purge_ in JOSM to work on a subset of a large municipality.
  * The _building_merge.py_ program may be run several times for the same municipality. Only buildings with a new _ref:lantmateriet:byggnad_ tag will be added each time.

### Changelog
* Added _building_split.py_.

### References

* [Lantmäteriet product page](https://geotorget.lantmateriet.se/dokumentation/GEODOK/25/latest.html)
* [OSM Sweden building import plan](https://wiki.openstreetmap.org/wiki/Import/Catalogue/Sweden_Building_Import)
* [OSM building import progress](https://wiki.openstreetmap.org/wiki/Import/Catalogue/Sweden_Building_Import/Progress)
