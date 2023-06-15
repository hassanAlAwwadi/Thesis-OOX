This directory contains two bugs taken from the Defects4J repository <https://github.com/rjust/defects4j>, which were manually converted to OOX.

1. Collections 25
2. Compress 3

The Collections 25 bug can be found in collections_25.oox. The original code has not been copied but can be found in the Defects4J repository, I recommend using Docker to run Defects4J.


For the Compress 3 bug, we have copied the relevant java classes to each bug/java/original.
In bug/java/modified we have removed unused and or irrelevant code to the bug.
The reason for removing code is that OOX cannot support all operations yet (Strings, etc) and to reduce the manual work of converting them.