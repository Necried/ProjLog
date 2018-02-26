# Project LogGen and Upkeep
A Client-Server Interface providing automatic project log generation and upkeep.

This side-project is implemented using Haste and Haskell, and was created to
facilitate a deeper understanding of using the aforementioned technologies,
especially Haste.App's client-server capabilities.

Requirements
------------
* [Haste](http://haste-lang.org) version 0.6.0.0
* Haste-App version 0.6.0.0
* `haste-prim` and `haste-lib`, version 0.6.0.0
* GHC version 7.10
* LaTeX

How to run
----------
* Execute `make` from source directory
* Run the executable `main` from the command line
* Open index.html in a browser

TODO
----
* Embed a PDF viewer in the browser in conjunction with downloading the PDF.
* Beautify the layout, possibly with Bootstrap.
* Allow deletions of log entries and files.
* "Sessionize" the entire thing, will probably not be done anytime soon.
* Implement the actual tex-pdf file writing and conversion
* Implement HTML form submissions with Haste.App
