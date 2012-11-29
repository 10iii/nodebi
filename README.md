bi
==
Pure JavaScript Big Integer module for node.js
Copyright (c)  2012  10iii
All Rights Reserved.
This module is released under a BSD license.

This module is modified from Tom Wu's jsbn library. Which is also under a BSD license.
See http://www-cs-students.stanford.edu/~tjw/jsbn/

The main change from jsbn is using a buff array instead of hashset member to keep digits
and estimate buff size when create a new BI object during calculating.
For detail see https://github.com/10iii/nodebi
