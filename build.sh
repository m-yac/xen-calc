#!/bin/bash
cd microtonal-utils
npm install && npm run build:all
cd ..
rm -r microtonal-utils-dist
mv microtonal-utils/dist microtonal-utils-dist
