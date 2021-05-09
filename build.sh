#!/bin/bash

# Clear out the `dist` directory
rm -rf dist
mkdir dist

# Move the source files
cp *.js dist
cp *.html dist
cp *.css dist
cp *.ttf dist
cp favicons/* dist
cp .nojekyll dist

# Build microtonal-utils and move its dist
cd microtonal-utils
npm install && npm run build:all
cd ..
mkdir dist/microtonal-utils
cp -R microtonal-utils/dist dist/microtonal-utils/dist

# Move scale-workshop sources
mkdir -p dist/scale-workshop/src
cp -R scale-workshop/src/js dist/scale-workshop/src/js
cp -R scale-workshop/src/lib dist/scale-workshop/src/lib
