#!/bin/bash
git submodule update --init
cd microtonal-utils
npm install && npm run build:all
cd ..
mv microtonal-utils/dist microtonal-utils-dist
