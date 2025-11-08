#!/usr/bin/env zsh

# Source: https://www.iana.org/assignments/media-types/media-types.xhtml

set -e -o pipefail

# cd to script directory
cd ${0:h}

curl -sSO https://www.iana.org/assignments/media-types/media-types.xml
fgrep '<file ' media-types.xml | cut -f2 -d'>' | cut -f1 -d'<' | sort | uniq \
  >media-types.txt
