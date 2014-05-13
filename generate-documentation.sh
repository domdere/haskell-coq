#!/bin/bash

# Generates the documentation and puts it in the gh-pages branch
# Taken from https://github.com/jspahrsummers/documentalist/blob/master/generate-pages and modified.

# can run this script in git hooks, can use
# "`git branch | grep '\*' | cut -f2 -d' '`" == "master"
# to check that the branch is set to master.

# i use this in my hook:

#BRANCH=`git branch | grep '\*' | cut -f2 -d' '`
#
#if [ $BRANCH == "master" ]
#then
#    echo "Generating Coq Documentation in gh-pages"
#    ./generate-documentation.sh
#    git checkout master
#fi


set -x
set -o

PUBDOCDIR=`mktemp -d -t pages.XXXXXX`

make html

mv build/html $PUBDOCDIR

HEAD=`git rev-parse HEAD`

git checkout gh-pages
git rm -rf --ignore-unmatch .

mv $PUBDOCDIR/html/* .

rm -rf $PUBDOCDIR

git add -A

git commit --allow-empty -m "Generated documentation from $HEAD"
