#!/bin/bash
pushd .
tmpdir=tmp_dir
git clone https://github.com/BenKaufmann/program-opts.git  --branch master --single-branch $tmpdir
cd $tmpdir
cp -r src          ../libprogram_opts
cp -r program_opts ../libprogram_opts

popd
rm -rf $tmpdir

