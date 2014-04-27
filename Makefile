compilecoq := coqc -noglob -init-file coq.config
coq_makefile := coq_makefile
coq_top := coqtop -R . ""
coqsource := $(shell find src -name \*.v)
src_dir := src
class_src_dir := $(src_dir)/classes
type_src_dir := $(src_dir)/types
output_dir := build

class_build_src := $(patsubst $(class_src_dir)/%.v,$(output_dir)/%.v,$(coqsource))
type_build_src := $(patsubst $(type_src_dir)/%.v,$(output_dir)/%.v,$(coqsource))
all_build_src := $(class_build_src) $(type_build_src) $(output_dir)/Haskell.v
drop_build_dir := $(patsubst $(output_dir)/%,%,$(all_build_src))

.PHONY: clean

default: all

makefile: $(all_build_src)
	cd $(output_dir); $(coq_makefile) Haskell.v > Makefile.coq

console: $(all_build_src)
	cd $(output_dir); $(coq_top)

all: makefile
	cd $(output_dir); make -f Makefile.coq

# ch1 targets

$(output_dir):
	mkdir -p $(output_dir)

$(output_dir)/%.v: $(class_src_dir)/%.v $(output_dir)
	cp $< $@

$(output_dir)/%.v: $(type_src_dir)/%.v $(output_dir)
	cp $< $@

$(output_dir)/Haskell.v: $(src_dir)/Haskell.v
	cp $(src_dir)/Haskell.v $(output_dir)/Haskell.v

clean:
	rm -rfv $(output_dir)/*
