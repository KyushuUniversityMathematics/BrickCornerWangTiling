.SUFFIXES: .svg .png .v .ml
.svg.png:
	rsvg-convert $< > $@
.ml.v:
	coqc $<

examplepng = b22a.png b22b.png b22c.png b44a.png b44b.png b44c.png
examplesvg = b22a.svg b22b.svg b22c.svg b44a.svg b44b.svg b44c.svg 

all: TilingRender

TilingRender: TilingProgram.ml TilingRender.ml
	ocamlc TilingProgram.ml TilingRender.ml -o TilingRender

svg.made: TilingRender
	./TilingRender
	touch svg.made

png: svg.made $(examplepng)
	@echo $(examplepng)

clean:
	rm -f *.cmo *.cmi *.png *.svg svg.made
