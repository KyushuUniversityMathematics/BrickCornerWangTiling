.SUFFIXES: .svg .png
.SUFFIXES: .v .ml
.svg.png:
	rsvg-convert $< > $@
.v.ml:
	coqc $<

examplepng = b22a.png b22b.png b22c.png b44a.png b44b.png b44c.png
examplesvg = b22a.svg b22b.svg b22c.svg b44a.svg b44b.svg b44c.svg 

all: TilingRender

TilingRender: TilingProgram.ml TilingRender.ml
	-rm TilingProgram.mli
	ocamlc TilingProgram.ml TilingRender.ml -o TilingRender

png: TilingRender
	./TilingRender
	make $(examplepng)

clean:
	rm -f *.cmo *.cmi *.png *.svg ./TilingRender ./TilingProgram.ml
