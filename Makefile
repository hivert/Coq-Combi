# OPT=-load-vernac-source init.v

include Makefile.coq

COQDOCFLAGS += --lib-subtitles

TAGS: $(VFILES)
	coqtags $(VFILES)

clean::
	- rm -rf depend.d depend.dot depend.pdf html scripts/ocamldot scripts/ocamldot.ml scripts/ocamldot.cmi scripts/ocamldot.cmo mlihtml

# dependency on all instead of $(GLOBFILES) to workaround for Coq Bug 4660
dochtml: all $(VFILES) html/depend.png html/depend.svg
	rm -f html/*.html
	$(COQDOC) -toc $(COQDOCFLAGS) -html -g $(COQDOCLIBS) -d html $(COQEXTLIBS) $(VFILES)
	rm -f html/index_lib.html
	mv html/index.html html/index_lib.html
	cat scripts/header.html html/depend.map scripts/footer.html > html/index.html


depend.d: .coqdeps.d
	rm -f depend
	cat .coqdeps.d | sed -e 's/[^ ]*glob//g' | sed -e 's/[^ ]*beautified//g' > depend.d

scripts/ocamldot: scripts/ocamldot.mll
	ocamllex scripts/ocamldot.mll
	ocamlc -o $@ scripts/ocamldot.ml

depend.dot: depend.d scripts/ocamldot
	rm -f depend.dot
	scripts/ocamldot depend.d > depend.dot
	sed -i -e "s/Theories/Combi/g" -e "s/3rdparty.ALEA/ALEA/g" -e "s/\//./g" depend.dot

html/depend.png: depend.dot
	- mkdir -p html
	dot -Tpng -o html/depend.png -Tcmapx -o html/depend.map depend.dot

html/depend.svg: depend.dot
	- mkdir -p html
	dot -Tsvg -o html/depend.svg depend.dot

depend.pdf: depend.dot
	rm -f depend.pdf
	dot -Tpdf -o depend.pdf depend.dot

update-github-doc: dochtml
	rm -rf /tmp/doctmp
	git clone git@github.com:hivert/Coq-Combi.git -b gh-pages /tmp/doctmp
	rsync -avP --delete --exclude .git --exclude README.md html/ /tmp/doctmp
	cd /tmp/doctmp && git add --all && git commit -m "Updated doc"
	cd /tmp/doctmp && git push
