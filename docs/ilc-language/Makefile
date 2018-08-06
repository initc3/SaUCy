DOC = ilc.tex
PDFLATEX = latex 
BIBTEX = bibtex
RERUN = "(There were undefined (references|citations)|Rerun to get (cross-references|the bars) right)"
RERUNBIB = "No file.*\.bbl|Citation.*undefined"
TARDIR = $(DOC:.tex=-src)

IMG_SRCS = $(wildcard figures/*-source.pdf)
IMG_OBJS = $(patsubst %-source.pdf,%.eps,$(IMG_SRCS))

ALL_TEX_FILES = $(shell find . -type f -name '*.tex')
BIB_FILES = $(wildcard *.bib)

.PHONY: pdf clean

pdf: images $(DOC:.tex=.pdf)

all: pdf

%.pdf: %.tex *.tex $(BIB_FILES) $(IMG_OBJS) $(ALL_TEX_FILES)
	$(eval DOC_BASE := $(shell basename $@ .pdf))
	rm -f $(DOC_BASE).bbl
	${PDFLATEX} $<
	egrep -c $(RERUNBIB) $*.log && ($(BIBTEX) $*;$(PDFLATEX) $<) ; true
	egrep $(RERUN) $*.log && ($(PDFLATEX) $<) ; true
	egrep $(RERUN) $*.log && ($(PDFLATEX) $<) ; true
	egrep -i "(Reference|Citation).*undefined" $*.log ; true
	dvips -o $(DOC_BASE).ps -t letter $(DOC_BASE).dvi
	ps2pdf14 -dPDFSETTINGS=/prepress -dEmbedAllFonts=true $(DOC_BASE).ps


clean:
	find . -name "*.aux" | xargs rm -f
	find . -name "*.log" | xargs rm -f
	find . -name "*.out" | xargs rm -f
	@\rm -f \
        $(DOC:.tex=.dvi) \
        $(DOC:.tex=.pdf) \
        $(DOC:.tex=.ps)  \
        $(DOC:.tex=.bbl) \
        $(DOC:.tex=.blg) \
        $(DOC:.tex=.lof) \
        $(DOC:.tex=.lot) \
        $(DOC:.tex=.loc) \
        $(DOC:.tex=.lol) \
	$(DOC:.tex=-src.tar.gz)

images: $(IMG_OBJS)

%.eps: %-source.pdf
	pdftops -eps $< $(<:-source.pdf=.eps)

veryclean: clean
	@\rm -f *~ *.log
	@\rm -f figures/*.eps

tar: pdf
	@test -d $(TARDIR) || mkdir $(TARDIR)
	@cp Makefile *.{tex,bib,bst,cls} $(TARDIR)
	@tar cz $(TARDIR) > $(TARDIR).tar.gz
	@rm -rf $(TARDIR)
