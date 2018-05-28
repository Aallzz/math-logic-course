.PHONY: pack all run clean
GENERATED=
OCAMLC=ocamlc # ocamlopt for speed
PACKAGE=hw4.zip

ifeq ($(OS),Windows_NT)
	DEL=del /f
else
	DEL=rm -f
endif

all: main.exe

run: main.exe
	./main.exe

main.exe: $(GENERATED)
	cd src && $(OCAMLC) str.cma $(GENERATED:src/%=%) main.ml -o ../main.exe

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src

clean:
	cd src && $(DEL) $(GENERATED:src/%=%) *.c* *.o*
	$(DEL) main.exe $(PACKAGE)
