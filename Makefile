all: main.hs
	ghc --make main.hs
	hastec main.hs

clean:
	rm -r main main.js main.hi main.o
