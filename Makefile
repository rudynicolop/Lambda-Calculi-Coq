.PHONY: all build install clean

all: build

build:
	dune build -p lambda

install:
	dune install -p lambda

clean:
	dune clean -p lambda
