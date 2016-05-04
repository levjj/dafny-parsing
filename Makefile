default: clean Parsing.dll

clean:
	rm -f *.dll *.mdb *.exe Parsing.cs Example.cs

Parsing.dll: Parsing.dfy ParsingNative.cs
	dafny Parsing.dfy ParsingNative.cs

test: Parsing.dll
	dafny /compile:3 Example.dfy ParsingNative.cs
