coqdoc --body-only -s --latex StringHelper.v -o ~/school/msc/StringHelper.tex
coqdoc --body-only -s --latex AuthenticationSystem.v -o ~/school/msc/AuthenticationSystem.tex
coqdoc --body-only -s --latex Login.v -o ~/school/msc/Login.tex
coqdoc --body-only -s --latex VCRIO.v -o ~/school/msc/VCRIO.tex
coqdoc --body-only -s --latex Extract.v -o ~/school/msc/Extract.tex

ocamldoc -notoc -latex -I ../../src/ocaml/ -I .extract .extract/Login.ml -o ~/school/msc/MLExtract.tex 
