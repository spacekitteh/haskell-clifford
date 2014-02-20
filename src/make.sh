ghc clifford.lhs && latexmk -c clifford.lhs && lhs2TeX clifford.lhs > clifford.tex && latexmk clifford.tex -lualatex && latexmk -c && evince clifford.pdf
