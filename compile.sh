if [ -d stdpp ]
then
  echo compiling stdpp library
else
  echo stdpp library not detected, cloning git repository
  git clone https://gitlab.mpi-sws.org/iris/stdpp.git
  echo finished cloning stdpp
  echo compiling stdpp library
fi
cd stdpp
git checkout 13df6821
git pull
make
cd ..
echo finished compiling stdpp library
echo compiling MyUtils.v
coqc MyUtils.v
echo compiling IGrammar.v
coqc IGrammar.v
echo compiling IGrammarTheorems.v
coqc IGrammarTheorems.v
echo compiling IGrammarBonusTheorems.v
coqc IGrammarBonusTheorems.v
echo compiling IPGrammar.v
coqc IPGrammar.v
echo compiling IPGrammarTheorems.v
coqc IPGrammarTheorems.v
echo compiling IPPGrammar.v
coqc IPPGrammar.v
echo compiling IPPGrammarTheorems.v
coqc IPPGrammarTheorems.v

read -p "FINISHED, press enter to continue"
