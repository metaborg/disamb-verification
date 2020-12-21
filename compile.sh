if [ -d stdpp ]
then
  echo updating and compiling stdpp library
else
  echo stdpp library not detected, cloning git repository
  git clone https://gitlab.mpi-sws.org/iris/stdpp.git
  echo finished cloning stdpp
  echo compiling stdpp library
fi
cd stdpp
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
echo compiling IPGrammar.v
coqc IPGrammar.v
echo compiling IPGrammarSafety.v
coqc IPGrammarSafety.v
read -p "FINISHED, press enter to continue"
