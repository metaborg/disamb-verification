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
read -p "FINISHED, press enter to continue"
