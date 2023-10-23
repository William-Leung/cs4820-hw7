#include <iostream>
#include <fstream>

using namespace std;

int main()
{
  ofstream outfile("test.txt");

  int n = 2000;
  int m = 2000;
  int p = 10;
  outfile << n << " " << m << " " << p << endl;

  bool first = true;
  for (int i = 0; i < n; i++)
  {
    outfile << rand() % 1000 + 1 << endl;
  }
  for(int i = 1; i < m; i++){
    outfile << i << " " << i+1 << " " << rand() % 1000 + 1 << endl;
  }
  outfile << "1 2000 50" << endl;

  outfile.close();
  return 0;
}