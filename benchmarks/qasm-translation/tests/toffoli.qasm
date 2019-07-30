gate toffoli a, b, c {
  h c;
  T a; T b; T c;
  cx a, b; cx a, c;
  tdg b; tdg c;
  cx b, c; cx c, a;
  T a; tdg c;
  cx c, a; cx a, b; cx b, c;
  h c;
}
