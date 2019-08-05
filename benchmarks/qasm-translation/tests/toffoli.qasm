OPENQASM 2.0;
gate toffoli a, b, c {
  h c;
  t a; t b; t c;
  cx a, b; cx a, c;
  tdg b; tdg c;
  cx b, c; cx c, a;
  t a; tdg c;
  cx c, a; cx a, b; cx b, c;
  h c;
}
