void main() {
  int a;
  a = 1;
  int *b;
  b = 1;
  *b = 1;
  if (a==*b)
	print 0;
  if (a==b)
    print 2; 
}