
void main(int n) {
  int y;
  y = 1889;
  while (y < n) {
    y = y + 1;
    if (leapyear(y))
      print y;
    if(leapyear1(y))
	   print y;
  }
}

int leapyear(int y) {
  return y % 4 == 0 && (y % 100 != 0 || y % 400 == 0);
}
char leapyear1(int y) {
  return y % 4 == 0 && (y % 100 != 0 || y % 400 == 0);
}
