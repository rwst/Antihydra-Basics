\\ Fill [1..1000] with orbits of D(n+1)=ceil(3*D(n)/2)
\\ Collect starting values of each new orbit

hit = vector(1000);
starts = List();

{
s = 1;
while(s <= 1000,
  listput(starts, s);
  d = s;
  while(d <= 1000,
    hit[d] = 1;
    d = ceil(3*d/2);
  );
  s++;
  while(s <= 1000 && hit[s], s++);
);
}

{
for(i = 1, #starts,
  if(i > 1, printf(", "));
  printf("%d", starts[i]);
);
}
