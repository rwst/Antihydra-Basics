\\ Fill [1..1000] with orbits of D(n+1)=ceil(3*D(n)/2)
\\ Each position gets the start value of the orbit that covers it

arr = vector(1000);

{
s = 1;
while(s <= 1000,
  d = s;
  while(d <= 1000,
    arr[d] = s;
    d = ceil(3*d/2);
  );
  s++;
  while(s <= 1000 && arr[s], s++);
);
}

{
for(i = 1, 100,
  if(i > 1, printf(", "));
  printf("%d", arr[i]);
);
}
