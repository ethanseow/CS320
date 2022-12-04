let rec mccarthy n = 
  if n <= 100 then
    mccarthy (mccarthy (n + 11))
  else
    n - 10;;


let rec kmccarthy n k = 
  if n <= 100 then
    kmccarthy (fun res -> )
  else
    n - 10;;