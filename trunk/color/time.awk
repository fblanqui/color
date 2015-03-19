{if($2>10)print}
{tot+=$2;n++}
END{printf"files: %d, time: %ds, mean: %.2fs\n",n,tot,tot/n}