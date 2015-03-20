{if($2>10){subtotal+=$2;subnb++;print}}
{total+=$2;nb++;if($2>maxval){maxval=$2;maxfile=$1}}
END{printf"files: %d, time: %ds, mean: %.2fs, max: %.2fs (%s)\nfiles>10s: %d (%d%%), time: %ds (%d%%)\n",nb,total,total/nb,maxval,maxfile,subnb,100*subnb/nb,subtotal,100*subtotal/total}