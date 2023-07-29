import Auto.Util.ExprExtra

set_option lazyReduce.printTime true
set_option maxRecDepth 50000 in
#lazyReduce List.map (fun n => (List.range (1000 + n)).length) (List.range 10)

set_option maxRecDepth 50000 in
#lazyReduce (List.range 10000).length