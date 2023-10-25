open TreeProcessor
open TreeProcessor.User

val result = translate (Tree (Tree (Leaf 1,Mul,Leaf 2),Plus,Leaf 3))
val () = print (showResult result ^ "\n")