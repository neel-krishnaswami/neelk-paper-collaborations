(* assume a basic form of exceptions with an equality operation -- also
 * go in a separate module?  Other points -- we could support allocating
 * a "new" exception as in SML.  In fact, the issue of exceptions that
 * carry values (as a dynamic) are quite similar to "refs" versus 
 * naked locations... 
 *)
Parameter exn : Set.
Parameter eqexn : forall (x y:exn), {x=y} + {x<>y}.
