/* Override the effect declaration in the standard library. */
val print_endline = monadic "print_endline_monadic" : string -> unit
