type op = int -> int -> int 
type state = int * (op * int) option
type event = Digit of Int | Op of op | Equals | Clear | Nothing

let eval : state -> int = function
  | (n, None) -> n
  | (n, (op, m)) -> op m n

let step : event -> state -> state =
  fun e ((current, reg) as s) ->
    match e with
    | Digit n -> (10 * current + n, reg)
    | Nothing -> s
    | Clear -> (0, reg)
    | Equals -> (eval s, None)
    | Op op -> (0, Some(op, eval s))

	
