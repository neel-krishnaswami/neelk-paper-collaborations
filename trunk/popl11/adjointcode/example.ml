(* An ML function value *)

let succ n = n + 1

(* Here's a simple program that just returns 0 over and over... *)
let repeat = Dsl.run(do U(let g : S(V(D(int))) = omega(value(const 0)) in g))

(* The same thing, only using a fixed point *)

let const = Dsl.run(do U(let g : S(V(D(int))) -* S(V(D(int))) = fun xs -> omega(value(const 0))
                         in fix g))

(* Now, let's compute the increasing integers using a fixed point *)

let ints = Dsl.run (do U(let f : S(V(D(int))) -* S(V(D(int))) =
                           fun xs -> cons (const 0) (let omega(x) = xs in
                                                     omega(value((const succ) (start x))))
                         in
                         fix f))

(* Observe how we can pack and unpack a stream without chaning the the result *)

let rebuild = Dsl.run (do U(let f : S(V(D(int))) -* S(V(D(int))) =
                              fun xs -> cons (const 0) (let omega(x) = xs in
                                                        omega(value((const succ) (start x))))
                            in
                            let xs = fix f in
                            let omega(x) = xs in
                            omega(value(start x))
                         ))
(* Now, let's compute fibonaccis as a stream. Observe that we can write functions on 
   streams, and apply them to the results of fixed points. There are some transparent  
   coercions from ML pairs to U-pairs to make this more readable. 
*)

let step (a,b) = (b, a+b)

let fibs = Dsl.run (do U(let f : S(V(D(int * int))) -* S(V(D(int * int))) =
                           fun xs -> cons (const (1,1)) (let omega(x) = xs in
							 omega(value((const step) (start x))))
                         in
			 let map_fst : S(V(D(int * int))) -o S(V(D(int))) =
			   (fun pairs ->
			     let omega(pair) = pairs in
			     omega(value(fst (start pair))))
			 in
			 let pairs = fix f in
			 map_fst pairs))


(* Now, let's see a trivial use of higher order contractiveness. See that we
take the fixed point of the output of a higher-order function! *)

let ho_ints =
  Dsl.run(do U(let ccompose :  (S(V(D(int))) -* S(V(D(int)))) -o
                               (S(V(D(int))) -o S(V(D(int)))) -o
                               S(V(D(int))) -* S(V(D(int))) =
                 fun f g x -> f (g x)
               in
               let f : S(V(D(int))) -* S(V(D(int))) = cons (const 0) in
               let g : S(V(D(int))) -o S(V(D(int))) =
                 (fun xs ->
                   let omega(x) = xs in
		   omega(value((const succ) (start x))))
               in
	       let h = ccompose f g in
               fix h))

let ho_ints2 =
  Dsl.run(do U(let hofix : ((D(int) -o S(V(D(int)))) -* D(int) -o S(V(D(int)))) 
		           -o
		           D(int) -o S(V(D(int))) = inject Dsl.hofix
	       in
	       let iota : (D(int) -o S(V(D(int)))) -* D(int) -o S(V(D(int))) =
		 fun f n -> cons n (f ((const succ) n))
	       in
	       (hofix(iota)) (const 0)))
    

(* Now let's build a few simple GUIs.

   There's a monad of GUI commands, of type Gui(A). The return for the monad
   is written return(blah), and the monadic binding is written let gui(x) = e in e' 

   To run them, call Dsl.guirun <foo>_example
*)

(* This just makes gui with a label *)

let label_gui =
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in 
      label (omega (value (const "Hello world!"))));;

(* Now, let's combine the label with a timer. We construct a 
   a stream of integers, which counts up every tick of the clock. 

   So, we lift the ML string_of_int function to streams, and then
   create a timer, and pass its output converted to strings to the 
   label function. 
*)

let label_timer_gui =
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in
      let ints : S(V(D(int))) =
	fix(fun xs ->
	      cons
		(const 0)
		(let omega(x) = xs in
                 omega(value((const succ) (start x))))) in 
      let ints_to_strings : S(V(D(int))) -o S(V(D(string))) =
	fun ns ->
	  let omega(nval) = ns in
	  omega(value((const string_of_int) (start nval)))
      in 
      label (ints_to_strings ints))


(* This creates a button and a label, which changes depending on whether
   the mouse is down or up.
*)

let bool_to_string b = if b then "True!" else "False!"

let button_gui =
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in
      let button : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.button in
      let bools_to_strings : S(V(D(bool))) -o S(V(D(string))) =
	fun bools ->
	  let omega(bval) = bools in omega(value((const bool_to_string) (start bval)))
      in 
      let gui(downs) = button (omega (value (const "Press me"))) in
      label (bools_to_strings downs))


(* Next, let's look more seriously at the use of feedback.

   This gui below constructs a single button, whose label depends on
   whether or not the button is being clicked or not. It uses the
   guifix function, which is of type (omega(X) -* Gui(omega(X))) -o
   Gui(omega(X)), which is a "monadic recursion" operation.
   The idea is that we only want to perform the side effect (of
   constructing the user interface) once, but we want feedback of
   the *values*. 

   So we construct the function feedback, which takes an input stream
   of booleans, and yields a Gui boolean stream as output, and which 
   maps a bool-to-string function over its input stream to make its 
   labels.

   One interesting feature is that the False/True message is shifted 
   by one time step, since we use a unit delay. This is predictable 
   from the denotational semantics of feedback, *without* having to 
   look at the guts of the implementation. 
*)

let feedback_button_gui = 
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in
      let button : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.button in
      let guifix : (S(V(D(bool))) -* Gui(S(V(D(bool))))) -o Gui(S(V(D(bool)))) = inject Dsl.guifix
      in
      let clicks_to_strings : S(V(D(bool))) -o S(V(D(string))) =
	fun clicks ->
	  let omega(click) = clicks in omega(value((const bool_to_string) (start click)))
      in
      let feedback : S(V(D(bool))) -* Gui(S(V(D(bool)))) =
	fun clicks -> button (cons (const "Uninitialized") (clicks_to_strings clicks))
      in
      let gui(ignore) = guifix feedback in
      return (() : I))


(* Our buttons tell us whether the button is down or up. So we can
   combine them with timers to create labels that display increasing
   numbers as long as the button is held down.

   This is something needing further study -- this sort of looks
   noncompositional, since the creation of a timer value affects how
   often the event loop runs, which obviously affects how often other
   streams tick.
*)

let int_of_bool b = if b then 1 else 0 

let button_timer_gui = 
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in
      let button : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.button in
      let ints_to_strings : S(V(D(int))) -o S(V(D(string))) = 
	fun ns ->
	  let omega(nval) = ns in
	  omega(value((const string_of_int) (start nval)))
      in 
      let downs_to_counts : S(V(D(bools))) -o S(V(D(int))) =
	fun downs ->
	  let omega(dval) = downs in 
	  fix(fun ds ->
		cons (const 0) (let omega(dval2) = ds in 
				omega(value((const (fun b n -> if b then n+1 else n))
					      (start dval)
					      (start dval2)))))
      in 
      let gui(downs) = button (omega(value(const "Press me"))) in
      label(ints_to_strings (downs_to_counts downs)))

(* Now, since our buttons tell us whether the button is down or up,
   they do not directly report click events to us. So if we want
   clicks as events, rather than down/up status, we need to write a
   function to convert this status into a click stream. We can do this
   by keeping track of the previous state, and reporting a click
   whenever the button was down on the previous tick, and is up on the
   current tick.

   This is possibly the simplest example of a pervasive pattern in GUI
   programming, in which a state machine is used to synthesize
   high-level events from lower-level events.
*)

(* The state of our state machine, which is pair of booleans saying whether the 
   current and previous timesteps were down (true) or up (false) *)

type clickstate = bool * bool

(* The transition function. Given whether the button is down on the current
   step, and the previous state, it computes the current state. *)

let click_step : bool -> clickstate -> clickstate =
  fun t2 (t1, t0) -> (t2, t1)

(* Determining whether to generate a click event on the current state *)

let isclick : clickstate -> bool =
  fun (current, prev) -> not current && prev

(* The conversion of downs to clicks happens in three steps.

   1. First, we lift the state transition function click_step to work on streams.
   2. Next, we generate a stream of states from a stream of downs by taking an 
      initial state and using feedback to produce the next state from the initial
      state and the current down. 
   3. Finally, we map over the stream of states with the isclick function.

   Below, we give a small example in which we create a click button widget from our 
   existing button widget, and use it to create a label which is incremented every 
   time the button is clicked. We also run a timer, to show that other events happening
   don't interfere with the clickbutton.
*)   

let clickbutton_gui =
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in
      let button : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.button in
      let ints_to_strings : S(V(D(int))) -o S(V(D(string))) = 
	fun ns ->
	  let omega(nval) = ns in
	  omega(value((const string_of_int) (start nval)))
      in 
      let downs_to_clicks : S(V(D(bool))) -o S(V(D(bool))) =
	let lift_step : S(V(D(bool))) -o S(V(D(clickstate))) -o S(V(D(clickstate))) =
	  fun downs states ->
	    let omega(downval) = downs in
	    let omega(stateval) = states in
	    omega(value((const click_step) (start downval) (start stateval)))
	in
	let downs_to_states : S(V(D(bool))) -o S(V(D(clickstate))) =
	  fun downs -> fix (fun states -> cons (const (false, false)) (lift_step downs states))
	in
	fun downs ->
	  let omega(stateval) = downs_to_states downs in
	  omega(value((const isclick) (start stateval)))
      in 
      let clickbutton : S(V(D(string))) -o Gui(S(V(D(bool)))) =
	fun names ->
	  let gui(downs) = button names in
	  return(downs_to_clicks downs)
      in
      let count_clicks : S(V(D(bools))) -o S(V(D(int))) =
	fun clicks ->
	  let omega(clickval) = clicks in 
	  fix(fun counts ->
		cons (const 0) (let omega(countval) = counts in 
				omega(value((const (fun b n -> if b then n+1 else n))
					      (start clickval)
					      (start countval)))))
      in
      let gui(clicks) = clickbutton (omega(value(const "Click me!"))) in
      label (ints_to_strings (count_clicks clicks)))
      

(* Now, let's see how modular development of widgets might work. This
   is a toy example, but it should illustrate how working with
   first-class streams and functions can make GUI programming much
   easier.

   Our example will be of a button whose output can be enabled or
   disabled by a checkbox -- i.e., a button which will only deliver
   clicks if an associated checkbox is ticked.

   The heart of this is just the enable_button function, which has a
   very simple type, and whose implementation is just a few lines of
   straightline code. All the dependency management is abstracted
   away. 

   Note furthermore that the enable_button function is defined in 
   terms of the clickbutton function -- so layered, hierarchical 
   development of GUI abstractions is not just possible, but 
   is actually *easy*. 

   To illustrate this, we hook it up to a label, which displays
   whether the last event received was a click event or not.
*)

let bool_to_string b = if b then "True!" else "False!"
let guard b b' = b && b'

let enable_button_gui =
 do U(let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `LEFT in
      let button : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.button in
      let checkbox : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.checkbox 
      in
      let downs_to_clicks : S(V(D(bool))) -o S(V(D(bool))) =
	let lift_step : S(V(D(bool))) -o S(V(D(clickstate))) -o S(V(D(clickstate))) =
	  fun downs states ->
	    let omega(downval) = downs in
	    let omega(stateval) = states in
	    omega(value((const click_step) (start downval) (start stateval)))
	in
	let downs_to_states : S(V(D(bool))) -o S(V(D(clickstate))) =
	  fun downs -> fix (fun states -> cons (const (false, false)) (lift_step downs states))
	in
	fun downs ->
	  let omega(stateval) = downs_to_states downs in
	  omega(value((const isclick) (start stateval)))
      in 
      let clickbutton : S(V(D(string))) -o Gui(S(V(D(bool)))) =
	fun names ->
	  let gui(downs) = button names in
	  return(downs_to_clicks downs)
      in
      let clicks_to_strings : S(V(D(bool))) -o S(V(D(string))) =
	fun clicks ->
	  let omega(click) = clicks in omega(value((const bool_to_string) (start click)))
      in
      let enable_button : S(V(D(string))) -o Gui(S(V(D(bool)))) =
	fun labels -> 
	  let gui(ticks) = checkbox (omega (value (const "Enable?"))) in
	  let gui(clicks) = clickbutton labels in
	  let omega(tick) = ticks in
	  let omega(click) = clicks in
	  return(omega(value((const guard) (start tick) (start click))))
      in
      let gui(results) = enable_button (omega (value (const "Try me out!"))) in
      label(clicks_to_strings results))
		 

(* Now, a simple calculator application *)

(* First, we'll give the state machine for the calculator. This is a simple 4-function
   calculator, so our state will be a pair, consisting of the current number being
   input-ed, and a register containing the operation and number to apply it to (if
   it is defined). 
*)

type op = int -> int -> int 
type state =
  | Lentry of int * op * int
  | Rentry of int * op * int
  | Noentry of int * op * int
  | Continue of int * op

let init_state = Rentry(0, (+), 0)

(* Next, we'll define the event type, which correspond to the *)

type event = Digit of int | Op of op | Equals | Clear | Nothing

let merge e1 e2 =
  match e1, e2 with
  | Nothing, _ -> e2
  | _ -> e1

(* The transition relation for the calculator. The behavior of a
   simple 4-function calculator is surprisingly irregular, and
   illustrates why it's a good idea to put it all in one place, where
   it can be looked at without the interference of GUI code or
   callbacks to complicate matters.

   In functional programming, it's common to code up state machines as
   sets of mutually-recursive functions. A good question to look at is
   the relationship between these explicit state machines and the
   implicit state machines.

   One surprising aspect of our work is the absence of continuations,
   which prior work on functional GUIs and event loops stressed a lot.
   I suspect that if find a way of writing these state machines as
   recursive functions, we'll need some kind of CPS to be able to to
   break the iteration at each time step and get the right coroutine
   behavior. (This idea is also reminiscent of loops in Esterel.)
*)

let step event state =
  match event, state with
  | Digit n, Rentry(a, op, b)  -> Rentry(a, op, 10*b + n)
  | Equals,  Rentry(a, op, b)  -> Noentry(op a b, op, b)
  | Op op',  Rentry(a, op, b)  -> Continue(op a b, op')
  | Digit n, Noentry(a, op, b) -> Lentry(n, op, b)
  | Equals,  Noentry(a, op, b) -> Noentry(op a b, op, b)
  | Op op',  Noentry(a, op, b) -> Continue(a, op')
  | Digit n, Lentry(a, op, b)  -> Lentry(10*a + n, op, b)
  | Equals,  Lentry(a, op, b)  -> Noentry(op a b, op, b)
  | Op op',  Lentry(a, op, b)  -> Continue(op a b, op')
  | Digit n, Continue(a, op)   -> Rentry(a, op, n)
  | Equals,  Continue(a, op)   -> Noentry(op a a, op, a)
  | Op op',  Continue(a, op)   -> Continue(a, op')
  | Clear,   state             -> init_state
  | Nothing, state             -> state


let display : state -> string = function
   | Continue(n, _)
   | Noentry(n, _, _)
   | Rentry(_, _, n) 
   | Lentry(n, _, _) -> string_of_int n

let div a b = if b = 0 then 0 else a / b
   
let calculator_gui =
 do U(let hstack : Gui(S((V(D(event))))) -o Gui(S(V(D(event)))) =
	inject (Dsl.stack `HORIZONTAL `START `HOMOGENEOUS `EXPAND) in
      let lhstack : Gui(I) -o Gui(I) =
	inject (Dsl.stack `HORIZONTAL `FINISH `INHOMOGENEOUS `NOEXPAND) in
      let vstack : Gui(I) -o Gui(I) = inject (Dsl.stack `VERTICAL `FINISH `HOMOGENEOUS `EXPAND) in
      let label : S(V(D(string))) -o Gui(I) = inject Dsl.label `RIGHT in
      let button : S(V(D(string))) -o Gui(S(V(D(bool)))) = inject Dsl.button 
      in
      (* First, we construct the clickbuttons, as above *)
      let downs_to_clicks : S(V(D(bool))) -o S(V(D(bool))) =
	let lift_step : S(V(D(bool))) -o S(V(D(clickstate))) -o S(V(D(clickstate))) =
	  fun downs states ->
	    let omega(downval) = downs in
	    let omega(stateval) = states in
	    omega(value((const click_step) (start downval) (start stateval)))
	in
	let downs_to_states : S(V(D(bool))) -o S(V(D(clickstate))) =
	  fun downs -> fix (fun states -> cons (const (false, false)) (lift_step downs states))
	in
	fun downs ->
	  let omega(stateval) = downs_to_states downs in
	  omega(value((const isclick) (start stateval)))
      in 
      let clickbutton : S(V(D(string))) -o Gui(S(V(D(bool)))) =
	fun names ->
	  let gui(downs) = button names in
	  return(downs_to_clicks downs)
      in
      (*
	Next, we lift the transition function to act on streams
      *)
      let transitions : S(V(D(event))) -o S(V(D(state))) -o S(V(D(state))) =
	fun es ss ->
	  let omega(eval) = es in
	  let omega(sval) = ss in
	  omega(value((const step) (start eval) (start sval)))
      in
      (*
	Next, we take in a stream of inputs, and use an initial state plus 
	feedback to compute a stream of states from a stream of inputs
      *)
      let states : S(V(D(event))) -o S(V(D(state))) =
	fun es ->
	  fix (fun ss -> cons (const init_state) (transitions es ss))
      in
      (*
	Now, our buttons will produce clicks, which we need to convert to 
	events. We take in streams of events, and streams of clicks, and
	return the input event if the click value is true, and the Nothing
	event otherwise
      *)
      let events_of_bools : S(V(D(event))) -o S(V(D(bool))) -o S(V(D(event))) =
	fun events clicks ->
	  let omega(e) = events in
	  let omega(c) = clicks in
	  omega(value((const (fun e' c' -> if c' then e' else Nothing)) (start e) (start c)))
      in
      (*
	We'll have 16 buttons, and we only want one stream of events, so we'll
	multiplex the event streams produced by the buttons. This function does
	that. 
      *)
      let map_merge : S(V(D(event))) -o S(V(D(events))) -o S(V(D(event))) =
	fun es1 es2 ->
	  let omega(e1) = es1 in
	  let omega(e2) = es2 in 
	  omega(value((const merge) (start e1) (start e2)))
      in
      (*
	As a convenience, we take a stream of desired events and labels, and an 
	input stream of events, produce a button which yields the multiplexed 
	output stream. If we had polymorphism and more types available, we could
	abstract over this state-passing as well.
      *)
      let cbutton : S(V(D(event))) -o S(V(D(string))) -o S(V(D(event))) -o Gui(S(V(D(event)))) =
	fun es names erest -> 
	  let gui(clicks) = clickbutton(names) in
	  return (map_merge erest (events_of_bools es clicks))
      in
      (*
	Next, we construct a widget which builds a whole row of the calculator.
	Adding support for lists would make the type signature a little nicer, but
	since this is just a prototype I've left it out. Note that we're just 
	compositionally building the GUI, introducing auxilliary widget definitions
	as easily as writing a function. 
      *)
      let button_row : S(V(D(string))) -o S(V(D(event))) -o 
	               S(V(D(string))) -o S(V(D(event))) -o 
	               S(V(D(string))) -o S(V(D(event))) -o 
	               S(V(D(string))) -o S(V(D(event))) -o 
		       S(V(D(event))) -o Gui(S(V(D(event)))) =
	fun n1 e1 n2 e2 n3 e3 n4 e4 es -> 
	  hstack(let gui(es) = cbutton e1 n1 es in 
		 let gui(es) = cbutton e2 n2 es in 
		 let gui(es) = cbutton e3 n3 es in
	         cbutton e4 n4 es)
      in
      (* Now we can finally lay out the whole calculator GUI, using
	 the horizontal and vertical stacking functions -- they are
	 just functions which take GUI expressions and return GUI
	 expressions.  The nice thing is that the layout of the code
	 is pretty much the same as the layout of the GUI -- so we
	 retain advantages of HTML-style markup, while still building
	 an interactive application.  *)
      let es : S((V(D(event)))) = omega(value(const Nothing)) in
      vstack (let gui(es) =
		button_row
		  (omega(value(const "C"))) (omega(value(const Clear))) 
		  (omega(value(const "0"))) (omega(value(const (Digit 0)))) 
	          (omega(value(const "="))) (omega(value(const Equals))) 
	          (omega(value(const "/"))) (omega(value(const (Op div))))
		  es
	      in
	      let gui(es) = 
		button_row
		  (omega(value(const "1"))) (omega(value(const (Digit 1))))
		  (omega(value(const "2"))) (omega(value(const (Digit 2))))
		  (omega(value(const "3"))) (omega(value(const (Digit 3))))
	          (omega(value(const "X"))) (omega(value(const (Op ( * )))))
		  es
	      in
	      let gui(es) =
		button_row 
		  (omega(value(const "4"))) (omega(value(const (Digit 4))))  
		  (omega(value(const "5"))) (omega(value(const (Digit 5))))  
		  (omega(value(const "6"))) (omega(value(const (Digit 6)))) 
		  (omega(value(const "-"))) (omega(value(const (Op ( - )))))
		  es 	
	      in
	      let gui(es) =
		button_row
		  (omega(value(const "7"))) (omega(value(const (Digit 7))))  
		  (omega(value(const "8"))) (omega(value(const (Digit 8))))  
		  (omega(value(const "9"))) (omega(value(const (Digit 9)))) 
	          (omega(value(const "+"))) (omega(value(const (Op ( + )))))
		  es
	      in
	      let omega(sval) = states es in
	      lhstack(label (omega(value((const display) (start sval)))))))
		       


	  
