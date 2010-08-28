let time =
  let start = Unix.gettimeofday () in
  (fun () -> Unix.gettimeofday () -. start)

let delete_event ev =
  print_endline "Delete event occurred";
  flush stdout;
  false (* false = quit *)

let destroy () = print_endline "destroy"; GMain.Main.quit ()

let locale = GtkMain.Main.init ()


module type IMAGE =
sig 
  type point = unit -> unit
  type color = Gl.rgba
  type colorpoint = color -> point -> point
  type image = unit -> unit

  val neg : float -> float

  val point      : Gl.point2 -> point
  val colorpoint : Gl.rgba -> point -> point
  val projection : x:(float * float) -> y:(float * float) -> unit
  val rotate     : angle:float -> image -> image
  val translate  : x:float -> y:float -> image -> image 
  val scale      : x:float -> y:float -> image -> image 
  val join       : image list -> image

  val triangles   : (point * point * point) list -> image
(*
  val lines       : (point * point) list -> image
  val lines_strip : point list -> image
  val quads       : (point * point * point * point) list -> image
*)
  val lineloop    : point list -> image
  val polygon     : point list -> image
end

module Image : IMAGE =
struct
  type point = unit -> unit
  type color = Gl.rgba
  type colorpoint = color -> point -> point 
  type image = unit -> unit 

  let point(x,y) : point = fun () -> GlDraw.vertex2 (x,y)

  let colorpoint col pt : point =
    fun () -> (let (r,g,b,a) = col in
	       GlDraw.color ~alpha:a (r,g,b);
	       pt())
  
  let neg x = 0.0 -. x
  
  let projection ~x ~y =
    begin
      GlMat.mode `projection;
      GlMat.load_identity ();
      GlMat.ortho ~x ~y ~z:(1.0,-1.0);
    end

  let rotate ~angle thunk () =
    begin
      GlMat.mode `modelview;
      GlMat.push();
      GlMat.rotate ~angle:angle ~x:0.0 ~y:0.0 ~z:1.0 ();
      thunk();
      GlMat.pop();
    end

  let triangles ps () =
    begin
      GlDraw.begins `triangles;
      List.iter (fun (p1,p2,p3) -> (p1(); p2(); p3())) ps;
      GlDraw.ends()
    end

  let translate ~x ~y thunk () =
    begin
      GlMat.mode `modelview;
      GlMat.push();
      GlMat.translate ~x:x ~y:y ~z:0.0 ();
      thunk();
      GlMat.pop();
    end

  let scale ~x ~y thunk () =
    begin
      GlMat.mode `modelview;
      GlMat.push();
      GlMat.scale ~x ~y ~z:1.0 ();
      GlMat.pop();
    end

  let lineloop ps () =
    begin
      GlDraw.begins `line_loop;
      List.iter (fun thunk -> thunk()) ps;
      GlDraw.ends()
    end
    
  let polygon ps () =
    begin
      GlDraw.begins `polygon;
      List.iter (fun thunk -> thunk()) ps;
      GlDraw.ends()
    end
    

  let join images () =
    begin
      GlMat.mode `modelview;
      GlMat.push();
      List.iter (fun t -> t()) images;
      GlMat.pop();
    end
end

let my_opengl_reshape ar ~width ~height =
  print_endline "my_opengl_reshape called";
  ar#make_current ();
  GlDraw.viewport 0 0 width height;
  GlMat.mode `projection;
  GlMat.load_identity ();
  GlMat.ortho (0.0, float_of_int width) (float_of_int height, 0.0) (-1.0, 0.0)

let my_opengl_init ar () =
  begin
    print_endline "my_opengl_init called";
    ar#make_current ();
    GlDraw.shade_model `smooth;
    GlClear.color (1.0, 1.0, 1.0);
    Gl.disable `depth_test;
    List.iter Gl.enable [`alpha_test; `alpha_test; `line_smooth;
			 `polygon_smooth; `point_smooth; `blend];
    GlFunc.blend_func ~src:`src_alpha ~dst:`one_minus_src_alpha;
    GlFunc.alpha_func `greater 0.0 
  end

let rotated_triangle angle =
  let r = (1.0, 0.0, 0.0, 0.5) in
  let g = (0.0, 1.0, 0.0, 0.5) in 
  let b = (0.0, 0.0, 1.0, 0.5) in
  let radian = 2.0 *. 3.14159 *. angle /. 360.0 in 
  let triangle c1 c2 c3 =
    Image.triangles [Image.colorpoint c1 (Image.point ((-1.732 /. 2.0), -0.5)),
		     Image.colorpoint c2 (Image.point (0.0, 1.0)),
		     Image.colorpoint c3 (Image.point ((1.732 /. 2.0), -0.5))] in 
  let t1 = triangle r g b in
  let t2 = Image.translate ~x:(sin radian) ~y:(sin radian) (Image.rotate ~angle:180.0 (triangle b r g)) in
  let t3 = Image.rotate ~angle:angle (Image.translate ~x:2.0 ~y:0.0 (triangle g b r)) in
  Image.rotate ~angle:0.0 (Image.join [t1; t2; t3])
  
let my_opengl_display ar () =
  ar#make_current ();
  GlClear.clear [ `color ];
  Image.projection ~x:(-3.0, 3.0) ~y:(-3.0, 3.0);
  rotated_triangle (time () *. 90.0) ();
  Gl.flush ();
  ar#swap_buffers ()

let _ =
  let window = GWindow.window () in 
  let _ = window#event#connect#delete ~callback:delete_event in 
  let _ = window#connect#destroy ~callback:destroy in 
  let ar = GlGtk.area [`USE_GL; `RGBA; `DOUBLEBUFFER] ~packing:window#add
	   ~show:true ()
  in 
  let _ = ar#connect#reshape ~callback:(my_opengl_reshape ar) in
  let _ = ar#connect#realize ~callback:(my_opengl_init ar) in
  let _ = ar#connect#display ~callback:(my_opengl_display ar) in
  let _ = GMain.Timeout.add ~ms:5 ~callback:(fun () -> my_opengl_display ar (); true) in 
  window#show ();
  GMain.Main.main ()
