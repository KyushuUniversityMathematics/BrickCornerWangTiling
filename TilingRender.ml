open TilingProgram

let rec separate_list = function
	| [] -> [],[]
	| t::[] -> [t], []
	| t::t'::q -> let left, right = separate_list q in t::left, t'::right

let rec print_horizontal = function
	| [] -> ()
	| t::[] -> Printf.printf "^\n"
	| _::t::q -> (Printf.printf "^ :: %d :: " t ; print_horizontal q)

let rec print_vertical = function
	| [] -> ()
	| t::[] -> Printf.printf "%d\n" t
	| t::_::q -> (Printf.printf "%d :: ^ :: " t ; print_vertical q)

let rec print_lines = function
	| [] -> ()
	| t::[] -> print_horizontal t
	| t::t'::q -> (print_horizontal t ; print_vertical t' ; print_lines q)

let print_tiling n m boundary =
	print_lines (tiling_nm n m boundary)
	
let svg_header stream width height = 
	Printf.fprintf stream "<svg width=\"%d\" height=\"%d\">\n" width height

let svg_triangle stream =
	Printf.fprintf stream "\t<polygon points=\"%d,%d %d,%d %d,%d\" fill=\"%s\" stroke=\"%s\" stroke-width=\"%d\"/>\n"

let svg_footer stream = 
	Printf.fprintf stream "</svg>\n"

let svg_tiling colors size stroke_width stroke_color n m boundary filename = 
	let h = e_nm n m boundary
	and v = e'_nm n m boundary in

	let stream = open_out filename in

	let svg_tile i j = 
		let t = h j (i+1)
		and l = v (j+1) i
		and b = h (j+1) (i+1)
		and r = v (j+1) (i+1) in
		let x = i * size and y = j * size in
		let x' = x + size and y' = y + size 
		and cx = x + size / 2 and cy = y + size / 2 in
		svg_triangle stream x y cx cy x' y colors.(t) stroke_color stroke_width ;
		svg_triangle stream x y x y' cx cy colors.(l) stroke_color stroke_width ;
		svg_triangle stream x y' cx cy x' y' colors.(b) stroke_color stroke_width ;
		svg_triangle stream x' y' cx cy x' y colors.(r) stroke_color stroke_width 
	in

	let rec aux i j = match i,j with
		| 0, 0 -> svg_tile 0 0
		| 0, j -> (svg_tile 0 j ;  aux (n-1) (j-1))
		| i, j -> (svg_tile i j ; aux (i-1) j)
	in

	svg_header stream (n * size) (m * size);
	aux (n-1) (m-1);
	svg_footer stream;
	close_out stream


let colors = [| "#2C3E50" ; "#E74C3C" ; "#ECF06D" ; "#345BDB" ; "#2980B9" ; "#29995C" |]
let tile_size = 50
let stroke_width = 1
let stroke_color = "#000000"

let () = 
	let render = svg_tiling colors tile_size stroke_width stroke_color in
	render 2 2 boundary22a "b22a.svg";
	render 2 2 boundary22b "b22b.svg";
	render 2 2 boundary22c "b22c.svg";
	render 4 4 boundary44a "b44a.svg";
	render 4 4 boundary44b "b44b.svg";
	render 4 4 boundary44c "b44c.svg";
