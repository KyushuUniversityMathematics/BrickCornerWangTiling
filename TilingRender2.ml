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

        let rec max_f f i = match i with
                | 0 -> f 0
                | 1 -> f 1
                | i -> max (f i) (max_f f (i-1))
        in

        let rec max_f2 f i j = match i, j with
                | 0, j -> max_f (f 0) j
		| 1, j -> max_f (f 1) j
                | i, j -> max (max_f (f i) j) (max_f2 f (i-1) j)
        in

	let hv_max = max (max_f2 h n m) (max_f2 v n m) in
	
	let stream = open_out filename in

	let svg_tile i j = 
		let t = h j (i+1)
		and l = v (j+1) i
		and b = h (j+1) (i+1)
		and r = v (j+1) (i+1) in
		let x = i * size and y = j * size in
		let x' = x + size and y' = y + size 
		and cx = x + size / 2 and cy = y + size / 2 in
		svg_triangle stream x y cx cy x' y (colors t hv_max) stroke_color stroke_width ;
		svg_triangle stream x y x y' cx cy (colors l hv_max) stroke_color stroke_width ;
		svg_triangle stream x y' cx cy x' y' (colors b hv_max) stroke_color stroke_width ;
		svg_triangle stream x' y' cx cy x' y (colors r hv_max) stroke_color stroke_width 
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


let red i c = max 0 (max (min 255 (3 * 255 - 6 * 255 * i / (c+1))) (3 * 255 * i / (c+1) - 2 * 255))
let green i c = max 0 (min 255 (min (3 * 255 * i / (c+1)) (5 * 255 / 2 - 3 * 255 * i / (c+1))))
let blue i c = max 0 (min 255 (min (6 * 255 * i / (c+1) - 3 * 255) (6 * 255 - 6 * 255 * i / (c+1))))
let string_of_0x n = match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 -> string_of_int n
    | 10 -> "A"
    | 11 -> "B"
    | 12 -> "C"
    | 13 -> "D"
    | 14 -> "E"
    | n -> "F"
let colors i c = "#" ^ (string_of_0x ((red i c) / 16)) ^ (string_of_0x ((red i c) mod 16)) ^ (string_of_0x ((green i c) / 16)) ^ (string_of_0x ((green i c) mod 16)) ^ (string_of_0x ((blue i c) / 16)) ^ (string_of_0x ((blue i c) mod 16))
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
