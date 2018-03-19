open Common

exception NotImplemented

exception IllegalFormat

module Integer : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0
  let one = 1

  let (++) x y = x + y
  let ( ** ) x y = x * y
  let (==) x y = x = y 
end

(* Problem 1-1 *)
(* Scalars *)

module Boolean : SCALAR with type t = bool 
=
struct
  type t = bool

  exception ScalarIllegal

  let zero = false
  let one = true

  let (++) x y = if x=zero && y=zero then zero else one;;
  let ( ** ) x y = if x=one && y= one then one else zero ;;
  let (==) x y = if x= one && y= zero then zero else if x=zero && y= one then zero else one;;
end

(* Problem 1-2 *)
(* Vectors *)

module VectorFn (Scal : SCALAR) : VECTOR with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = elem list

  exception VectorIllegal

  let create (l  : elem list)=
    match l with
    |[]->raise VectorIllegal
    |head::tail-> l
  ;;
  let to_list (v:t) =
    match v with
    |[]->[]
    |head::tail-> v
  ;;
  let dim v = List.length v;;
  let nth v n =if n>= dim v || n<0 then raise VectorIllegal else List.nth v n;;
  let (++) v1 v2 = if dim v1 != dim v2 then raise VectorIllegal else
      let rec f v1 v2=
      match (v1, v2) with
	|([], [])-> []
	|(_, [])->[]
	|([], _)->[]
        |(head_1::tail_1, head_2::tail_2)-> (Scal.(++) head_1 head_2)::(f tail_1 tail_2)
	in f v1 v2
  ;;
  let (==) v1 v2 = if dim v1 != dim v2 then raise VectorIllegal else
      let rec f v1 v2=
	match (v1, v2) with
   |([],[])-> true
   |(_, [])->false
   |([], _)->false
   |(head_1::tail_1, head_2::tail_2)-> if Scal.(==) head_1 head_2 then f tail_1 tail_2 else false
      in f v1 v2
  ;;

  let innerp v1 v2 = if dim v1 != dim v2 then raise VectorIllegal else
      let rec f v1 v2 d=
	if d>0 then Scal.(++) (Scal.( ** ) (nth v1 (d-1)) (nth v2 (d-1))) (f v1 v2 (d-1)) else Scal.zero
      in f v1 v2 (dim v1)
  ;;
end

(* Problem 1-3 *)
(* Matrices *)

module MatrixFn (Scal : SCALAR) : MATRIX with type elem = Scal.t
=
struct
  type elem = Scal.t
  type t = VectorFn(Scal).t list

  module Vector= VectorFn(Scal)
  
  exception MatrixIllegal
  
  let create l =
    if l=[] then raise MatrixIllegal else
    let rec create_aux l=
    match l with
      |[]-> []
      |head::tail-> (Vector.create head)::(create_aux tail)
    in create_aux l
  ;;

  let identity n =
    if n<= 0 then raise MatrixIllegal else
    let rec iden_col n i c=
      let rec iden_row n j temp r=
	if n=temp then r else if temp=j then iden_row n j (temp+1) (Scal.one::r) else iden_row n j (temp+1) (Scal.zero::r)
      in if n=i then c else iden_col n (i+1) ((iden_row n i 0 [])::c)   
	in create (iden_col n 0 [])
  ;;

  let dim m = List.length m;;
  
  let get m r c =
    if (r< 0 || r>= dim m) || (c<0 || c>=dim m) then raise MatrixIllegal else
      (Vector.nth (List.nth m r) c)
  ;;

  let transpose m = 
    let rec transpose_aux m1 m2 temp d=
      let rec make_trans_row m1 r c d l=
	if r=d then l else make_trans_row m1 (r+1) c d (l@([get m1 r c]))
      in if temp=d then m2 else transpose_aux m1 (m2@([make_trans_row m1 0 temp d []])) (temp+1) d
	  
    in create (transpose_aux m [] 0 (dim m))
  ;;
  let to_list m=
    if m=[] then raise MatrixIllegal else
    let rec to_list_aux m=
      match m with
      |[]->[]
      |head::tail-> (Vector.to_list head)::(to_list_aux tail)
    in to_list_aux m
  ;;


  let (++) m1 m2 = 
    if (dim m1) != (dim m2) then raise MatrixIllegal else
      let rec f m1 m2=
	match (m1, m2) with
   	|([],[])->[]
   	|(_,[])->[]
   	|([], _)->[]
    	|(head_1::tail_1, head_2::tail_2)-> (Vector.(++) head_1 head_2)::(f tail_1 tail_2)
      in f m1 m2
  ;;
	
  let ( ** ) m1 m2 =
    if (dim m1) != (dim m2) then raise MatrixIllegal else
      let rec f m1 m2=
      match m1 with
   	|[]->[]
    |head::tail->
      let rec result_row r m2= 
  	match m2 with
     |[]->[]
     |head::tail-> (Vector.innerp r head)::(result_row r tail)
      in (result_row head m2)::(f tail m2)
	in create (f m1 (transpose m2))
  ;;

  let (==) m1 m2 =
	if (dim m1) != (dim m2) then raise MatrixIllegal else
   let rec f m1 m2=
   	match (m1, m2) with
  	|([], [])->true
   	|(_, [])-> false
   	|([], _)-> false
    |(head_1::tail_1, head_2::tail_2)-> if (Vector.(==) head_1 head_2) then f tail_1 tail_2 else false
   in f m1 m2
  ;;
end

(* Problem 2-1 *)
(* Closure *)

module ClosureFn (Mat : MATRIX) :
sig
  val closure : Mat.t -> Mat.t
end
=
struct
  let closure m =
    let rec closure_aux m result=
      if Mat.(==) (Mat.(++) (Mat.identity (Mat.dim m)) (Mat.( ** ) m result)) result then result 
      else closure_aux m (Mat.(++) (Mat.identity (Mat.dim m)) (Mat.( ** ) m result))
    in closure_aux m (Mat.identity (Mat.dim m))
  ;;
end

(* Problem 2-2 *)
(* Applications to Graph Problems *)

module BoolMat = MatrixFn (Boolean)
module BoolMatClosure = ClosureFn (BoolMat)

let reach m = if m=[] then raise IllegalFormat else BoolMat.to_list (BoolMatClosure.closure (BoolMat.create m));;

let al = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  false; false];
   [false; true;  true;  false; true;  false];
   [false; true;  false; true;  true;  true];
   [false; false; true;  true;  true;  false];
   [false; false; false; true;  false; true]]

let solution_al' = 
  [[true;  false; false; false; false; false];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true];
   [false; true;  true;  true;  true;  true]]

module Distance : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = -1              (* Dummy value : Rewrite it! *)
  let one = 0               (* Dummy value : Rewrite it! *)

  let (++) x y = if x=zero || y=zero then -(x*y) else (if x>y then y else x);;
  let ( ** ) x y = if x>=0 && y>=0 then (x+y) else zero;;
  let (==) x y = (x= y);; 
end

(* .. Write some code here .. *)

module DisMat= MatrixFn(Distance)
module DisClosure=ClosureFn(DisMat)

let distance m = if m=[] then raise IllegalFormat else DisMat.to_list (DisClosure.closure (DisMat.create m));;

let dl =
  [[  0;  -1;  -1;  -1;  -1;  -1 ];
   [ -1; 0  ; 35 ; 200; -1 ; -1  ];
   [ -1; 50 ; 0  ; -1 ; 150; -1  ];
   [ -1; 75;  -1 ; 0  ; 100; 25  ];
   [ -1; -1 ; 50 ; 65 ; 0  ; -1  ];
   [ -1; -1 ; -1 ; -1 ; -1 ; 0   ]]

let solution_dl' =
  [[0;  -1;  -1;  -1;  -1;  -1  ];
   [-1; 0;   35;  200; 185; 225 ];
   [-1; 50;  0;   215; 150; 240 ];
   [-1; 75;  110; 0;   100; 25  ];
   [-1; 100; 50;  65;  0;   90  ];
   [-1; -1;  -1;  -1;  -1;  0   ]]

module Weight : SCALAR with type t = int
=
struct
  type t = int

  exception ScalarIllegal

  let zero = 0              (* Dummy value : Rewrite it! *)
  let one = -1               (* Dummy value : Rewrite it! *)
 
  let (++) x y = if x=one || y=one then one else (if x>y then x else y) ;; 
  let ( ** ) x y = if x>=zero && y>= zero then (if x>y then y else x) else if x=one && y=one then one else (if x>y then x else y);; 
    let (==) x y = (x=y);;
end

(* .. Write some code here .. *)

module W_Mat= MatrixFn(Weight)
module W_Closure= ClosureFn(W_Mat)

let weight m = if m=[] then raise IllegalFormat else W_Mat.to_list (W_Closure.closure (W_Mat.create m));;

let ml =
  [[-1; 0  ; 0  ; 0  ; 0  ; 0   ];
   [0 ; -1 ; 10 ; 100; 0  ; 0   ];
   [0 ; 50 ; -1 ; 0  ; 150; 0   ];
   [0 ; 75 ; 0  ; -1 ; 125; 40 ];
   [0 ; 0  ; 25 ; -1 ; -1 ; 0   ];
   [0 ; 0  ; 0  ; 0  ; 0  ; -1  ]]

let solution_ml' =
  [[-1; 0;  0;   0;   0;   0  ];
   [0;  -1; 25;  100; 100; 40 ];
   [0;  75; -1;  150; 150; 40 ];
   [0;  75; 25;  -1;  125; 40 ];
   [0;  75; 25;  -1;  -1;  40 ];
   [0;  0;  0;   0;   0;   -1 ]]

let _ =
  try 
  if reach al = solution_al' && distance dl = solution_dl' && weight ml = solution_ml' then
    print_endline "\nYour program seems fine (but no guarantee)!"
  else
    print_endline "\nYour program might have bugs!"
  with _ -> print_endline "\nYour program is not complete yet!" 

