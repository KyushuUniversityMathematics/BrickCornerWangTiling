type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type reflect =
| ReflectT
| ReflectF

(** val iffP : bool -> reflect -> reflect **)

let iffP b pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality = 
 struct 
  type 't axiom = 't -> 't -> reflect
  
  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }
  
  (** val mixin_of_rect :
      ('a1 rel -> 'a1 axiom -> 'a2) -> 'a1 mixin_of -> 'a2 **)
  
  let mixin_of_rect f m =
    let { op = x; mixin_of__1 = x0 } = m in f x x0
  
  (** val mixin_of_rec :
      ('a1 rel -> 'a1 axiom -> 'a2) -> 'a1 mixin_of -> 'a2 **)
  
  let mixin_of_rec f m =
    let { op = x; mixin_of__1 = x0 } = m in f x x0
  
  (** val op : 'a1 mixin_of -> 'a1 rel **)
  
  let op x = x.op
  
  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)
  
  (** val type_rect : (__ -> __ mixin_of -> __ -> 'a1) -> coq_type -> 'a1 **)
  
  let type_rect f t =
    f __ t __
  
  (** val type_rec : (__ -> __ mixin_of -> __ -> 'a1) -> coq_type -> 'a1 **)
  
  let type_rec f t =
    f __ t __
  
  type sort = __
  
  (** val coq_class : coq_type -> sort mixin_of **)
  
  let coq_class cT =
    cT
  
  (** val pack : 'a1 mixin_of -> coq_type **)
  
  let pack c =
    Obj.magic c
  
  (** val clone : coq_type -> 'a1 mixin_of -> (sort -> 'a1) -> coq_type **)
  
  let clone cT c x =
    pack c
  
  module Exports = 
   struct 
    
   end
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t =
  (Equality.coq_class t).Equality.op

(** val eqn : int -> int -> bool **)

let rec eqn m n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      true)
      (fun n0 ->
      false)
      n)
    (fun m' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      false)
      (fun n' ->
      eqn m' n')
      n)
    m

(** val eqnP : int Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : int Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val c_other2 : int -> int **)

let c_other2 c0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Pervasives.succ
    0)
    (fun n ->
    0)
    c0

(** val c_other3 : int -> int -> int **)

let c_other3 c0 c1 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ
      0)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Pervasives.succ (Pervasives.succ
        0))
        (fun n0 -> Pervasives.succ
        0)
        n)
      c1)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Pervasives.succ (Pervasives.succ
        0))
        (fun n0 ->
        0)
        c1)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Pervasives.succ
        0)
        (fun n1 ->
        0)
        c1)
      n)
    c0

type boundary = int -> int -> int

type edge = int -> int -> int

(** val null : 'a1 -> 'a1 **)

let null x =
  x

(** val e_i : int -> edge -> int -> int list **)

let rec e_i j e i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (null 0) :: [])
    (fun j' ->
    app (e_i j' e i) ((e i (Pervasives.succ j')) :: ((null 0) :: [])))
    j

(** val e'_i : int -> edge -> int -> int list **)

let rec e'_i j e' i =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (e' i 0) :: [])
    (fun j' ->
    app (e'_i j' e' i)
      ((null (Pervasives.succ 0)) :: ((e' i (Pervasives.succ j')) :: [])))
    j

(** val e_e' : int -> int -> edge -> edge -> int list list **)

let rec e_e' n m e e' =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (e_i m e 0) :: [])
    (fun n' ->
    app (e_e' n' m e e')
      ((e'_i m e' (Pervasives.succ n')) :: ((e_i m e (Pervasives.succ n')) :: [])))
    n

(** val tiling :
    int -> int -> boundary -> (boundary -> edge) -> (boundary -> edge) -> int
    list list **)

let tiling n m b e_ e'_ =
  e_e' n m (e_ b) (e'_ b)

(** val e_12 : boundary -> edge **)

let e_12 b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    b 0 j)
    (fun n ->
    b (Pervasives.succ (Pervasives.succ 0)) j)
    i

(** val e'_12 : boundary -> edge **)

let e'_12 b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    b (Pervasives.succ 0) 0)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      if eq_op nat_eqType (Obj.magic b (Pervasives.succ 0) 0)
           (Obj.magic b (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0))))
      then if eq_op nat_eqType (Obj.magic b 0 (Pervasives.succ 0))
                (Obj.magic b (Pervasives.succ (Pervasives.succ 0))
                  (Pervasives.succ 0))
           then c_other2 (b (Pervasives.succ 0) 0)
           else b (Pervasives.succ 0) 0
      else if eq_op nat_eqType (Obj.magic b 0 (Pervasives.succ 0))
                (Obj.magic b (Pervasives.succ (Pervasives.succ 0))
                  (Pervasives.succ 0))
           then if eq_op nat_eqType
                     (Obj.magic b 0 (Pervasives.succ (Pervasives.succ 0)))
                     (Obj.magic b (Pervasives.succ (Pervasives.succ 0))
                       (Pervasives.succ (Pervasives.succ 0)))
                then c_other3 (b (Pervasives.succ 0) 0)
                       (b (Pervasives.succ 0) (Pervasives.succ
                         (Pervasives.succ (Pervasives.succ 0))))
                else b (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ 0)))
           else b (Pervasives.succ 0) 0)
      (fun n0 ->
      b (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ
        (Pervasives.succ 0))))
      n)
    j

(** val e_22 : boundary -> edge **)

let e_22 b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    b 0 j)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      if eq_op nat_eqType (Obj.magic b (Pervasives.succ 0) 0)
           (Obj.magic b (Pervasives.succ 0) (Pervasives.succ (Pervasives.succ
             (Pervasives.succ 0))))
      then if eq_op nat_eqType
                (Obj.magic b (Pervasives.succ (Pervasives.succ 0)) 0)
                (Obj.magic b (Pervasives.succ (Pervasives.succ 0))
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
           then c_other3 (b 0 j)
                  (b (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))
                    j)
           else if eq_op nat_eqType (Obj.magic b 0 (Pervasives.succ 0))
                     (Obj.magic b (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ 0))) (Pervasives.succ 0))
                then b 0 j
                else if eq_op nat_eqType
                          (Obj.magic b 0 (Pervasives.succ (Pervasives.succ
                            0)))
                          (Obj.magic b (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ 0))) (Pervasives.succ
                            (Pervasives.succ 0)))
                     then ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                             (fun _ ->
                             b (Pervasives.succ (Pervasives.succ
                               (Pervasives.succ 0))) (Pervasives.succ 0))
                             (fun n0 ->
                             (fun fO fS n -> if n=0 then fO () else fS (n-1))
                               (fun _ ->
                               b (Pervasives.succ (Pervasives.succ
                                 (Pervasives.succ 0))) (Pervasives.succ 0))
                               (fun n1 ->
                               c_other2 (b 0 j))
                               n0)
                             j)
                     else b (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ 0))) j
      else if eq_op nat_eqType
                (Obj.magic b (Pervasives.succ (Pervasives.succ 0)) 0)
                (Obj.magic b (Pervasives.succ (Pervasives.succ 0))
                  (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))))
           then if eq_op nat_eqType (Obj.magic b 0 (Pervasives.succ 0))
                     (Obj.magic b (Pervasives.succ (Pervasives.succ
                       (Pervasives.succ 0))) (Pervasives.succ 0))
                then b (Pervasives.succ (Pervasives.succ (Pervasives.succ
                       0))) j
                else if eq_op nat_eqType
                          (Obj.magic b 0 (Pervasives.succ (Pervasives.succ
                            0)))
                          (Obj.magic b (Pervasives.succ (Pervasives.succ
                            (Pervasives.succ 0))) (Pervasives.succ
                            (Pervasives.succ 0)))
                     then ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                             (fun _ ->
                             b 0 (Pervasives.succ 0))
                             (fun n0 ->
                             (fun fO fS n -> if n=0 then fO () else fS (n-1))
                               (fun _ ->
                               b 0 (Pervasives.succ 0))
                               (fun n1 ->
                               c_other2
                                 (b (Pervasives.succ (Pervasives.succ
                                   (Pervasives.succ 0))) j))
                               n0)
                             j)
                     else b 0 j
           else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                   (fun _ ->
                   b 0 (Pervasives.succ 0))
                   (fun n0 ->
                   (fun fO fS n -> if n=0 then fO () else fS (n-1))
                     (fun _ ->
                     b 0 (Pervasives.succ 0))
                     (fun n1 ->
                     b (Pervasives.succ (Pervasives.succ (Pervasives.succ
                       0))) (Pervasives.succ (Pervasives.succ 0)))
                     n0)
                   j))
      (fun n0 ->
      b (Pervasives.succ (Pervasives.succ (Pervasives.succ 0))) j)
      n)
    i

(** val e'_22 : boundary -> edge **)

let e'_22 b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    0)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      e'_12 (fun i0 j0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          b 0 j0)
          (fun n0 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            b (Pervasives.succ 0) j0)
            (fun n1 ->
            e_22 b (Pervasives.succ 0) j0)
            n0)
          i0) (Pervasives.succ 0) j)
      (fun n0 ->
      e'_12 (fun i0 j0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          e_22 b (Pervasives.succ 0) j0)
          (fun n1 ->
          b (Pervasives.succ i0) j0)
          i0) (Pervasives.succ 0) j)
      n)
    i

(** val bSnm_to_bnm : int -> boundary -> boundary **)

let bSnm_to_bnm m b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    b i j)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      b i j)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          0)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            b 0 (Pervasives.succ 0))
            (fun n2 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              b 0 (Pervasives.succ (Pervasives.succ 0)))
              (fun n3 ->
              c_other2 (b 0 j))
              n2)
            n1)
          j)
        (fun n1 ->
        b (Pervasives.succ i) j)
        i)
      n)
    m

(** val bSnm_to_b1m : int -> boundary -> boundary **)

let bSnm_to_b1m m b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    b i j)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      b i j)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        b 0 j)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          b (Pervasives.succ 0) j)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            0)
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              b 0 (Pervasives.succ 0))
              (fun n4 ->
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ ->
                b 0 (Pervasives.succ (Pervasives.succ 0)))
                (fun n5 ->
                c_other2 (b 0 j))
                n4)
              n3)
            j)
          n1)
        i)
      n)
    m

(** val e_1m : boundary -> edge **)

let e_1m b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    b 0 j)
    (fun n ->
    b (Pervasives.succ (Pervasives.succ 0)) j)
    i

(** val e'_1m : int -> boundary -> edge **)

let e'_1m m b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    0)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      b (Pervasives.succ 0) 0)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        c_other3 (b (Pervasives.succ 0) 0)
          (b (Pervasives.succ 0) (Pervasives.succ m)))
        (fun n1 ->
        b (Pervasives.succ 0) (Pervasives.succ m))
        n0)
      j)
    i

(** val e_n2 : int -> boundary -> edge **)

let rec e_n2 n b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    e_12 b)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      e_12 b)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        e_22 b)
        (fun n1 i j ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          bSnm_to_b1m (Pervasives.succ (Pervasives.succ 0)) b 0 j)
          (fun i' ->
          e_n2 n' (bSnm_to_bnm (Pervasives.succ (Pervasives.succ 0)) b) i' j)
          i)
        n0)
      n')
    n

(** val e'_n2 : int -> boundary -> edge **)

let rec e'_n2 n b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    e'_12 b)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      e'_12 b)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        e'_22 b)
        (fun n1 i j ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          0)
          (fun i' ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            e'_1m (Pervasives.succ (Pervasives.succ 0))
              (bSnm_to_b1m (Pervasives.succ (Pervasives.succ 0)) b)
              (Pervasives.succ 0) j)
            (fun n2 ->
            e'_n2 n' (bSnm_to_bnm (Pervasives.succ (Pervasives.succ 0)) b) i'
              j)
            i')
          i)
        n0)
      n')
    n

(** val bnm_to_bmn : boundary -> boundary **)

let bnm_to_bmn b i j =
  b j i

(** val enm_to_emn : (boundary -> edge) -> boundary -> edge **)

let enm_to_emn e b i j =
  e (bnm_to_bmn b) j i

(** val e_nm : int -> int -> boundary -> edge **)

let rec e_nm n m b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    e_1m b)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      e_1m b)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        enm_to_emn (fun b' -> e'_n2 m b') b)
        (fun n1 i j ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          bSnm_to_b1m m b 0 j)
          (fun i' ->
          e_nm n' m (bSnm_to_bnm m b) i' j)
          i)
        n0)
      n')
    n

(** val e'_nm : int -> int -> boundary -> edge **)

let rec e'_nm n m b =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    e'_1m m b)
    (fun n' ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      e'_1m m b)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        enm_to_emn (fun b' -> e_n2 m b') b)
        (fun n1 i j ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          0)
          (fun i' ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            e'_1m m (bSnm_to_b1m m b) (Pervasives.succ 0) j)
            (fun n2 ->
            e'_nm n' m (bSnm_to_bnm m b) i' j)
            i')
          i)
        n0)
      n')
    n

(** val tiling_nm : int -> int -> boundary -> int list list **)

let tiling_nm n m b =
  tiling n m b (e_nm n m) (e'_nm n m)

(** val boundary22a : int -> int -> int **)

let boundary22a i j =
  0

(** val boundary22b : int -> int -> int **)

let boundary22b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Pervasives.succ (Pervasives.succ
    0))
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      0)
      (fun n0 -> Pervasives.succ
      0)
      j)
    i

(** val boundary22c : int -> int -> int **)

let boundary22c i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ
      0)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        0)
        (fun n0 -> Pervasives.succ
        0)
        n)
      i)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ (Pervasives.succ
      0))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ
          0)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            0)
            (fun n2 -> Pervasives.succ
            0)
            n1)
          i)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ
          0)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Pervasives.succ
            0)
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ ->
              0)
              (fun n4 -> Pervasives.succ
              0)
              n3)
            i)
          n1)
        n0)
      n)
    j

(** val boundary44a : int -> int -> int **)

let boundary44a i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Pervasives.succ (Pervasives.succ
    0))
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        0))))
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))
          (fun n1 -> Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ
          0))))
          n0)
        j)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ
          0))))
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            0)))
            (fun n2 -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ
            0))))
            n1)
          j)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ
            0)))))
            (fun n2 -> Pervasives.succ
            0)
            j)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ
            0))))
            (fun n3 ->
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
              0)))
              (fun n4 -> Pervasives.succ (Pervasives.succ (Pervasives.succ
              (Pervasives.succ
              0))))
              n3)
            j)
          n1)
        n0)
      n)
    i

(** val boundary44b : int -> int -> int **)

let boundary44b i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
      (Pervasives.succ
      0))))
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
        (Pervasives.succ
        0))))
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            0)))
            (fun n2 -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ
            0))))
            n1)
          n0)
        n)
      i)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ (Pervasives.succ
      0))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          0)
          (fun n1 -> Pervasives.succ (Pervasives.succ (Pervasives.succ
          (Pervasives.succ (Pervasives.succ
          0)))))
          i)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ
          0)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            0)
            (fun n3 -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            (Pervasives.succ (Pervasives.succ
            0)))))
            i)
          n1)
        n0)
      n)
    j

(** val boundary44c : int -> int -> int **)

let boundary44c i j =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ (Pervasives.succ
      0))
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Pervasives.succ (Pervasives.succ
        0))
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
          0)))
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> Pervasives.succ (Pervasives.succ (Pervasives.succ
            0)))
            (fun n2 -> Pervasives.succ (Pervasives.succ
            0))
            n1)
          n0)
        n)
      i)
    (fun n ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Pervasives.succ (Pervasives.succ
      0))
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ ->
          0)
          (fun n1 -> Pervasives.succ
          0)
          i)
        (fun n1 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Pervasives.succ
          0)
          (fun n2 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ ->
            0)
            (fun n3 -> Pervasives.succ
            0)
            i)
          n1)
        n0)
      n)
    j

