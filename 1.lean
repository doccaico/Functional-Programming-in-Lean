def main : IO Unit :=
  IO.println s!"Hello, world!"

#eval main

#eval String.append "a" "b"

def add1 (n : Nat) : Nat := n + 1

#eval add1 0

def plus (a : Nat) (b : Nat) := a + b

#eval plus 1 2

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin
#eval origin.x
#eval origin.y
#eval Point.x origin
#eval Point.y origin
/- Positional Structure Arguments -/
/- '⟨' の入力方法は\< -/
/- '⟩' の入力方法は\> -/
#check (⟨1.0, 2.0⟩ : Point)
 
#eval { x := 0.0, y := 0.0 : Point }

def zeroX (p : Point) : Point :=
  { p with x := 0 }
#eval zeroX origin

#check Point.mk 1.0 2.0

structure Point' where
  make ::
  x : Float
  y : Float
deriving Repr

#check Point'.make 1.0 2.0

#eval Point.x origin
#eval "a".append "b"

#eval Nat.zero
#eval Nat.succ 0

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false
#eval isZero 0 = true
#eval isZero 5 = false

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ k => k
#eval pred 0 = 0
#eval pred 5 = 4

def getY (p : Point) : Float :=
  match p with
  | { x := _, y := y' } => y'
#eval getY origin

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }
#eval natOrigin

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
#eval replaceX Nat natOrigin 10

inductive Sign where
  | pos
  | neg

def posOrNegThree (s: Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
#eval posOrNegThree Sign.pos
#eval posOrNegThree Sign.neg

def arr := ["a", "b", "c", "d"] /- List String -/

def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)

#eval length String ["a", "b", "c", "d"] == 4
#eval length String (List.cons "a" (List.cons "b" List.nil)) == 2

def length' (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length' α ys)

#eval length' String arr = 4
#eval length' String (List.cons "a" (List.cons "b" List.nil)) = 2

/- 色々な書き方ができる -/
#eval List.length arr = 4
#eval arr.length = 4
#eval List.length (α := String) arr = 4 /- 型を明示 -/

/- 型が分からないのでエラー -/
/- #eval [].head? -/
#eval [].head? (α := Int) = none
#eval ([] : List Int).head? = none

/- '×' の入力方法は\x -/
/- unicodeの入力方法を確認するには、文字の上で<space>\\ -/
def fives : String × Int := { fst := "five", snd := 5 }
def fives' : String × Int := ("five", 5)
#eval fives = fives'

/- 2要素以上のProd(Tuple)はネストする -/
def sevens : String × Int × Nat := ("VII", 7, 10 + 20)
#eval sevens.fst = "VII"
#eval sevens.snd.fst = 7
#eval sevens.snd.snd = 30

/- '⊕' の入力方法は\o+ -/
def PetName : Type := String ⊕ String
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
#eval howManyDogs animals == 3

/- {α : Type} は省略可能 -/
def length'' (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length'' ys)
#eval length'' arr = 4

/- '→' の入力方法は\r or \-> -/
def length''' : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length''' ys)
#eval length''' arr = 4

def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs
#eval drop 2 arr = ["c", "d"]

/- Slow unzip -/
def unzip : List (α × β ) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys => (x :: (unzip xys).fst, y :: (unzip xys).snd)
#eval unzip [(1, 10), (2, 20), (3, 30)] = ([1, 2, 3], [10, 20, 30])

/- Faster unzip -/
def unzip' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip' xys
    (x :: unzipped.fst, y :: unzipped.snd)
#eval unzip' [(1, 10), (2, 20), (3, 30)] = ([1, 2, 3], [10, 20, 30])

/- Faster unzip (use pattern matching) -/
def unzip'' : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip'' xys
    (x :: xs, y :: ys)
#eval unzip'' [(1, 10), (2, 20), (3, 30)] = ([1, 2, 3], [10, 20, 30])

def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α 
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false
#eval sameLength [1, 2, 3] [10, 20, 30] = true
#eval sameLength [1, 2] [10, 20, 30, 40] = false

/- Anonymous Functions (無名関数) -/
/- 'λ' の入力方法は\fun -/
#eval (fun x y => x + y) 1 2 = 3
#eval (λ x y => x + y) 1 2 = 3

/- この関数がなぜ正しく動くのか分からない -/
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
#eval double 10 = 20

def double' : Nat → Nat := fun
  | 0 => 0
  | k => k * 2
#eval double 10 = 20

/- '·' の入力方法は\. -/
#eval (fun x => x + 2) 1 = 3
#eval (· + 2) 1 = 3

/- Namespaces (名前空間) -/
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#check NewNamespace.triple
#check NewNamespace.quadruple

/- open -/
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
#eval timesTwelve 10 = 120

/- open ** in でその下の1行だけ名前空間を開ける -/
open NewNamespace in
#check quadruple
/-
 -- ERROR --
#check triple
-/

/- in を省略することもできる -/
open NewNamespace
#check quadruple
#check triple /- ok -/

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none
#eval Inline.string? Inline.lineBreak = none
#eval Inline.string? (Inline.string "ABC") = (some "ABC")

/- 上記のInline.string?は下記のようにif letを使って書ける -/
def Inline.string?' (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none
#eval Inline.string?' Inline.lineBreak = none
#eval Inline.string?' (Inline.string "ABC") = (some "ABC")

/- String Interpolation (s!) -/
#eval s!"three fives is {NewNamespace.triple 5}" = "three fives is 15"
