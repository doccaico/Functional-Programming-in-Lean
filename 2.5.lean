def onePlusOneIsTwo : 1 + 1 = 2 := rfl
/- ERROR -/
/- def onePlusOneIsFifteen : 1 + 1 = 15 := rfl -/

def OnePlusOneIsTwo' : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo' : OnePlusOneIsTwo' := rfl

theorem onePlusOneIsTwo'' : 1 + 1 = 2 := by decide

/- '∧'の入力方法は\and -/
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by decide

/- '∨'の入力方法は\or -/
theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide

/- '¬'の入力方法は\not -/
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide

/- '→'の入力方法は\r -/
theorem falseImpliesTrue : False → True := by decide
theorem falseImpliesTrue' : (1 + 1 = 5) → (2 + 3 = 5) := by decide

/-
* Evidence as Arguments
-/
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

/- ERROR -/
/- def third (xs : List α) : α := xs[2] -/
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by decide)

/-
* Indexing Without Evidence
-/

def thirdOption (xs : List α) : Option α := xs[2]?
#eval thirdOption woodlandCritters = some "snail"
#eval thirdOption ["only", "two"] = none

#eval woodlandCritters[1]! = "deer"

/-
* Exercises
-/

def exerciseOne : 2 + 3 = 5 := rfl
def exerciseOne' : "Hello, ".append "world" = "Hello, world" := rfl
/- ERROR -/
/- def exercisesOne'' : 5 < 18 := rfl -/

theorem exerciseTwo : 2 + 3 = 5 := by decide
theorem exerciseTwo' : "Hello, ".append "world" = "Hello, world" := by decide
theorem exerciseTwo'' : 5 < 18 := by decide

def fifthList := ["a", "b", "c", "d", "e"]
def fifth (xs : List α) (ok : xs.length > 4) : α := xs[4]
#eval fifth fifthList (by decide) = "e"
