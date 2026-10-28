module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Data.Word5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Data.Word8
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Data.Word11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Data.Word14
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Data.Word17
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Transitions.TableAgreement.Data.Word20

/-!
# Finite obligations for the staged word interpretation

Six intermediate full-degree tables break the long words at their existing
stage boundaries. To identify `f` with `L * R⁻¹`, we check `f(R(x)) = L(x)`;
the semantic proof then uses the surjectivity of the genuine permutation `R`.
This avoids expanding inverse words and avoids deriving any permutation law
for an unverified numerical table. All tests include every ambient letter.

`SeedChecks`, `MiddleChecks`, `FrontChecks` and `TailChecks` are independent
numerical obligations, not asserted certificates. `Soundness` connects their
conjunction to the exact published `TableAgreement`.

Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, and the literal generic words
in `FirstFour.Words` and `Transitions.WordModel`. Reproduction and measurements
are in `TableAgreement/source/README.md`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged
open Tables

/-- Clear a right inverse before checking a word on ambient letters. -/
def crossTest (f l r : Nat → Nat) (x : Nat) : Bool :=
  f (r (x % 306936)) == l (x % 306936)

/-- A test is required on the entire original ambient set. -/
def Checks (test : Nat → Bool) : Prop := ∀ x : Fin 306936, test x.val = true

def left5 (x : Nat) : Nat :=
  FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (x))))))))))))))))))))))))))))))))))))

def right5 (x : Nat) : Nat :=
  FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (x))))))))))))))))))))))))))))))))))

def check5 : Nat → Bool := crossTest raw5 left5 right5

def left8 (x : Nat) : Nat :=
  FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (x))))))))))))))))))))))))))))))))

def right8 (x : Nat) : Nat :=
  FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawA (FirstFourModel.rawB (FirstFourModel.rawB (FirstFourModel.rawA (x)))))))))))))))))))))))))))))))

def check8 : Nat → Bool := crossTest raw8 left8 right8

def left11 (x : Nat) : Nat :=
  raw8 (raw5 (raw5 (raw8 (raw8 (raw5 (raw8 (raw5 (raw5 (raw8 (raw5 (raw8 (raw5 (raw8 (raw5 (raw5 (x))))))))))))))))

def right11 (x : Nat) : Nat :=
  raw8 (raw5 (raw5 (raw5 (raw5 (raw5 (raw5 (raw5 (raw8 (raw8 (raw5 (raw8 (raw8 (raw5 (raw8 (x)))))))))))))))

def check11 : Nat → Bool := crossTest raw11 left11 right11

def left14 (x : Nat) : Nat :=
  raw8 (raw8 (raw5 (raw8 (raw5 (raw5 (raw5 (raw8 (raw8 (raw5 (raw5 (raw5 (raw8 (x)))))))))))))

def right14 (x : Nat) : Nat :=
  raw5 (raw8 (raw8 (raw8 (raw8 (raw8 (raw5 (raw5 (raw8 (raw5 (raw8 (raw8 (raw5 (x)))))))))))))

def check14 : Nat → Bool := crossTest raw14 left14 right14

def left17 (x : Nat) : Nat :=
  raw11 (raw14 (raw14 (raw14 (raw11 (raw11 (raw14 (raw11 (raw14 (raw14 (raw11 (raw11 (raw11 (raw11 (x))))))))))))))

def right17 (x : Nat) : Nat :=
  raw11 (raw14 (raw11 (raw14 (raw14 (raw11 (raw14 (x)))))))

def check17 : Nat → Bool := crossTest raw17 left17 right17

def left20 (x : Nat) : Nat :=
  raw11 (raw14 (raw11 (raw14 (raw11 (raw11 (raw14 (raw11 (raw14 (raw14 (raw11 (raw11 (raw11 (x)))))))))))))

def right20 (x : Nat) : Nat :=
  raw14 (raw14 (raw11 (raw14 (raw14 (raw14 (raw11 (raw14 (raw14 (raw14 (raw11 (raw14 (x))))))))))))

def check20 : Nat → Bool := crossTest raw20 left20 right20

def left23 (x : Nat) : Nat :=
  raw20 (raw20 (raw20 (raw20 (raw20 (raw20 (raw20 (raw17 (raw17 (raw17 (raw17 (x)))))))))))

def right23 (x : Nat) : Nat :=
  raw17 (raw20 (raw20 (raw17 (raw20 (raw20 (raw20 (raw20 (raw17 (raw17 (raw20 (x)))))))))))

def check23 : Nat → Bool := crossTest raw23 left23 right23

def left26 (x : Nat) : Nat :=
  raw17 (raw17 (raw17 (raw20 (raw20 (raw20 (raw17 (raw20 (raw20 (raw20 (raw17 (x)))))))))))

def right26 (x : Nat) : Nat :=
  raw17 (raw20 (raw17 (raw17 (raw17 (raw20 (x))))))

def check26 : Nat → Bool := crossTest raw26 left26 right26

def left29 (x : Nat) : Nat :=
  raw17 (raw17 (raw17 (raw20 (raw17 (raw17 (raw20 (raw17 (raw20 (raw20 (x))))))))))

def right29 (x : Nat) : Nat :=
  raw17 (raw17 (raw20 (raw20 (raw17 (raw17 (raw20 (raw17 (raw17 (x)))))))))

def check29 : Nat → Bool := crossTest raw29 left29 right29

def left32 (x : Nat) : Nat :=
  raw17 (raw20 (raw20 (raw17 (raw17 (raw20 (raw17 (raw20 (raw17 (raw17 (x))))))))))

def right32 (x : Nat) : Nat :=
  raw20 (raw17 (raw20 (raw17 (raw20 (raw20 (x))))))

def check32 : Nat → Bool := crossTest raw32 left32 right32

def left35 (x : Nat) : Nat :=
  raw23 (raw32 (raw23 (raw26 (x))))

def right35 (x : Nat) : Nat :=
  raw23 (raw26 (raw23 (x)))

def check35 : Nat → Bool := crossTest raw35 left35 right35

def left38 (x : Nat) : Nat :=
  raw23 (raw26 (raw23 (raw29 (raw32 (x)))))

def right38 (x : Nat) : Nat :=
  raw23 (x)

def check38 : Nat → Bool := crossTest raw38 left38 right38

def left41 (x : Nat) : Nat :=
  raw26 (raw26 (raw26 (x)))

def right41 (x : Nat) : Nat :=
  raw26 (raw23 (raw29 (x)))

def check41 : Nat → Bool := crossTest raw41 left41 right41

def left44 (x : Nat) : Nat :=
  raw38 (raw41 (raw35 (x)))

def right44 (x : Nat) : Nat :=
  raw41 (raw38 (x))

def check44 : Nat → Bool := crossTest raw44 left44 right44

def left47 (x : Nat) : Nat :=
  raw41 (raw38 (raw41 (x)))

def right47 (x : Nat) : Nat :=
  raw35 (x)

def check47 : Nat → Bool := crossTest raw47 left47 right47

def left50 (x : Nat) : Nat :=
  raw47 (raw44 (x))

def right50 (x : Nat) : Nat :=
  raw47 (x)

def check50 : Nat → Bool := crossTest raw50 left50 right50

/-- The sole inverse inside a left factor is word32, an involution. -/
def square32 (x : Nat) : Bool :=
  raw32 (raw32 (x % 306936)) == x % 306936

/-- First stage: word5 and word8 in the original two checked permutations. -/
def SeedChecks : Prop := Checks check5 ∧ Checks check8

/-- Middle stages: words11,14 in words5,8, then words17,20 in words11,14. -/
def MiddleChecks : Prop :=
  Checks check11 ∧ Checks check14 ∧ Checks check17 ∧ Checks check20

/-- Four generators of the first last-four stage, in words17,20. -/
def FrontChecks : Prop :=
  Checks check23 ∧ Checks check26 ∧ Checks check29 ∧ Checks check32

/-- The remaining six generators, and the inverse used inside word35. -/
def TailChecks : Prop :=
  Checks square32 ∧ Checks check35 ∧ Checks check38 ∧ Checks check41 ∧
    Checks check44 ∧ Checks check47 ∧ Checks check50

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour.Transitions.Staged
