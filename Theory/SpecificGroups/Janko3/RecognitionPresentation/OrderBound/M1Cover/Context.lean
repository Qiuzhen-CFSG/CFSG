module

public import Theory.SpecificGroups.Janko3.RecognitionPresentation.OrderBound.M1Cover.defCode

/-! Kernel-checked coset certificate for ATLAS J3G1-P1, literal subgroup M₁.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
open Subgroup.CosetWordCertificate

def definitions : Definitions (Fin 3) where
  parent n := min (defCode n / 8) (n - 1)
  letter n := decode (defCode n % 8)
  parent_lt n := by
    have := Nat.min_le_right (defCode (n+1) / 8) (n+1-1)
    omega

/-- All rotations of a source relator or its inverse remain actual relations. -/
def rotatedRelator (r : Nat) : Word (Fin 3) :=
  (if r % 128 < 64 then relatorWords (r / 128)
   else FreeGroup.invRev (relatorWords (r / 128))).rotate (r % 64)

theorem eval_rotate {G α : Type*} [Group G] (g : α → G)
    (w : Word α) (hw : eval g w = 1) (k : Nat) : eval g (w.rotate k) = 1 := by
  simp only [eval, FreeGroup.lift_mk] at hw ⊢
  rw [List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one hw k

theorem rotatedRelator_valid (r : Nat) : eval generator (rotatedRelator r) = 1 := by
  apply eval_rotate
  split
  · exact generator_relators _
  · rw [eval_invRev, generator_relators, inv_one]

def context : Context (Fin 3) :=
  ⟨definitions.parent, definitions.letter, rotatedRelator, allowed⟩

theorem context_valid : Valid context M1 generator (definitions.repr generator) :=
  definitions.valid rotatedRelator allowed allowed_mem rotatedRelator_valid

end Sporadic.Janko3.RecognitionPresentation.OrderBound.M1Certificate
