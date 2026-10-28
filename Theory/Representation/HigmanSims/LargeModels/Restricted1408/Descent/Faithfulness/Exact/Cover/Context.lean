module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.defCode

/-! Centralizer-coset certificate for the thirteen ATLAS HS relators.
Untrusted data generated from the retained trace; all deduction checks use
Lean's kernel and the actual abstract relations. See `source/README.md`. -/

@[expose] public section
namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
open Subgroup.CosetWordCertificate

def definitions : Definitions Nat where
  parent n := min (defCode n / 16) (n - 1)
  letter n := decode (defCode n % 16)
  parent_lt n := by
    have := Nat.min_le_right (defCode (n+1) / 16) (n+1-1)
    omega

def rotatedRelator (r : Nat) : Word Nat :=
  (if r % 128 < 64 then sourceWords (r / 128)
   else FreeGroup.invRev (sourceWords (r / 128))).rotate (r % 64)

private theorem eval_rotate {G α : Type*} [Group G] (g : α → G)
    (w : Word α) (hw : eval g w = 1) (k : Nat) : eval g (w.rotate k) = 1 := by
  simp only [eval, FreeGroup.lift_mk] at hw ⊢
  rw [List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one hw k

theorem rotatedRelator_valid (r : Nat) : eval certGenerator (rotatedRelator r) = 1 := by
  apply eval_rotate
  split
  · exact sourceWords_valid _
  · rw [eval_invRev, sourceWords_valid, inv_one]

def context : Context Nat :=
  ⟨definitions.parent, definitions.letter, rotatedRelator, allowed⟩

theorem context_valid : Valid context centralizer certGenerator (definitions.repr certGenerator) :=
  definitions.valid rotatedRelator allowed allowed_mem rotatedRelator_valid

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
