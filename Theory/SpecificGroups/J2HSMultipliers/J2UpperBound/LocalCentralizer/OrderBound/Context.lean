module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.defCode
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound.Words

/-! Kernel-checked coset certificate for the normalized J₂ centralizer presentation, the trivial subgroup.
Generated from `source/compact.json` by `source/generate.py`.
The data are untrusted; `Scan.chunk_sound` supplies actual subgroup witnesses. -/

@[expose] public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
open Subgroup.CosetWordCertificate

def definitions : Definitions Bool where
  parent n := min (defCode n / 4) (n - 1)
  letter n := decode (defCode n % 4)
  parent_lt n := by
    have := Nat.min_le_right (defCode (n+1) / 4) (n+1-1)
    omega

/-- All rotations of a source relator or its inverse remain actual relations. -/
def rotatedRelator (r : Nat) : Word Bool :=
  (if r % 256 < 128 then relatorWord ⟨r / 256 % 16, Nat.mod_lt _ (by decide)⟩
   else FreeGroup.invRev (relatorWord ⟨r / 256 % 16, Nat.mod_lt _ (by decide)⟩)).rotate (r % 128)

theorem eval_rotate {G α : Type*} [Group G] (g : α → G)
    (w : Word α) (hw : eval g w = 1) (k : Nat) : eval g (w.rotate k) = 1 := by
  simp only [eval, FreeGroup.lift_mk] at hw ⊢
  rw [List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one hw k

theorem rotatedRelator_valid (r : Nat) : eval generator (rotatedRelator r) = 1 := by
  apply eval_rotate
  split
  · exact relatorWord_valid _
  · rw [eval_invRev, relatorWord_valid, inv_one]

def context : Context Bool :=
  ⟨definitions.parent, definitions.letter, rotatedRelator, fun _ => false⟩

theorem context_valid : Valid context (⊥ : Subgroup Presentation) generator (definitions.repr generator) :=
  definitions.valid rotatedRelator (fun _ => false) (by simp) rotatedRelator_valid

end Theory.SpecificGroups.J2HSMultipliers.J2.LocalCentralizerPresentation.OrderBound
