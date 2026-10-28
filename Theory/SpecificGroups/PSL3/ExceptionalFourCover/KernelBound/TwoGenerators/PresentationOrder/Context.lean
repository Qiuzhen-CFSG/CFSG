module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.defCode
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelBound.TwoGenerators.PresentationOrder.Setup

/-! A coset-word certificate for the four-relator presentation of PSL₃(4).
The untrusted data are emitted by `source/emit.py`; the generic relator-scan
soundness theorem turns kernel-checked deductions into subgroup witnesses.
Source: Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11. -/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
open Subgroup.CosetWordCertificate

def definitions : Definitions (Fin 2) where
  parent n := min (defCode n / 4) (n - 1)
  letter n := decode (defCode n % 4)
  parent_lt n := by
    have := Nat.min_le_right (defCode (n+1) / 4) (n+1-1)
    omega

/-- Conjugate rotations, also allowing inversion, of the four literal relations. -/
def rotatedRelator (r : Nat) : Subgroup.CosetWordCertificate.Word (Fin 2) :=
  (if r % 32 < 16 then sourceRelator ⟨r / 32 % 4, Nat.mod_lt _ (by decide)⟩
   else FreeGroup.invRev (sourceRelator ⟨r / 32 % 4, Nat.mod_lt _ (by decide)⟩)).rotate (r % 16)

private theorem eval_rotate {G α : Type*} [Group G] (g : α → G)
    (w : Subgroup.CosetWordCertificate.Word α) (hw : eval g w = 1) (k : Nat) : eval g (w.rotate k) = 1 := by
  simp only [eval, FreeGroup.lift_mk] at hw ⊢
  rw [List.map_rotate]
  exact List.prod_rotate_eq_one_of_prod_eq_one hw k

theorem rotatedRelator_valid (r : Nat) : eval generator (rotatedRelator r) = 1 := by
  apply eval_rotate
  split
  · exact sourceRelator_valid _
  · rw [eval_invRev, sourceRelator_valid, inv_one]

def context : Context (Fin 2) :=
  ⟨definitions.parent, definitions.letter, rotatedRelator, allowed⟩

theorem context_valid : Valid context smallSubgroup generator (definitions.repr generator) :=
  definitions.valid rotatedRelator allowed allowed_mem rotatedRelator_valid

end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.OrderCertificate
