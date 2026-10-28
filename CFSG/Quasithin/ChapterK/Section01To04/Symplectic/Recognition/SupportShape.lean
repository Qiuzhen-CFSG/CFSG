module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.Catalogue

/-!
# The support of the quadratic Schur-field orbit

For one factor repeated twice, Frobenius periodicity forces the two selected
positions to differ by r in the graph numbering modulo 2r. Since r is twice
the Schur degree, they are two coefficient twists of the same basic module.
The binary degree is sixteen times the Schur degree. This identifies the
support to which the genuine tensor descent must be applied; no intertwiner
with a descended tensor is inferred from dimension alone.

Source: Aschbacher--Smith K.3.4, printed p.456, and GLS3, Remark 2.8.8.
-/

public section
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition
open Representation Representation.FrobeniusTensor Fin.NatCast
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary

variable {F D V : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} [IsIrreducible ρ]
  {d : D ≃* Derived F} {r : ℕ}

/-- The actual Schur degree is the positive half parameter in the repeated-pair branch. -/
theorem TensorParameters.half_degree (P : TensorParameters ρ d r)
    (ha : P.factors = 1) (ht : P.blocks = 2) :
    let s := Module.finrank (ZMod 2) (Symplectic.SchurField ρ)
    0 < s ∧ r = 2*s ∧ Module.finrank (ZMod 2) V = 16*s := by
  refine ⟨schurField_finrank_pos ρ, ?_, ?_⟩
  · simpa only [ht, Nat.mul_comm] using P.field_degree
  · simpa only [ha, ht, pow_one, show 4^2 = 16 from rfl, Nat.mul_comm] using P.binary_degree

/-- The two graph positions are separated by precisely half a field orbit. -/
theorem TensorParameters.half_support [NeZero (2*r)] (P : TensorParameters ρ d r)
    (ha : P.factors = 1) (ht : P.blocks = 2) :
    ∃ j : Fin (2*r), P.support = {j, j + (r : Fin (2*r))} := by
  classical
  have hs := P.half_degree ha ht
  dsimp at hs
  have hr : 0 < r := by omega
  have hc : P.support.card = 2 := by rw [P.support_card, ha, ht, one_mul]
  obtain ⟨j, k, hjk, heq⟩ := Finset.card_eq_two.mp hc
  have hj : j ∈ P.support := by rw [heq]; simp
  have hrot : j + (r : Fin (2*r)) ∈ P.support := by
    rw [← P.periodic]
    unfold rotateSupport
    refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
    exact congrArg (fun n : ℕ => j + (n : Fin (2*r))) hs.2.1.symm
  have hne : j + (r : Fin (2*r)) ≠ j := by
    intro hh
    have hz : (r : Fin (2*r)) = 0 := add_left_cancel (hh.trans (add_zero j).symm)
    have hv := congrArg Fin.val hz
    simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega : r < 2*r)] at hv
    omega
  rw [heq] at hrot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrot
  have hk := hrot.resolve_left hne
  exact ⟨j, by rw [heq, hk]⟩

end CFSG.Quasithin.ChapterK.Symplectic.Recognition
