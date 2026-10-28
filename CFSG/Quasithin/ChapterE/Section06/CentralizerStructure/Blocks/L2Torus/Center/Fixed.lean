module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Natural

/-!
# Fixed points on the block's natural quotient

A nonidentity diagonal unit has no fixed vectors on the natural plane.
Thus the torus-fixed elements of U(L) are precisely C_U(L). Together with
the Borel factorization this identifies the two fixed subgroups relevant
to the remaining global-centrality argument.

Source: the natural action in C.1.12 and the L₂ case of E.6.7,
Aschbacher–Smith, printed pp.124 and 246.
-/

@[expose] public section

open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus
variable {L F : Type*} [Group L] [Field F] [Finite F]
    {B : Subgroup L} {a : MarkedBlockModel L B F}

theorem DiagonalSection.torus_nontrivial (d : DiagonalSection a)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) : Nontrivial d.torus := by
  let : Finite d.torus := Finite.of_injective d.torusEquiv d.torusEquiv.injective
  apply Finite.one_lt_card_iff_nontrivial.mp
  rw [d.torus_card, hF]
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  omega

/-- The torus has no fixed points on U(L) beyond the genuine central kernel. -/
theorem DiagonalSection.blockU_fixed_eq_center (d : DiagonalSection a)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    ChapterC.blockU L ⊓ centralizer (d.torus : Set L) = ChapterC.blockU L ⊓ center L := by
  apply le_antisymm _ (inf_le_inf_left _ (center_le_centralizer _))
  rintro v ⟨hvU, hvX⟩
  refine ⟨hvU, ?_⟩
  let : Nontrivial d.torus := d.torus_nontrivial hn hF
  obtain ⟨x, hx⟩ := exists_ne (1 : d.torus)
  have hu : (d.torusEquiv x : F) ≠ 1 := by
    intro h
    apply hx
    apply d.torusEquiv.injective
    exact (Units.ext h).trans (map_one _).symm
  let vU : ChapterC.blockU L := ⟨v, hvU⟩
  have hc : ChapterC.blockConjugate L (x : L) vU = vU := by
    apply Subtype.ext
    change (x : L) * v * (x : L)⁻¹ = v
    rw [mem_centralizer_iff.mp hvX x x.property, mul_inv_cancel_right]
  have he := a.naturalMap_conjugate (x : L) vU
  rw [hc, d.quotient_torusEquiv] at he
  apply (a.naturalMap_eq_one vU).mp
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · have h : (a.naturalMap vU).toAdd 0 =
        (d.torusEquiv x : F) * (a.naturalMap vU).toAdd 0 := by
      simpa [diag2_coe', mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 0
    by_contra hzero
    exact hu (mul_right_cancel₀ hzero (h.symm.trans (one_mul _).symm))
  · have h : (a.naturalMap vU).toAdd 1 =
        (d.torusEquiv x : F)⁻¹ * (a.naturalMap vU).toAdd 1 := by
      simpa [diag2_coe', mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 1
    have hui : (d.torusEquiv x : F)⁻¹ ≠ 1 := by simpa using hu
    by_contra hzero
    exact hui (mul_right_cancel₀ hzero (h.symm.trans (one_mul _).symm))

variable [CharP F 2]

/-- Since the omega-center is already S-fixed, torus-fixed means Borel-fixed. -/
theorem DiagonalSection.omegaCenter_fixed_eq_borel_fixed (d : DiagonalSection a)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (d.torus : Set L) =
      Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ centralizer (B : Set L) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le d.torus_le_borel))
  rintro z ⟨hz, hx⟩
  refine ⟨hz, mem_centralizer_iff.mpr ?_⟩
  intro b hb
  rw [d.borel_product S hS] at hb
  obtain ⟨s, hs, x, hxX, rfl⟩ := hb
  have hscomm := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2 s hs
  have hxcomm := mem_centralizer_iff.mp hx x hxX
  calc
    (s * x) * z = s * (x * z) := mul_assoc _ _ _
    _ = s * (z * x) := congrArg (s * ·) hxcomm
    _ = (s * z) * x := (mul_assoc _ _ _).symm
    _ = (z * s) * x := congrArg (· * x) hscomm
    _ = z * (s * x) := mul_assoc _ _ _

end CFSG.Quasithin.ChapterE.Section06.L2Torus
