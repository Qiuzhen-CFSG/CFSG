module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal.CentralizerImage

/-!
# Cubic fixed points in the extraspecial kernel

The source conjugation action on U and its literal quotient U/Z are
intertwined by the quotient map. Each fiber has two elements; orbit counting
for the Sylow three-group lifts every fixed quotient point. Thus the image
of C_U(D_H) is exactly C_{U/Z}(D_H), and its kernel is the actual central
subgroup Z. This gives the factor two in the fixed-subgroup order.

Source: Aschbacher–Smith, the H-local calculation preceding 15.3.60, p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The fixed subgroup of the literal action on U/Z. -/
noncomputable def quotientFixed (P : Sylow 3 (centralizerH Z)) :
    Subgroup (VectorQuotient Z ZS) :=
  ⨅ p : P, MulAut.fixedSubgroup (quotientAction Z ZS (p : centralizerH Z))

/-- The centralizer of D_H inside the actual U, retaining the inclusion in H. -/
def kernelFixed (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Subgroup (closureU Z ZS) :=
  (centralizer ((P : Subgroup (centralizerH Z)) : Set (centralizerH Z))).comap
    (inclusion (closureU_le_H d.subgroup_le))

/-- Ambient commutation characterizes the fixed subgroup in U. -/
lemma kernelFixed_mem (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z))
    (u : closureU Z ZS) : u ∈ kernelFixed Z ZS d P ↔
      ∀ p : P, ((p : centralizerH Z) : G) * (u : G) =
        (u : G) * ((p : centralizerH Z) : G) := by
  constructor
  · intro hu p
    exact congrArg Subtype.val (hu (p : centralizerH Z) p.property)
  · intro hu p hp
    exact Subtype.ext (hu ⟨p, hp⟩)

/-- Fixedness refers to the published quotientAction, with the chosen Sylow group. -/
lemma quotientFixed_mem (P : Sylow 3 (centralizerH Z)) (u : VectorQuotient Z ZS) :
    u ∈ quotientFixed Z ZS P ↔ ∀ p : P, quotientAction Z ZS (p : centralizerH Z) u = u := by
  simp only [quotientFixed, mem_iInf, MulAut.mem_fixedSubgroup]

/-- The actual central denominator is fixed by the whole Sylow group. -/
lemma denominator_le_kernelFixed (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Z.subgroupOf (closureU Z ZS) ≤ kernelFixed Z ZS d P := by
  intro z hz
  apply (kernelFixed_mem Z ZS d P z).mpr
  intro p
  exact (mem_centralizer_iff.mp (p : centralizerH Z).property z hz).symm

/-- Every quotient fixed point lifts to an element of C_U(D_H). -/
lemma kernelFixed_image [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    (kernelFixed Z ZS d P).map (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))) =
      quotientFixed Z ZS P := by
  let U := closureU Z ZS
  let q : U →* VectorQuotient Z ZS := QuotientGroup.mk' (Z.subgroupOf U)
  let act := conjMulDistribMulActionOfLeNormalizer (centralizerH Z) U (H_normalizes_closureU Z ZS)
  let _ : MulDistribMulAction (centralizerH Z) U := act
  let _ : MulDistribMulAction P U := MulDistribMulAction.compHom U (P : Subgroup (centralizerH Z)).subtype
  let _ : MulDistribMulAction P (VectorQuotient Z ZS) :=
    MulDistribMulAction.compHom _ ((quotientAction Z ZS).comp (P : Subgroup (centralizerH Z)).subtype)
  have hequiv (p : P) (u : U) : q (p • u) = p • q u := by
    exact (quotientAction_mk Z ZS (p : centralizerH Z) u).symm
  have hk : Nat.card q.ker = 2 := by
    rw [QuotientGroup.ker_mk', Nat.card_congr
      (subgroupOfEquivOfLe (d.center_le.trans (ZS_le_closureU Z ZS))).toEquiv]
    exact d.center_card
  have h := fixed_image_of_prime_free_kernel P.isPGroup' q
    (by rw [hk]; decide) hequiv
  have hF : FixedPoints.subgroup P U = kernelFixed Z ZS d P := by
    ext u
    rw [kernelFixed_mem]
    constructor
    · intro hu p
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hu p))
    · intro hu p
      apply Subtype.ext
      change ((p : centralizerH Z) : G) * (u : G) * ((p : centralizerH Z) : G)⁻¹ = (u : G)
      rw [hu, mul_inv_cancel_right]
  have hQ : FixedPoints.subgroup P (VectorQuotient Z ZS) = quotientFixed Z ZS P := by
    ext u
    rw [quotientFixed_mem]
    rfl
  rw [hF, hQ, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), top_inf_eq] at h
  exact h

/-- The fixed subgroup in U has twice the order of its quotient fixed subgroup. -/
lemma kernelFixed_card [Finite G] (d : Recognition Z ZS) (P : Sylow 3 (centralizerH Z)) :
    Nat.card (kernelFixed Z ZS d P) = 2 * Nat.card (quotientFixed Z ZS P) := by
  let q := QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS))
  have h := card_subgroup_of_ker_le q (kernelFixed Z ZS d P)
    (by rw [QuotientGroup.ker_mk']; exact denominator_le_kernelFixed Z ZS d P)
  rw [kernelFixed_image, QuotientGroup.ker_mk', Nat.card_congr
    (subgroupOfEquivOfLe (d.center_le.trans (ZS_le_closureU Z ZS))).toEquiv,
    d.center_card] at h
  exact h
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
