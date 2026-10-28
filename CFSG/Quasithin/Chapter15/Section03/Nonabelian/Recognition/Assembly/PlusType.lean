module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly
public import Theory.GroupTheory.DihedralCentralProductThree

/-!
# The actual plus-type group in 15.3.58(2)

The preimage of a recognized singular three-space under U → U/Z has order
sixteen. The source power quadratic form makes all its elements square to
one, so it is elementary abelian and contains the center of U. Since the
same quotient dimension gives |U| = 128, the intrinsic recognition constructs
an equivalence with the external central product of three D₈ groups.

The only additional source inputs are extraspeciality and Z(U) = Z from
15.3.55, and the interpretation of the quadratic form by squares from
15.3.56(1). No elementary subgroup or plus-type conclusion is assumed.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1147–1149.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u f
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}

/-- The literal power-form facts of 15.3.55 and 15.3.56(1). -/
structure EarlierPowerInputs (d : EarlierSourceInputs Z ZS V M C v s)
    (a : EarlierActionInputs d) : Prop where
  extraspecial : IsExtraspecial 2 (closureU Z ZS)
  center_eq : center (closureU Z ZS) = Z.subgroupOf (closureU Z ZS)
  power_zero : ∀ x : closureU Z ZS,
    a.quadratic (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) x)) = 0 ↔
      x ^ 2 = 1

/-- The singular constituent lifts to the elementary subgroup needed by
intrinsic plus-type recognition. All maps are the literal quotient maps. -/
theorem NaturalPair.elementary_preimage
    {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}
    (p : NaturalPair d a) (b : EarlierPowerInputs d a) :
    ∃ A : Subgroup (closureU Z ZS), IsElementaryAbelian 2 A ∧
      Nat.card A = 16 ∧ center (closureU Z ZS) ≤ A := by
  let U := closureU Z ZS
  let N := Z.subgroupOf U
  let π := QuotientGroup.mk' N
  let D : Subgroup (VectorQuotient Z ZS) :=
    AddSubgroup.toSubgroup' p.pair.first.toSubmodule.toAddSubgroup
  let A : Subgroup U := D.comap π
  have hsquare (x : A) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact (b.power_zero x.val).mp (p.first_singular _ x.property)
  have hinv (x : A) : x⁻¹ = x :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hsquare x)
  have hab : IsElementaryAbelian 2 A := {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc
        x * y = (x * y)⁻¹ := (hinv _).symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
        _ = y * x := by rw [hinv, hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
  have hNA : N ≤ A := by
    intro x hx
    change π x ∈ D
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact D.one_mem
  have hcN : Nat.card (N.subgroupOf A) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNA).toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (d.Z_le_ZS.trans (ZS_le_closureU Z ZS))).toEquiv).trans d.Z_card
  let e : p.pair.first.toSubmodule ≃ D := {
    toFun x := ⟨x.val.toMul, x.property⟩
    invFun x := ⟨Additive.ofMul x.val, x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hcD : Nat.card D = 8 := by
    rw [← Nat.card_congr e, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, p.first_model.finrank_eq_three]
    rfl
  have hmap : A.map π = D := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hi : N.relIndex A = Nat.card D := by
    have hh := Subgroup.relIndex_ker (K := A) π
    rw [QuotientGroup.ker_mk', hmap] at hh
    exact hh
  have hc := (N.subgroupOf A).card_mul_index
  change Nat.card (N.subgroupOf A) * N.relIndex A = Nat.card A at hc
  rw [hcN, hi, hcD] at hc
  exact ⟨A, hab, hc.symm, b.center_eq ▸ hNA⟩

/-- The order follows from the proved parameter and the literal quotient U/Z. -/
theorem NaturalPair.card_U
    {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}
    (p : NaturalPair d a) : Nat.card (closureU Z ZS) = 128 := by
  have hcN : Nat.card (Z.subgroupOf (closureU Z ZS)) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (d.Z_le_ZS.trans (ZS_le_closureU Z ZS))).toEquiv).trans d.Z_card
  have hcQ : Nat.card (VectorQuotient Z ZS) = 64 := by
    rw [← Nat.card_congr (Additive.toMul : Space Z ZS ≃ VectorQuotient Z ZS),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      d.dimension, p.s_eq_one]
    rfl
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Z.subgroupOf (closureU Z ZS))
  change Nat.card (closureU Z ZS) = Nat.card (VectorQuotient Z ZS) *
    Nat.card (Z.subgroupOf (closureU Z ZS)) at hc
  rw [hcQ, hcN] at hc
  exact hc

/-- An actual equivalence with the external central product of three D₈ groups,
using the singular constituent's preimage rather than an assumed plus type. -/
theorem NaturalPair.plusType
    {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}
    (p : NaturalPair d a) (b : EarlierPowerInputs d a) :
    Nonempty (closureU Z ZS ≃* DihedralCentralProductThree.Model) := by
  obtain ⟨A, hA, hcA, hZA⟩ := p.elementary_preimage b
  let := hA
  let := b.extraspecial
  exact DihedralCentralProductThree.exists_mulEquiv_of_elementary_sixteen p.card_U A hcA hZA

/-- All of 15.3.58(2), conditional on the enumerated earlier-source data and
exact universal classification witnesses. -/
theorem lemma_15_3_58_two_of_earlier_source
    (hG64 : G64SourceTheorem C)
    (hG93 : IrreducibleSieve.G93SourceTheorem.{u, u, f} C)
    (d : EarlierSourceInputs Z ZS V M C v s) (a : EarlierActionInputs d)
    (b : EarlierPowerInputs d a) :
    s = 1 ∧ Nonempty (closureU Z ZS ≃* DihedralCentralProductThree.Model) := by
  obtain ⟨p⟩ := naturalPair_of_earlier_source hG64 hG93 d a
  exact ⟨p.s_eq_one, p.plusType b⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
