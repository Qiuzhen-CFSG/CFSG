module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Saturated
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.SpecificGroups.BinaryLinear.FourSevenFixer
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The binary degree-four containing component

The original two-core quotient supplies a seven-element in the literal image
of L inside I/Z(I). The opposite elementary moved factor normalizes I and
fixes that image pointwise. In PSL₄(2), the seven-element fixer has no
involution; faithful descent through the center of the perfect group I
therefore makes the opposite factor centralize I. The original moved
normalizer bound excludes the escaping component.

This applies to every binary-three module row, including fixed vectors,
without a module irreducibility or later generation-bound hypothesis.
Quasisimple.Source applies it to the remaining containing-carrier list.
Source: Aschbacher--Smith A.3.12(4) and 10.2.9, pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The opposite moved factor centralizes the actual degree-four component. -/
theorem binary_four_common_centralizer [Group.IsPerfect I]
    (h7 : 7 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* PSL(4, ZMod 2)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have h7B : 7 ∣ Nat.card B := by
    have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact (hc ▸ h7).trans (card_quotient_dvd_card (pCore 2 B))
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 7 h7B
  obtain ⟨l,hl⟩ := markedLocalHom_surjective c.strict.le e x
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u, partner_normalizes D c hu⟩
  have ha2 : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩) ^ 2 = 1
    rw [← map_pow]
    have he : (⟨u,partner_normalizes D c hu⟩ : normalizer (I : Set G)) ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := U) u hu)
    rw [he,map_one]
  have hfix : MulAut.centralQuotientAction e a (x : PSL(4,ZMod 2)) = x := by
    have hxval := congrArg Subtype.val hl
    change e (QuotientGroup.mk' (center I) (inclusion c.strict.le l)) = x at hxval
    rw [←hxval,MulAut.centralQuotientAction_apply]
    have hal : a (inclusion c.strict.le l) = inclusion c.strict.le l := by
      apply Subtype.ext
      change u*l.val*u⁻¹=l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val l.property).symm
    rw [hal]
  have hqa : MulAut.centralQuotientAction e a = 1 :=
    BinaryLinear.FourSevenFixer.eq_one_of_fixes_seven x ((orderOf_coe x).trans hx) _
      (by rw [←map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- An original quotient with a factor seven excludes every marked PSL₄(2) carrier. -/
theorem not_binary_four_of_seven [Group.IsPerfect I]
    (h7 : 7 ∣ Nat.card (L ⧸ pCore 2 L))
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) 4 2) : False := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := eI.trans (Atlas.fieldEquivPSL 4 f)
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (binary_four_common_centralizer D c h7 e)

/-- Every original binary-three module row excludes the binary degree-four carrier. -/
theorem not_binary_four_of_binary_three [Group.IsPerfect I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) 4 2) : False := by
  apply not_binary_four_of_seven D c _ hI
  rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]
  decide
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
