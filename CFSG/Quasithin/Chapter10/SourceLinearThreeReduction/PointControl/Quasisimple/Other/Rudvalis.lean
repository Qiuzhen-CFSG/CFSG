module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Saturated
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.SpecificGroups.Rudvalis.BinaryThreeFixer
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# Rudvalis exclusion on every original binary-three module row

The literal image of L in I/Z(I) retains the two-core quotient, so its order
is divisible by 21. The opposite elementary moved factor fixes that image
pointwise. The actual Rudvalis involution-centralizer orders and the inner
automorphism theorem make this action trivial. Faithful descent for the
perfect group I then gives common centralization, contradicting the source
moved-normalizer bound.

No irreducibility or splitting of the selected module is required, and its
fixed vectors are retained. Quasisimple.Source applies the result to the
remaining natural-section carriers.
Source: Aschbacher--Smith A.3.12 and 10.2.9, printed pp.47--48,750--751.
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

/-- The opposite moved factor centralizes an actual Rudvalis component
whenever the original two-core quotient has a factor 21. -/
theorem rudvalis_common_centralizer [IsQuasisimple I]
    (h21 : 21 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Rudvalis.Model) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have h21B : 21 ∣ Nat.card B := by
    have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact (hc ▸ h21).trans (card_quotient_dvd_card (pCore 2 B))
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩
  have ha2 : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩) ^ 2 = 1
    rw [←map_pow]
    have he : (⟨u,partner_normalizes D c hu⟩ : normalizer (I : Set G)) ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := U) u hu)
    rw [he,map_one]
  have hfix : ∀ x ∈ B, MulAut.centralQuotientAction e a x = x := by
    intro x hx
    obtain ⟨l,hl⟩ := markedLocalHom_surjective c.strict.le e ⟨x,hx⟩
    have hxval := congrArg Subtype.val hl
    change e (QuotientGroup.mk' (center I) (inclusion c.strict.le l)) = x at hxval
    rw [←hxval,MulAut.centralQuotientAction_apply]
    have hal : a (inclusion c.strict.le l) = inclusion c.strict.le l := by
      apply Subtype.ext
      change u*l.val*u⁻¹=l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val l.property).symm
    rw [hal]
  have hqa : MulAut.centralQuotientAction e a = 1 :=
    Rudvalis.eq_one_of_fixes_twentyOne B h21B _ (by rw [←map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- A factor 21 in the actual original quotient excludes Rudvalis. -/
theorem not_rudvalis_of_twentyOne [IsQuasisimple I]
    (h21 : 21 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Rudvalis.Model) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (rudvalis_common_centralizer D c h21 e)

/-- Every original binary-three row, including its natural section and
fixed kernel, excludes the actual Rudvalis carrier. -/
theorem not_rudvalis_of_binary_three [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (e : (I ⧸ center I) ≃* Rudvalis.Model) : False := by
  apply not_rudvalis_of_twentyOne D c _ e
  rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]
  decide

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
