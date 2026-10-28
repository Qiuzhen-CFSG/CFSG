module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.EqualityRowOrdinary.EvenModels.Geometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryThree
import all CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.EvenModels.BinaryThree

/-!
# Direct BinaryThree ordinary-component exclusion

This internal source extension reuses the intrinsic model calculations of
OrdinaryComponents.EvenModels.BinaryThree. The original residual input and literal
marked Sylow supply its geometric hypotheses without a partner residual identity.
The deliberate private import keeps those existing model lemmas internal.

Source: Aschbacher--Smith 15.2.24, printed p.1117, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
open Section01 Section03 Candidates.ComponentStructure ClassificationModels OrdinaryComponents
open BinaryLinear BinaryLinear.OuterCyclic BinaryNaturalDual.VectorStabilizers
open ChapterB.QuasisimpleSource.NaturalDualCentralizer DoubleCoverCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
variable (hcard : Nat.card (centralInvolutions T) = 2)
variable {P : Sylow 2 I} {z : G}
variable (c : ComponentData (T := T) (Mc := Mc) I P z)
include r hcard

/-- If the original involution fixes only a two-group in a centerless component
with two-group outer quotient, K centralizes that component, contradicting escape. -/
theorem not_component_of_fixed_and_outer_two
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hcenter : center c.component = ⊥)
    (houter : IsPGroup 2 (MulAut.Outer c.component))
    (hfixed : IsPGroup 2 a.fixedSubgroup) : False := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    r.residual_le_plane_escape hI
  have hKL := r.ordinary_component_normalizes hI c.isComponent
  let A := K.subgroupOf I
  have hAN : A ≤ normalizer (c.component : Set I) := by
    intro k hk
    apply mem_normalizer_iff.mpr
    intro x
    have hh := mem_normalizer_iff.mp (hKL hk) (x : G)
    have hmem (y : I) : (y : G) ∈ c.component.map I.subtype ↔ y ∈ c.component := by
      exact mem_map_iff_mem (f := I.subtype) I.subtype_injective
    rw [← hmem x, ← hmem (k * x * k⁻¹)]
    exact hh
  let f : A →* MulAut c.component := c.component.normalizerMonoidHom.comp (inclusion hAN)
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hKI).symm.toMonoidHom (subgroupOfEquivOfLe hKI).symm.surjective
  have hcomm (k : A) : a * f k = f k * a := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((a (f k x) : I) : G) = (((f k) (a x) : I) : G)
    rw [ha]
    change z * (((k : I) : G) * ((x : I) : G) * ((k : I) : G)⁻¹) * z⁻¹ =
      ((k : I) : G) * ((a x : I) : G) * ((k : I) : G)⁻¹
    rw [ha]
    have hkMc : ((k : I) : G) ∈ Mc :=
      r.geometry.in_partner (map_subtype_le _ k.property)
    have hzk : z * ((k : I) : G) = ((k : I) : G) * z := by
      have hh := hkMc
      rw [← (r.marked_centralizer_of_seed_card hcard hz hzne).2] at hh
      exact (mem_centralizer_singleton_iff.mp hh).symm
    calc
      _ = (z * ((k : I) : G)) * ((x : I) : G) * (z * ((k : I) : G))⁻¹ := by group
      _ = (((k : I) : G) * z) * ((x : I) : G) * (((k : I) : G) * z)⁻¹ := by rw [hzk]
      _ = _ := by group
  have hf := perfect_action_eq_one_of_fixed_and_outer_pGroups hpA hcenter houter a
    hfixed f hcomm
  have hLK : c.component.map I.subtype ≤ centralizer (K : Set G) := by
    rintro l ⟨x,hx,rfl⟩ k hk
    let ki : A := ⟨⟨k,hKI hk⟩,hk⟩
    have he := congrArg (fun b : MulAut c.component => ((b ⟨x,hx⟩ : I) : G))
      (DFunLike.congr_fun hf ki)
    change k * (x : G) * k⁻¹ = (x : G) at he
    exact mul_inv_eq_iff_eq_mul.mp he
  exact c.escapes (hLK.trans (r.residual_centralizer_le_partner))

open scoped MatrixGroups
/-- The actual binary PSL₃ row of15.2.24 is impossible. -/
theorem not_binary_linear_three_component
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hz : z ∈ centralInvolutions T) (hzne : z ≠ 1)
    (a : MulAut c.component)
    (ha : ∀ x : c.component, ((a x : I) : G) = z * (x : G) * z⁻¹)
    (hm : ClassicalGroup.IsPSL c.component 3 2)
    (hi : a ∈ (MulAut.conj (G := c.component)).range) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let eq : c.component ≃* Matrix.PSL3Two.SL :=
    (e.trans (Atlas.fieldEquivPSL 3 ef)).trans Matrix.PSL3Two.equiv.symm
  have hc : center c.component = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr eq ⟨x,hx⟩).property
    change eq x ∈ center Matrix.PSL3Two.SL at hh
    rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact eq.map_eq_one_iff.mp hh
  have ho := Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
    (MulAut.outerCongr eq).symm
  apply not_component_of_fixed_and_outer_two r hcard c hI hz hzne a ha hc ho
  obtain ⟨t,ht⟩ := hi
  have horder := marked_component_action_order_two c
    (r.marked_centralizer_of_seed_card hcard hz hzne).1 hz hzne a ha
  have htorder : orderOf t = 2 := by
    rw [← orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hc),ht]
    exact horder
  have hf := Matrix.PSL3Two.InvolutionResidual.sl_centralizer_two (eq t)
    ((eq.orderOf_eq t).trans htorder)
  have he := MulAut.fixedSubgroupCongr eq (MulAut.conj t)
  rw [MulAut.congr_conj,MulAut.fixedSubgroup_conj,MulAut.fixedSubgroup_conj] at he
  rw [←ht,MulAut.fixedSubgroup_conj]
  exact hf.of_equiv he.symm
end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.EqualityRowEvenModels
