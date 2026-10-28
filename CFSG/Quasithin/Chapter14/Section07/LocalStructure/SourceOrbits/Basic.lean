module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import Theory.LinearAlgebra.BinaryTwoTransitivity

/-!
# Original subgroup placements for 14.7.12--13

The elementary normal U lies in the original Sylow subgroup of H. Since
U centralizes V, the proved characteristic-two natural-action theorem
places it in Q=O₂(LT); its full L-span remains in Q. The natural L-action
also transports any ordered pair of distinct nonidentity vectors of V.
All maps are the original conjugation maps, and the full earlier 12.2.2
input is retained only for the existing natural centralizer theorem.

Source: Aschbacher--Smith 14.7.12--13, printed p.1046.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

include d in
/-- The original elementary U lies in T, without any critical-path hypothesis. -/
theorem U_le_T : F.U ≤ (T : Subgroup G) := by
  let := d.natural.chosen.elementary
  let := F.U_normal
  have hp : IsPGroup 2 (F.U.subgroupOf F.H) := d.U_elementary.isPGroup.comap_subtype
  have hh := hp.le_sylow_of_normal (T.subtype (F.invariant 1))
  intro x hx
  exact hh (show (⟨x,F.U_le_H hx⟩ : F.H) ∈ F.U.subgroupOf F.H from hx)

omit [Finite G] in
/-- L normalizes the actual two-core of LT. -/
theorem L_normalizes_Q : L ≤ normalizer (Q T L : Set G) :=
  le_sup_left.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

include d in
/-- The original U and its L-span lie in the literal Q. -/
theorem U_and_span_le_Q
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    F.U ≤ Q T L ∧ conjugateSpanBy F.U L ≤ Q T L := by
  have hU : F.U ≤ Q T L := by
    change F.U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←d.natural.centralizer_LT structural]
    refine le_inf ((U_le_T d).trans le_sup_right) ?_
    exact (le_centralizer_iff_isMulCommutative.mpr d.abelian).trans
      (centralizer_le (Data.V_le_U F))
  exact ⟨hU,conjugateSpanBy_le hU L_normalizes_Q⟩

include d in
/-- Full natural L action transports the exact ordered vector pair. -/
theorem pair_transporter {a b c e : G}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (he : e ∈ V)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (he1 : e ≠ 1)
    (hab : a ≠ b) (hce : c ≠ e) :
    ∃ l ∈ L, l*a*l⁻¹ = c ∧ l*b*l⁻¹ = e := by
  let := d.natural.chosen.elementary
  let a' : Additive V := Additive.ofMul ⟨a,ha⟩
  let b' : Additive V := Additive.ofMul ⟨b,hb⟩
  let c' : Additive V := Additive.ofMul ⟨c,hc⟩
  let e' : Additive V := Additive.ofMul ⟨e,he⟩
  obtain ⟨f,hfa,hfb⟩ := BinaryLinear.exists_linearEquiv_pair a' b' c' e'
    (fun hh => ha1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hb1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hc1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => he1 (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hab (congrArg (fun v : Additive V => (v.toMul : G)) hh))
    (fun hh => hce (congrArg (fun v : Additive V => (v.toMul : G)) hh))
  obtain ⟨l,hl⟩ := d.natural.naturalMarking.geometryAction.surjective f
  refine ⟨l,l.property,?_,?_⟩
  · have hh := d.natural.naturalMarking.geometryAction.conjugation l a'
    rw [hl,hfa] at hh
    exact hh.symm
  · have hh := d.natural.naturalMarking.geometryAction.conjugation l b'
    rw [hl,hfb] at hh
    exact hh.symm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
