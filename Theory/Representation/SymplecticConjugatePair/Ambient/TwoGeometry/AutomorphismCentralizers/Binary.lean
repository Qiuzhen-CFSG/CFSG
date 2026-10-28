module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.Representation.SymplecticConjugatePair.OddOrder.Binary.Automorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.AutomorphismCentralizers.FixedModels
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.Basic

/-!
# Binary outer involutions and their centralizers

Restriction of Aut(S₆) to the characteristic A₆ is faithful. The proved
exceptional A₆ conjugacy calculation therefore makes all noninner involutions
of Aut(S₆) conjugate. Transport through the actual polar equivalence
Sp₄(2) ≃ S₆ identifies a diagram-moving involution with the constructed graph
map. Its full fixed group is Sz(2), whose Sylow two-subgroup is cyclic of
order four. The cyclic outer quotient then gives centralizer two-rank at most
two. No cocycle descent premise or identification of S₆ with A₆ is used.

Source: Aschbacher–Smith H.7, printed p.389, and the exceptional involutions
underlying 16.1.4 on pp.1170–1173; GLS3 Proposition 5.2.7(a).
-/

public noncomputable section

open Subgroup GLS3.Chapter5
namespace SymplecticConjugatePair.Ambient.AutomorphismCentralizers.BinaryInvolutions
private abbrev S := Equiv.Perm (Fin 6)
private abbrev A := alternatingGroup (Fin 6)
local instance : (alternatingGroup (Fin 6)).Characteristic := by
  rw [← alternatingGroup.commutator_perm_eq (by norm_num : 5 ≤ Nat.card (Fin 6))]
  infer_instance
private abbrev res : MulAut S →* MulAut A := MulAut.characteristic A
private theorem res_conj (g : S) : res (MulAut.conj g) = MulAut.conjNormal g := rfl
private theorem res_compatible (a : MulAut S) (g : S) :
    res a * MulAut.conjNormal g * (res a)⁻¹ = MulAut.conjNormal (a g) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change a (g * a.symm x.val * g⁻¹) = a g * x.val * (a g)⁻¹
  simp
private theorem res_injective : Function.Injective res := by
  intro a b h
  apply MulEquiv.ext
  intro g
  apply alternatingConjHom_injective (by decide : 4 ≤ Fintype.card (Fin 6))
  rw [← res_compatible, ← res_compatible, h]
private theorem res_not_natural (a : MulAut S) (ha : a ∉ MulAut.innerSubgroup S) :
    res a ∉ naturalAlternatingAutomorphismSubgroup := by
  rintro ⟨g, hg⟩
  exact ha ⟨g, res_injective ((res_conj g).trans hg)⟩
private theorem res_normal_form (a : MulAut S) (ha : a ^ 2 = 1)
    (hi : a ∉ MulAut.innerSubgroup S) :
    ∃ g : S, res a = MulAut.conjNormal g * canonicalExceptionalAut *
      (MulAut.conjNormal g)⁻¹ := by
  obtain ⟨s, hs⟩ := exceptionalAut_eq_twist (res a) (res_not_natural a hi)
  have hsq : exceptionalTwistAut s ^ 2 = 1 := by
    rw [← hs, ← map_pow, ha, map_one]
  exact exceptionalTwistAut_conjugate_canonical s hsq |>.imp (fun g hg => hs.trans hg)

private theorem outer_involutions_conjugate (a b : MulAut S)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hai : a ∉ MulAut.innerSubgroup S) (hbi : b ∉ MulAut.innerSubgroup S) :
    IsConj a b := by
  obtain ⟨g, hg⟩ := res_normal_form a ha hai
  obtain ⟨h, hh⟩ := res_normal_form b hb hbi
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨MulAut.conj (g * h⁻¹), res_injective ?_⟩
  rw [map_mul, map_mul, map_inv, res_conj, hg, hh, map_mul, map_inv]
  group
end SymplecticConjugatePair.Ambient.AutomorphismCentralizers.BinaryInvolutions
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace SymplecticConjugatePair.Ambient.AutomorphismCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual binary outer quotient is cyclic, using the two geometric
automorphism types. -/
theorem binary_outer_cyclic (hF : Nat.card F = 2) :
    IsCyclic (MulAut.Outer (Sp F)) := by
  let π := QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨π ExceptionalGraph.graphAut, top_unique ?_⟩
  intro x _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Sp F)) x
  have hip (g : Sp F) : π (MulAut.conj g) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  by_cases ha : PreservesDiagram a
  · obtain ⟨g, σ, rfl⟩ := SemilinearClassification.inner_field_of_preservesDiagram a ha
    rw [fieldAutomorphism_eq_one_of_card_two hF, mul_one, hip]
    exact (zpowers _).one_mem
  · obtain ⟨g, rfl⟩ := SymplecticConjugatePair.OddOrder.Binary.binary_moving_eq_inner_graph hF a ha
    rw [map_mul, hip, one_mul]
    exact mem_zpowers _

/-- Every diagram-moving binary involution is conjugate to the constructed
exceptional graph automorphism, with no descent premise. -/
theorem binary_moving_conjugate_graph (hF : Nat.card F = 2)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : ¬ PreservesDiagram a) :
    IsConj a (ExceptionalGraph.graphAut (F := F)) := by
  let e := (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F hF)).trans
    Binary.symmetricSixEquiv.symm
  let φ := MulAut.congr e
  have hout (b : MulAut (Sp F)) (hb : ¬ PreservesDiagram b) :
      φ b ∉ MulAut.innerSubgroup (Equiv.Perm (Fin 6)) := by
    intro hm
    rw [← MulAut.map_innerSubgroup_congr e] at hm
    obtain ⟨c, hc, hcb⟩ := hm
    have he : c = b := φ.injective hcb
    obtain ⟨g, hg⟩ := he ▸ hc
    exact hb (hg ▸ inner_preservesDiagram g)
  have hs : ExceptionalGraph.graphAut (F := F) ^ 2 = 1 := by
    rw [ExceptionalGraph.graphAut_square, fieldAutomorphism_eq_one_of_card_two hF]
  have hsq : (φ a) ^ 2 = 1 := by
    have ha2 : a ^ 2 = 1 := by simpa only [hao] using pow_orderOf_eq_one a
    rw [← map_pow, ha2, map_one]
  have hgsq : (φ ExceptionalGraph.graphAut) ^ 2 = 1 := by
    rw [← map_pow, hs, map_one]
  have hh := SymplecticConjugatePair.Ambient.AutomorphismCentralizers.BinaryInvolutions.outer_involutions_conjugate
    (φ a) (φ ExceptionalGraph.graphAut) hsq hgsq
    (hout a ha) (hout _ ExceptionalGraph.graphAut_not_preservesDiagram)
  obtain ⟨c, hc⟩ := isConj_iff.mp hh
  refine isConj_iff.mpr ⟨φ.symm c, φ.injective ?_⟩
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using hc
/-- The binary automorphism-centralizer bound has no descent or model premise. -/
theorem binary_moving_centralizer_rank_le (hF : Nat.card F = 2)
    (a : MulAut (Sp F)) (hao : orderOf a = 2) (ha : ¬ PreservesDiagram a) :
    primeRank 2 (centralizer ({a} : Set (MulAut (Sp F)))) ≤ 2 := by
  let := binary_outer_cyclic hF
  have hfixed : primeRank 2 a.fixedSubgroup ≤ 1 := by
    rw [fixed_rank_eq_of_isConj (binary_moving_conjugate_graph hF a hao ha)]
    have hh := graph_fixed_rank_le (n := 1)
      (by simpa only [pow_one] using hF) (by decide)
    rw [pow_one] at hh
    exact hh
  exact (centralizer_rank_le_fixed_add_one InvolutionNormalForms.inner_injective a).trans
    (Nat.add_le_add_right hfixed 1)

end SymplecticConjugatePair.Ambient.AutomorphismCentralizers
