module
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CubicIntersectionRankLower

/-!
# Cubic rank obstruction for nonnormal ordinary components

A component and a distinct conjugate commute, and their intersection embeds
in the original component center. If that center has at most three elements,
three-rank at least two in the component forces ambient three-rank at least
three. Thus a nonnormal component in a strongly quasithin group has
three-rank at most one. The same bound passes to its actual central quotient
by the odd-prime cyclic-Sylow theorem.

This preserves the scalar kernel in the linear/unitary degree-three branches
of the A.3.8 outer-group inspection. Source: Aschbacher--Smith A.3.8(3),
printed pp.45–46, with the central-product rank argument of A.2.12(II).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
variable {G : Type*} [Group G] [Finite G]

/-- A center of order at most three allows the full cubic intersection bound. -/
theorem component_normal_of_three_rank
    (hG : primeRank 3 G ≤ 2) {B : Subgroup G} (hB : IsComponent G B)
    (hZ : Nat.card (center B) ≤ 3) (hr : 2 ≤ primeRank 3 B) : B.Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  let C := B.map (MulAut.conj g).toMonoidHom
  have hc : B ≤ centralizer (C : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (hB.commutator_eq_bot_of_ne (hB.map_conj g) (Ne.symm hne))
  let f : (B ⊓ C : Subgroup G) → center B := fun x =>
    ⟨⟨x,x.property.1⟩,mem_center_iff.mpr (fun y => Subtype.ext (hc y.property x x.property.2).symm)⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : center B => ((z : B) : G)) he)
  have hi : Nat.card (B ⊓ C : Subgroup G) ≤ 3 :=
    (Nat.card_le_card_of_injective f hf).trans hZ
  have hrC : 2 ≤ primeRank 3 C := by
    exact hr.trans_eq (primeRank_equiv 3 ((MulAut.conj g).subgroupMap B))
  have hh := three_le_primeRank_of_cubic_intersection B C hc hi hr hrC
  omega

/-- Nonnormality forces cubic rank at most one in the original component
and in its literal central quotient. -/
theorem nonnormal_component_three_rank
    (hG : primeRank 3 G ≤ 2) {B : Subgroup G} (hB : IsComponent G B)
    (hZ : Nat.card (center B) ≤ 3) (hn : ¬ B.Normal) :
    primeRank 3 B ≤ 1 ∧ primeRank 3 (B ⧸ center B) ≤ 1 := by
  have hr : primeRank 3 B ≤ 1 := by
    by_contra! hh
    exact hn (component_normal_of_three_rank hG hB hZ (by omega))
  exact ⟨hr,(PrimeRank.le_of_surjective_of_source_le_one (by decide : (3 : ℕ) ≠ 2)
    (QuotientGroup.mk' (center B)) (QuotientGroup.mk'_surjective _) hr).trans hr⟩

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
