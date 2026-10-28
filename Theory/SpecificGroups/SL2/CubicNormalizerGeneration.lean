module
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Actor

/-!
# A cubic normalizer and a binary Sylow generate SL₂(4)

The normalizer of a cubic subgroup of SL₂(4) inverts a nonidentity
cubic element. It therefore cannot lie in the Sylow normalizer: the
latter has abelian diagonal quotient and a two-group kernel. The
rank-one overgroup theorem then gives generation. Sylow conjugacy
lifts the cubic normalizer through any two-group kernel, retaining
the supplied quotient map and original Sylow subgroup.

Source: Aschbacher--Smith, 5.1.23, printed pp.645--646,
refs/quasithin.pdf; used for its field-four chief-factor count.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup
variable {F X : Type*} [Field F] [Finite F] [CharP F 2] [Group X] [Finite X]

private theorem cubic_normalizer_not_le_borel (hF : Nat.card F = 4)
    (P : Sylow 2 SL(2,F)) (C : Subgroup SL(2,F)) (hC : Nat.card C = 3)
    (hCP : C ≤ normalizer (P : Set SL(2,F))) :
    ¬ normalizer (C : Set SL(2,F)) ≤ normalizer (P : Set SL(2,F)) := by
  let e := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  obtain ⟨t,ht,x,hx,htx⟩ := alternatingGroup.FiveLocalGeometry.exists_noncommuting_normalizer e C hC
  intro hn
  obtain ⟨f,_,hf⟩ := exists_sylowNormalizer_diagonal (MonoidHom.id SL(2,F))
    Function.surjective_id P (by simp)
  have hd : Disjoint (P : Subgroup SL(2,F)) C := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk,hC]
    exact (by decide : Nat.Coprime 2 3).pow_left k
  let a : normalizer (P : Set SL(2,F)) := ⟨t,hn ht⟩
  let b : normalizer (P : Set SL(2,F)) := ⟨x,hCP hx⟩
  have hcommP : ⁅t,x⁆ ∈ P := by
    apply (hf ⁅a,b⁆).mp
    simp only [commutatorElement_def]
    simp
  have hcommC : ⁅t,x⁆ ∈ C := by
    exact C.mul_mem ((mem_normalizer_iff.mp ht x).mp hx) (C.inv_mem hx)
  exact htx (commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hd hcommP hcommC))

/-- A binary SL₂(4) Sylow and the normalizer of its cubic complement generate. -/
theorem cubic_normalizer_sup_sylow (hF : Nat.card F = 4)
    (q : X →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Sylow 2 X) (C : Subgroup X) (hC : Nat.card C = 3)
    (hCP : C ≤ normalizer (P : Set X)) :
    (P : Subgroup X) ⊔ normalizer (C : Set X) = ⊤ := by
  let S := P.mapSurjective hq
  let D := C.map q
  have hD : Nat.card D = 3 := GLS3.Chapter5.cubic_image_card_of_two_kernel q hk C hC
  have hDS : D ≤ normalizer (S : Set SL(2,F)) := (map_mono hCP).trans (le_normalizer_map q)
  let e := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let R : Sylow 3 SL(2,F) := Sylow.ofCard D (by
    rw [hD,Nat.card_congr e.toEquiv,alternatingGroup.FiveLocalGeometry.card]
    decide +kernel)
  obtain ⟨Q,hCQ⟩ := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hC)).exists_le_sylow
  have hQR : Q.mapSurjective hq = R := by
    apply Sylow.ext
    exact R.is_maximal' (Q.mapSurjective hq).isPGroup' (map_mono hCQ)
  have hdis : Disjoint q.ker (Q : Subgroup X) :=
    IsPGroup.disjoint_of_ne 2 3 (by decide) q.ker (Q : Subgroup X) hk Q.isPGroup'
  have hi : Function.Injective (q.comp (Q : Subgroup X).subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    exact Subtype.ext (disjoint_def.mp hdis hx x.property)
  have hcard : Nat.card Q = 3 := by
    have he := Nat.card_congr (MonoidHom.ofInjective hi).toEquiv
    have hr : (q.comp (Q : Subgroup X).subtype).range = D := by
      rw [MonoidHom.range_comp,range_subtype]
      exact congrArg (fun Z : Sylow 3 SL(2,F) => (Z : Subgroup SL(2,F))) hQR
    rwa [hr,hD] at he
  have hQC : (Q : Subgroup X) = C := (eq_of_le_of_card_ge hCQ (by rw [hcard,hC])).symm
  have hN : (normalizer (C : Set X)).map q = normalizer (D : Set SL(2,F)) := by
    have hh := Q.normalizer_map_surjective q hq
    change (normalizer ((Q : Subgroup X) : Set X)).map q =
      normalizer (((Q : Subgroup X).map q) : Set SL(2,F)) at hh
    rw [hQC] at hh
    exact hh
  let J := (P : Subgroup X) ⊔ normalizer (C : Set X)
  have hJ : J.map q = ⊤ := by
    by_contra hne
    have hle := overgroup_le_sylowNormalizer S (map_mono (show (P : Subgroup X) ≤ J from le_sup_left)) hne
    have hNC : normalizer (D : Set SL(2,F)) ≤ normalizer (S : Set SL(2,F)) := by
      rw [← hN]
      exact (map_mono (show normalizer (C : Set X) ≤ J from le_sup_right)).trans hle
    exact cubic_normalizer_not_le_borel hF S D hD hDS hNC
  have hker : q.ker ≤ J := (hk.le_sylow_of_normal P).trans le_sup_left
  have he := congrArg (comap q) hJ
  rwa [comap_map_eq_self hker,comap_top] at he
end Matrix.SpecialLinearGroup
