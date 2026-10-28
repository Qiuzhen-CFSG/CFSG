module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Restricting full automorphism actions to subgroup pairs

For two subgroups S and R of G, restrict their common stabilizer in Aut(G)
to R. Its image consists exactly of the automorphisms of R extending to an
automorphism of G preserving S. A surjective realization of Aut(G) has the
same restriction image; its kernel on R is the pointwise fixer.

For conjugation by the full normalizer of an embedded group, the preimage
stabilizer is exactly the intersection of the normalizers of the embedded
subgroups. This identifies the maps used in concrete local calculations,
including outer automorphisms.

The proof uses subgroup restriction and surjectivity, without an automorphism
catalogue. Application: Aschbacher–Smith, Proposition 1.3.4, printed p.511,
and the Held local branch in GLS3, Table 5.3p.
-/

@[expose] public section

open scoped Pointwise

namespace Subgroup

variable {G A : Type*} [Group G] [Group A]

/-- The common setwise stabilizer in the full automorphism group. -/
def automorphismPairStabilizer (S R : Subgroup G) : Subgroup (MulAut G) :=
  MulAction.stabilizer (MulAut G) S ⊓ MulAction.stabilizer (MulAut G) R

/-- Setwise preservation expressed as an elementwise equivalence. -/
theorem mem_automorphism_stabilizer_iff (S : Subgroup G) (a : MulAut G) :
    a ∈ MulAction.stabilizer (MulAut G) S ↔ ∀ x, a x ∈ S ↔ x ∈ S := by
  constructor
  · intro h x
    change a • S = S at h
    simpa only [h, MulAut.smul_def] using
      (smul_mem_pointwise_smul_iff (a := a) (S := S) (x := x))
  · intro h
    change S.map a.toMonoidHom = S
    ext x
    rw [mem_map_equiv]
    simpa only [a.apply_symm_apply] using (h (a.symm x)).symm

theorem mem_automorphismPairStabilizer_iff (S R : Subgroup G) (a : MulAut G) :
    a ∈ automorphismPairStabilizer S R ↔
      (∀ x, a x ∈ S ↔ x ∈ S) ∧ (∀ x, a x ∈ R ↔ x ∈ R) := by
  exact and_congr (mem_automorphism_stabilizer_iff S a)
    (mem_automorphism_stabilizer_iff R a)

/-- Restriction of every extending automorphism, with no innerness condition. -/
def pairRestriction (S R : Subgroup G) : automorphismPairStabilizer S R →* MulAut R where
  toFun a := (a.val.subgroupMap R).trans (MulEquiv.subgroupCongr a.property.2)
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

@[simp] theorem pairRestriction_apply (S R : Subgroup G)
    (a : automorphismPairStabilizer S R) (x : R) :
    (pairRestriction S R a x : G) = a.val x := rfl

/-- Exact extension criterion for the restriction image. -/
theorem mem_pairRestriction_range_iff (S R : Subgroup G) (a : MulAut R) :
    a ∈ (pairRestriction S R).range ↔
      ∃ b : MulAut G, (∀ x, b x ∈ S ↔ x ∈ S) ∧ ∀ x : R, (a x : G) = b x := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b.val, (mem_automorphism_stabilizer_iff S b.val).mp b.property.1,
      fun _ => rfl⟩
  · rintro ⟨b, hS, hR⟩
    have hb : b ∈ automorphismPairStabilizer S R := by
      rw [mem_automorphismPairStabilizer_iff]
      refine ⟨hS, fun x => ⟨?_, ?_⟩⟩
      · intro hx
        let y : R := ⟨b x, hx⟩
        have hy : b (a.symm y : R) = b x := by
          rw [← hR]
          exact congrArg Subtype.val (a.apply_symm_apply y)
        exact b.injective hy ▸ (a.symm y).property
      · intro hx
        rw [← hR ⟨x, hx⟩]
        exact (a ⟨x, hx⟩).property
    refine ⟨⟨b, hb⟩, ?_⟩
    ext x
    exact (hR x).symm

/-- All actors whose automorphisms preserve both subgroups. -/
def actingPairStabilizer (ρ : A →* MulAut G) (S R : Subgroup G) : Subgroup A :=
  (automorphismPairStabilizer S R).comap ρ

/-- The actual map from preserving actors to the full pair stabilizer. -/
def actingPairMap (ρ : A →* MulAut G) (S R : Subgroup G) :
    actingPairStabilizer ρ S R →* automorphismPairStabilizer S R :=
  (ρ.comp (actingPairStabilizer ρ S R).subtype).codRestrict _ (fun a => a.property)

/-- Restrict the given actor homomorphism to the second subgroup. -/
def actingPairRestriction (ρ : A →* MulAut G) (S R : Subgroup G) :
    actingPairStabilizer ρ S R →* MulAut R :=
  (pairRestriction S R).comp (actingPairMap ρ S R)

@[simp] theorem actingPairRestriction_apply (ρ : A →* MulAut G) (S R : Subgroup G)
    (a : actingPairStabilizer ρ S R) (x : R) :
    (actingPairRestriction ρ S R a x : G) = ρ a.val x := rfl

/-- Full realization remains surjective on each pair stabilizer. -/
theorem actingPairMap_surjective (ρ : A →* MulAut G) (hρ : Function.Surjective ρ)
    (S R : Subgroup G) : Function.Surjective (actingPairMap ρ S R) := by
  intro b
  obtain ⟨a, ha⟩ := hρ b.val
  refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
  change ρ a ∈ automorphismPairStabilizer S R
  rw [ha]
  exact b.property

/-- A full realization computes the entire restriction image. -/
theorem actingPairRestriction_range (ρ : A →* MulAut G) (hρ : Function.Surjective ρ)
    (S R : Subgroup G) :
    (actingPairRestriction ρ S R).range = (pairRestriction S R).range := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨actingPairMap ρ S R b, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := actingPairMap_surjective ρ hρ S R b
    exact ⟨c, rfl⟩

/-- The restriction kernel is the pointwise fixer of the second subgroup. -/
theorem mem_actingPairRestriction_ker_iff (ρ : A →* MulAut G) (S R : Subgroup G)
    (a : actingPairStabilizer ρ S R) :
    a ∈ (actingPairRestriction ρ S R).ker ↔ ∀ x : R, ρ a.val x = x := by
  change actingPairRestriction ρ S R a = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun f : MulAut R => (f x : G)) h
  · intro h
    ext x
    exact h x

/-- Preservation inside an embedded group is ambient normalization of its image. -/
theorem normalizerAction_mem_stabilizer_iff (H : Subgroup A) (S : Subgroup H)
    (a : normalizer (H : Set A)) :
    H.normalizerMonoidHom a ∈ MulAction.stabilizer (MulAut H) S ↔
      a.val ∈ normalizer (S.map H.subtype : Set A) := by
  rw [mem_normalizer_iff_map_conj_eq]
  change S.map (H.normalizerMonoidHom a).toMonoidHom = S ↔ _
  rw [map_map]
  change S.map (H.normalizerMonoidHom a).toMonoidHom = S ↔
    S.map (H.subtype.comp (H.normalizerMonoidHom a).toMonoidHom) = S.map H.subtype
  rw [← map_map]
  exact ⟨congrArg (map H.subtype), fun h => map_injective H.subtype_injective h⟩

/-- The preserving permutation actors are the two literal ambient normalizers. -/
theorem mem_normalizer_actingPairStabilizer_iff (H : Subgroup A) (S R : Subgroup H)
    (a : normalizer (H : Set A)) :
    a ∈ actingPairStabilizer H.normalizerMonoidHom S R ↔
      a.val ∈ normalizer (S.map H.subtype : Set A) ∧
      a.val ∈ normalizer (R.map H.subtype : Set A) := by
  exact and_congr (normalizerAction_mem_stabilizer_iff H S a)
    (normalizerAction_mem_stabilizer_iff H R a)

end Subgroup
