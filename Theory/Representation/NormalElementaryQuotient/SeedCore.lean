module

public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PCoreRestriction

/-!
# The core of a seed stabilizer in a conjugation quotient

The pointwise stabilizer of a subgroup of a normal elementary abelian group
pulls back to its actual centralizer. A normal two-subgroup of that centralizer
therefore maps into the stabilizer's two-core, also after restricting the actor.
The proof keeps the quotient map and the original seed subgroup explicit.

Source application: Aschbacher--Smith 15.1.28, printed p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
  (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))

/-- The pointwise action kernel pulls back to the literal seed centralizer. -/
theorem subspaceKernel_comap (P : Subgroup V) :
    (subspaceKernel (V := Additive V) (representation V q hq hker) (subspace V P) ⊤).comap q =
      centralizer (P.map V.subtype : Set G) := by
  ext g
  constructor
  · rintro ⟨_, hg⟩ z ⟨v, hv, rfl⟩
    have he := congrArg (fun w : Additive V => (w.toMul : G))
      (hg (Additive.ofMul v) hv)
    rw [representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    refine ⟨mem_top _, ?_⟩
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [representation_apply, ← hg v.toMul (mem_map_of_mem V.subtype hv),
      mul_inv_cancel_right]

/-- Surjectivity identifies the pointwise stabilizer with that centralizer image. -/
theorem subspaceKernel_eq_map_centralizer (P : Subgroup V) :
    subspaceKernel (V := Additive V) (representation V q hq hker) (subspace V P) ⊤ =
      (centralizer (P.map V.subtype : Set G)).map q := by
  rw [← subspaceKernel_comap V q hq hker P, map_comap_eq_self]
  rw [q.range_eq_top_of_surjective hq]
  exact le_top

/-- A normal two-subgroup of the seed centralizer maps into its two-core. -/
theorem image_le_seed_core (P : Subgroup V) (R : Subgroup G)
    (hp : IsPGroup 2 R) (hRC : R ≤ centralizer (P.map V.subtype : Set G))
    (hCR : centralizer (P.map V.subtype : Set G) ≤ normalizer (R : Set G)) :
    R.map q ≤ (subspaceKernel (V := Additive V) (representation V q hq hker) (subspace V P) ⊤).pCoreIn 2 := by
  rw [subspaceKernel_eq_map_centralizer V q hq hker P]
  exact le_pCoreIn_of_normalizes (hp.map q) (map_mono hRC)
    ((map_mono hCR).trans (R.le_normalizer_map q))

/-- The same core containment holds in every restricted actor. -/
theorem image_subgroupOf_le_seed_core (P : Subgroup V) (R : Subgroup G)
    (hp : IsPGroup 2 R) (hRC : R ≤ centralizer (P.map V.subtype : Set G))
    (hCR : centralizer (P.map V.subtype : Set G) ≤ normalizer (R : Set G))
    (B : Subgroup H) :
    (R.map q).subgroupOf B ≤
      (subspaceKernel (V := Additive V) ((representation V q hq hker).comp B.subtype) (subspace V P) ⊤).pCoreIn 2 := by
  let C := subspaceKernel (V := Additive V) (representation V q hq hker) (subspace V P) ⊤
  have hle := image_le_seed_core V q hq hker P R hp hRC hCR
  have he : subspaceKernel (V := Additive V) ((representation V q hq hker).comp B.subtype) (subspace V P) ⊤ =
      (C ⊓ B).subgroupOf B := by
    ext x
    simp only [mem_subspaceKernel, mem_top, true_and, mem_subgroupOf, mem_inf]
    exact ⟨fun hx => ⟨⟨mem_top _, hx⟩,x.property⟩,fun hx => hx.1.2⟩
  rw [he, pCoreIn_subgroupOf 2 (C ⊓ B) B inf_le_right]
  intro x hx
  exact inf_pCoreIn_le_of_le 2 (show C ⊓ B ≤ C from inf_le_left) ⟨⟨pCoreIn_le 2 C (hle hx),x.property⟩,hle hx⟩
end Representation.NormalElementaryQuotient
