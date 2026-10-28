module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianActors
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Tensor.Quadratic
public import Theory.Representation.HermitianTensorThree.QuadraticSubspaces

/-!
# Large-subspace quadratic bounds for the Hermitian normalizer

An elementary actor of rank greater than 2n+1 lies in the inner image.
Its quadratic identity extends from a binary subspace of dimension greater
than 8n to the whole fixed-field module; the inner quadratic rank bound
then gives rank at most n. The final export retains the supplied action,
coordinates and injective normalizer map for ambient applications.

Source: Aschbacher--Smith H.4.4 and K.3.2.4, printed pp.381,455--456.
-/

open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable (n : ℕ) [NeZero n]

/-- An elementary inner quadratic actor has rank at most n. -/
theorem inner_quadratic_rank_le
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hA : IsElementaryTwo A)
    (hAL : A ≤ binaryImage n) (hq : IsQuadratic (UnipotentRadicals.ambientAction n) A) :
    rank A ≤ n := by
  let : Group.IsPerfect (Cover n) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect (binaryImage n) := Group.IsPerfect.ofSurjective
    (f := (binaryActionHom n).rangeRestrict) (binaryActionHom n).rangeRestrict_surjective
  have hM : SourceOvergroup n (binaryImage n) := by
    rw [SourceOvergroup,solvableResidual_eq_top,← MonoidHom.range_eq_map,range_subtype]
  let B := A.subgroupOf (binaryImage n)
  have hB : IsElementaryTwo B := by
    let := hA.2
    exact ⟨fun hz => hA.1 (by
      have hm := map_subgroupOf_eq_of_le hAL
      change B.map (binaryImage n).subtype = A at hm
      rw [hz,Subgroup.map_bot] at hm
      exact hm.symm), IsElementaryAbelian.subgroupOf hAL⟩
  have hr := ChapterK.Linear.Tensor.inner_quadratic_rank_le n (binaryImage n) hM B hB
    (fun x _ => x.property) (fun a ha b hb X => hq a.val ha b.val hb X)
  have hm : B.map (binaryImage n).subtype = A := map_subgroupOf_eq_of_le hAL
  rw [← hm,rank_map_injective (binaryImage n).subtype Subtype.val_injective]
  exact hr

end
end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian

namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
public noncomputable section
variable (n : ℕ) [NeZero n]

/-- An elementary normalizer actor quadratic on a binary subspace of
dimension greater than 8n has rank at most 2n+1. -/
theorem normalizer_actor_rank_le_of_large_quadratic_subspace
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ binaryNormalizer n)
    (W : Submodule (ZMod 2) (Space n)) (hW : 8*n < Module.finrank (ZMod 2) W)
    (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ X ∈ W, a (b X - X) = b X - X) :
    rank A ≤ 2*n+1 := by
  by_contra! hr
  have hAL := large_elementary_le_image n A hAN hr
  have hA : IsElementaryTwo A := ⟨fun hz => by simp [hz] at hr, inferInstance⟩
  have hq' := Representation.HermitianTensorThree.QuadraticSubspaces.quadratic_of_large_subspace
    n A hAL W hW hq
  have hbound := inner_quadratic_rank_le n A hA hAL hq'
  omega

/-- Transport the preceding bound through the given faithful coordinates. -/
theorem actor_rank_le_of_coordinates_on_large_subspace
    {X U : Type*} [Group X] [Finite X] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) X U)
    (e : U ≃ₗ[ZMod 2] Space n)
    (j : X →* binaryNormalizer n) (hj : Function.Injective j)
    (he : ∀ a v, e (ρ a v) = overgroupAction n (binaryNormalizer n) (j a) (e v))
    (A : Subgroup X) [IsElementaryAbelian 2 A]
    (W : Submodule (ZMod 2) U) (hW : 8*n < Module.finrank (ZMod 2) W)
    (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ v ∈ W, ρ a (ρ b v - v) = ρ b v - v) :
    rank A ≤ 2*n+1 := by
  let f := (binaryNormalizer n).subtype.comp j
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hf : Function.Injective f := Subtype.val_injective.comp hj
  have hbound := normalizer_actor_rank_le_of_large_quadratic_subspace n (A.map f)
    (by rintro _ ⟨a,_,rfl⟩; exact (j a).property) (W.map e.toLinearMap)
    (by rwa [e.finrank_map_eq]) (by
      rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨v,hv,rfl⟩
      have h := congrArg e (hq a ha b hb v hv)
      rw [he,map_sub,he] at h
      exact h)
  rwa [rank_map_injective f hf] at hbound
end
end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
