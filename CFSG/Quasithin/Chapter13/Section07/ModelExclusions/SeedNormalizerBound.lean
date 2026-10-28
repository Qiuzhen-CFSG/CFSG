module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
public import Theory.Quasithin.CoprimeRank
/-!
# A full faithful model bounds the original seed normalizer

Pull back the model subspace stabilizer using the actual map H→H/O₂(H).
The kernel on every subgroup is a two-group, so its three-rank is bounded
by the model stabilizer. The module map may be a quotient: seed invariance
alone suffices for this upper bound.

Source: Aschbacher–Smith, 13.7.6(3a), printed p.939.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.TransvectionRecognition
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
variable {G : Type*} [Group G] [Finite G]
  {H V₃ V₁ K : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
/-- The literal seed normalizer has rank at most that of its image-plane stabilizer. -/
theorem seed_normalizer_rank_le_of_full_action
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
    (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (σ : Representation (ZMod 2) A E)
    (f : Section08.Source.Hstar H →* A) (hf : Function.Injective f)
    (F : Additive (Section08.Source.Utilde H V₃ V₁) →ₗ[ZMod 2] E)
    (he : ∀ a u, F (ρ a u) = σ (f a) (F u)) :
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) ≤
      primeRank 3 (subspaceStabilizer σ ((sectionImage H V₃ V₁ V₃).map F)) := by
  let N := K ⊓ normalizer (V₃ : Set G)
  let i : N →* H := inclusion (inf_le_left.trans hKH)
  let q : N →* A := f.comp ((QuotientGroup.mk' (pCore 2 H)).comp i)
  let P := sectionImage H V₃ V₁ V₃
  let S := subspaceStabilizer σ (P.map F)
  have hs (n : N) : q n ∈ S := by
    intro v
    constructor
    · rintro ⟨u,hu,huv⟩
      have hm := sectionImage_invariant ρ hρ V₃ (i n⁻¹) ((normalizer (V₃ : Set G)).inv_mem n.property.2) u hu
      refine ⟨_,hm,?_⟩
      rw [he]
      change σ (q n⁻¹) (F u) = v
      change F u = σ (q n) v at huv
      rw [huv,map_inv,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply]
    · rintro ⟨u,hu,rfl⟩
      have hm := sectionImage_invariant ρ hρ V₃ (i n) n.property.2 u hu
      refine ⟨_,hm,?_⟩
      exact he _ _
  let qS : N →* S := q.codRestrict S hs
  have hker : IsPGroup 2 qS.ker := by
    have hk : qS.ker = (pCore 2 H).comap i := by
      ext n
      change (⟨q n,hs n⟩ : S) = 1 ↔ i n ∈ pCore 2 H
      rw [Subtype.ext_iff]
      change f (QuotientGroup.mk' (pCore 2 H) (i n)) = 1 ↔ _
      rw [← map_one f,hf.eq_iff]
      exact QuotientGroup.eq_one_iff _
    rw [hk]
    exact (pCore_isPGroup (p := 2) (G := H)).comap_of_injective i
      (inclusion_injective (inf_le_left.trans hKH))
  apply primeRank_le_of_coprime_ker 3 qS
  obtain ⟨n,hn⟩ := hker.exists_card_eq
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
