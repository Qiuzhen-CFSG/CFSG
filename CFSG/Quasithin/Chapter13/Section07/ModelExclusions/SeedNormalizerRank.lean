module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedTransitivity
public import Theory.Quasithin.TwoKernelSubgroupRank
/-!
# Model stabilizer ranks on the original seed normalizer

The seed contains V₁, so its image in U_H/V₁ has exactly the original seed
as preimage. A subgroup stabilizing that linear image therefore normalizes
V₃ itself. Pullback through the prescribed K/O₂(K) coordinates preserves
three-rank, since its kernel is a two-group. This gives the original
N_K(V₃) rank directly from the actual model plane stabilizer.

Source: Aschbacher–Smith, 13.7.6(3b), printed p.939.
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

omit [Finite G] in
private theorem vector_mem_seed_iff (h13 : V₁ ≤ V₃) (u : Section08.Source.UH H V₃) :
    vector H V₃ V₁ u ∈ sectionImage H V₃ V₁ V₃ ↔ (u : G) ∈ V₃ := by
  constructor
  · rintro ⟨w,hw,he⟩
    let q := QuotientGroup.mk' (V₁.subgroupOf (Section08.Source.UH H V₃))
    have hq : q w = q u := he
    have hk : w⁻¹ * u ∈ V₁.subgroupOf (Section08.Source.UH H V₃) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (w⁻¹ * u) = 1
      rw [map_mul,map_inv,hq,inv_mul_cancel]
    have hm := V₃.mul_mem hw (h13 hk)
    change (w : G) * ((w : G)⁻¹ * (u : G)) ∈ V₃ at hm
    simpa only [mul_inv_cancel_left] using hm
  · intro hu
    exact ⟨u,hu,rfl⟩

/-- A model seed stabilizer pulls back to the literal original component normalizer. -/
theorem seed_normalizer_rank_of_model
    {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
    (h13 : V₁ ≤ V₃) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E)
    (he : ∀ k : K, ∀ v,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v)) :
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) =
      primeRank 3 (subspaceStabilizer σ ((sectionImage H V₃ V₁ V₃).map eV.toLinearMap)) := by
  let P := sectionImage H V₃ V₁ V₃
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let S := subspaceStabilizer σ (P.map eV.toLinearMap)
  let N := S.comap q
  have hnormal : N.map K.subtype ≤ normalizer (V₃ : Set G) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨k,hk,rfl⟩ x hx
    let u : Section08.Source.UH H V₃ := ⟨x,le_conjugateSpanBy V₃ H hx⟩
    have hu : vector H V₃ V₁ u ∈ P := (vector_mem_seed_iff h13 u).mpr hx
    have hm := (hk (eV (vector H V₃ V₁ u))).mpr (Submodule.mem_map_of_mem hu)
    change σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV (vector H V₃ V₁ u)) ∈ P.map eV.toLinearMap at hm
    rw [← he k] at hm
    have hm' : ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))
        (vector H V₃ V₁ u) ∈ P := by
      obtain ⟨w,hw,hew⟩ := hm
      exact eV.injective hew ▸ hw
    rw [hρ] at hm'
    exact (vector_mem_seed_iff h13 _).mp hm'
  have hmap : N.map K.subtype = K ⊓ normalizer (V₃ : Set G) := by
    apply le_antisymm (le_inf (map_subtype_le N) hnormal)
    intro k hk
    change k ∈ K ∧ k ∈ normalizer (V₃ : Set G) at hk
    refine ⟨⟨k,hk.1⟩,?_,rfl⟩
    have hn : (⟨k,hk.1⟩ : K) ∈ N := by
      change ∀ v, σ (eK (QuotientGroup.mk' (pCore 2 K) ⟨k,hk.1⟩)) v ∈ P.map eV.toLinearMap ↔ v ∈ P.map eV.toLinearMap
      intro v
      obtain ⟨w,rfl⟩ := eV.surjective v
      rw [← he ⟨k,hk.1⟩ w]
      constructor
      · rintro ⟨u,hu,huv⟩
        have hew := eV.injective huv
        have hm := sectionImage_invariant ρ hρ V₃ (inclusion hKH (⟨k,hk.1⟩ : K)⁻¹)
          ((normalizer (V₃ : Set G)).inv_mem hk.2) u hu
        rw [hew] at hm
        simp only [map_inv,← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
          Module.End.one_apply] at hm
        exact Submodule.mem_map_of_mem hm
      · rintro ⟨u,hu,huv⟩
        have hew := eV.injective huv
        rw [← hew]
        exact Submodule.mem_map_of_mem
          (sectionImage_invariant ρ hρ V₃ (inclusion hKH ⟨k,hk.1⟩) hk.2 u hu)
    exact hn
  have hker : IsPGroup 2 q.ker := by
    have hk : q.ker = pCore 2 K := by
      dsimp only [q]
      rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    rw [hk]
    exact pCore_isPGroup
  rw [← hmap,← primeRank_congr 3 (N.equivMapOfInjective K.subtype K.subtype_injective)]
  exact primeRank_comap_eq_of_isTwoGroup_ker 3 (by decide) q
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)) hker S
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
