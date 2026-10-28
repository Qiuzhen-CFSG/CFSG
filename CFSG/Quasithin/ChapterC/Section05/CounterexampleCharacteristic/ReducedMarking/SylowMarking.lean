module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.NaturalSetup
/-!
# Simultaneous Sylow and module marking

Conjugate the image of the actual Baumann Sylow subgroup onto the upper
root and change the module projection by the same natural matrix. This
preserves the exact kernels and original conjugation formula, including
when the block image itself is only A₃.

Source: Aschbacher–Smith C.5.4(2), printed p.155.
-/
public section
open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem marked_sylow_quotient (K T : Subgroup G) (hn : S T ≤ normalizer (K : Set G))
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (q₀ : (K ⊔ S T : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) F)
    (π₀ : U K →* Multiplicative (Fin 2 → F))
    (hqsurj : Function.Surjective q₀) (hπ₀ : Function.Surjective π₀)
    (hqker : q₀.ker = (centralizer (U K : Set G)).subgroupOf (K ⊔ S T))
    (hπker : ∀ u, π₀ u = 1 ↔ (u : G) ∈ centralizer (K : Set G))
    (he : ∀ (z : (K ⊔ S T : Subgroup G)) (u : U K),
      π₀ (normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) u) = τ (q₀ z) (π₀ u))
    (hSylow : Chapter1.IsSylowIn 2 (S T) (K ⊔ S T)) :
    ∃ (q : (K ⊔ S T : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) F)
      (π : U K →* Multiplicative (Fin 2 → F)),
      Function.Surjective q ∧ Function.Surjective π ∧
      q.ker = (centralizer (U K : Set G)).subgroupOf (K ⊔ S T) ∧
      (∀ u, π u = 1 ↔ (u : G) ∈ centralizer (K : Set G)) ∧
      ((S T).subgroupOf (K ⊔ S T)).map q = upperUnipotent F ∧
      ∀ (z : (K ⊔ S T : Subgroup G)) (u : U K),
        π (normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) u) = τ (q z) (π u) := by
  let B := K ⊔ S T
  have hBN : B ≤ normalizer (K : Set G) := sup_le K.le_normalizer hn
  obtain ⟨P,hP⟩ := hSylow
  let P₀ := P.mapSurjective (f := q₀) hqsurj
  have hSP : ((S T).subgroupOf B).map q₀ = (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    have hi : (S T).subgroupOf B = (P : Subgroup B) := by
      apply map_injective B.subtype_injective
      rw [map_subgroupOf_eq_of_le (show S T ≤ B from le_sup_right),hP]
    rw [hi]
    rfl
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F) P₀ (upperUnipotentSylow F 2)
  have hPg : (P₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map (MulAut.conj g).toMonoidHom = upperUnipotent F :=
    congrArg (fun P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) => (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) hg
  let q := (MulAut.conj g).toMonoidHom.comp q₀
  let π := (τ g).toMonoidHom.comp π₀
  refine ⟨q,π,(MulAut.conj g).surjective.comp hqsurj,
    (τ g).surjective.comp hπ₀,?_,?_,?_,?_⟩
  · ext z
    change (MulAut.conj g) (q₀ z) = 1 ↔ _
    rw [(MulAut.conj g).map_eq_one_iff]
    exact SetLike.ext_iff.mp hqker z
  · intro u
    change τ g (π₀ u) = 1 ↔ _
    rw [(τ g).map_eq_one_iff,hπker]
  · change ((S T).subgroupOf B).map ((MulAut.conj g).toMonoidHom.comp q₀) = _
    rw [← map_map,hSP,hPg]
  · intro z u
    change τ g (π₀ (normalizerConjugate (inclusion hBN z) u)) =
      τ ((MulAut.conj g) (q₀ z)) (τ g (π₀ u))
    rw [he]
    simp only [MulAut.conj_apply,map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
