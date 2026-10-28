module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.NaturalBaumann
/-!
# Marking the actual reduced natural quotient

The proved Baumann image lies in the original natural SL₂ layer. Hence the
whole K Baum(T) action has precisely that image. Faithfulness of the natural
module gives its quotient map, and conjugacy of the actual Sylow image to
the upper root changes the projection by the same matrix. The original
central-cover kernel and literal conjugation formula are preserved.

Source: Aschbacher–Smith C.5.4(2),(4), printed p.155.
-/
public section
open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

theorem natural_marked_quotient (K T : Subgroup G) (hn : S T ≤ normalizer (K : Set G))
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K τ)
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd)
    (β : normalizer (K : Set G) →* MulAut (Multiplicative (Fin 2 → F)))
    (hβ : ∀ a u, β a (modelProjection m u) = modelProjection m (normalizerConjugate a u))
    (hβker : β.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)))
    (hβK : (K.subgroupOf (normalizer (K : Set G))).map β = τ.range)
    (hβS : ((S T).subgroupOf (normalizer (K : Set G))).map β ≤ τ.range)
    (hSylow : Chapter1.IsSylowIn 2 (S T) (K ⊔ S T)) :
    ∃ (q : (K ⊔ S T : Subgroup G) →* Matrix.SpecialLinearGroup (Fin 2) F)
      (π : U K →* Multiplicative (Fin 2 → F)),
      Function.Surjective q ∧ Function.Surjective π ∧
      q.ker = (centralizer (U K : Set G)).subgroupOf (K ⊔ S T) ∧
      (∀ u, π u = 1 ↔ (u : G) ∈ centralizer (K : Set G)) ∧
      ((S T).subgroupOf (K ⊔ S T)).map q = upperUnipotent F ∧
      (K.subgroupOf (K ⊔ S T)).map q = ⊤ ∧
      ∀ (z : (K ⊔ S T : Subgroup G)) (u : U K),
        π (normalizerConjugate (inclusion (sup_le K.le_normalizer hn) z) u) =
          τ (q z) (π u) := by
  let B := K ⊔ S T
  let N := normalizer (K : Set G)
  have hBN : B ≤ N := sup_le K.le_normalizer hn
  have hBrange : (B.subgroupOf N).map β = τ.range := by
    rw [subgroupOf_sup K.le_normalizer hn,Subgroup.map_sup,hβK,sup_eq_left.mpr hβS]
  let b := β.comp (inclusion hBN)
  have hbrange : b.range = τ.range := by
    calc
      _ = (B.subgroupOf N).map β := by
        ext z
        constructor
        · rintro ⟨v,rfl⟩; exact ⟨inclusion hBN v,v.property,rfl⟩
        · rintro ⟨v,hv,rfl⟩; exact ⟨⟨v,hv⟩,rfl⟩
      _ = _ := hBrange
  let e := MonoidHom.ofInjective (natural_action_injective τ hτ)
  let q₀ : B →* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.symm.toMonoidHom.comp (b.codRestrict τ.range (fun z => hbrange ▸ show b z ∈ b.range from ⟨z,rfl⟩))
  have hqτ (z : B) : τ (q₀ z) = b z := MonoidHom.apply_ofInjective_symm (natural_action_injective τ hτ) _
  have hqK : (K.subgroupOf B).map q₀ = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,hkg⟩ := (hβK.symm ▸ (show τ g ∈ τ.range from ⟨g,rfl⟩) : τ g ∈ (K.subgroupOf N).map β)
    let k₀ : B := ⟨k,(show K ≤ B from le_sup_left) hk⟩
    refine ⟨k₀,hk,?_⟩
    apply natural_action_injective τ hτ
    exact (hqτ k₀).trans hkg
  have hqsurj : Function.Surjective q₀ := MonoidHom.range_eq_top.mp
    (top_unique (hqK ▸ map_le_range q₀ (K.subgroupOf B)))
  have hqker : q₀.ker = (centralizer (U K : Set G)).subgroupOf B := by
    ext z
    change q₀ z = 1 ↔ _
    rw [← (natural_action_injective τ hτ).eq_iff,τ.map_one,hqτ]
    change inclusion hBN z ∈ β.ker ↔ _
    rw [hβker]
    rfl
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
  let π := (τ g).toMonoidHom.comp (modelProjection m)
  refine ⟨q,π,(MulAut.conj g).surjective.comp hqsurj,
    (τ g).surjective.comp (modelProjection_surjective m),?_,?_,?_,?_,?_⟩
  · ext z
    change (MulAut.conj g) (q₀ z) = 1 ↔ _
    rw [(MulAut.conj g).map_eq_one_iff]
    exact SetLike.ext_iff.mp hqker z
  · intro u
    change τ g (modelProjection m u) = 1 ↔ _
    rw [(τ g).map_eq_one_iff,modelProjection_kernel]
  · change ((S T).subgroupOf B).map ((MulAut.conj g).toMonoidHom.comp q₀) = _
    rw [← map_map,hSP,hPg]
  · change (K.subgroupOf B).map ((MulAut.conj g).toMonoidHom.comp q₀) = _
    rw [← map_map,hqK,map_top_of_surjective _ (MulAut.conj g).surjective]
  · intro z u
    change τ g (modelProjection m (normalizerConjugate (inclusion hBN z) u)) =
      τ ((MulAut.conj g) (q₀ z)) (τ g (modelProjection m u))
    rw [← hβ]
    change τ g (b z (modelProjection m u)) = _
    rw [← hqτ]
    simp only [MulAut.conj_apply,map_mul,map_inv,MulAut.mul_apply,MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
