module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SemilinearModel

/-!
# Aligning the full normalizer action with the genuine internal Sylow

The original C.5.4 assertion that S∩K is Sylow, together with internality
of the S-action, identifies its full image in the intrinsic SL₂ model.
Conjugating that Sylow and changing the quotient basis by the same matrix
marks the whole normalizer action with S-image the complete upper root.
The two independent C.5.4 inputs remain explicit, rather than imposing
innerness on the full ambient Sylow normalizer.

Source: Aschbacher–Smith, C.5.4(2),(4) and C.5.6(7), printed pp.155,159.
-/
@[expose] public section
open Subgroup Matrix.SpecialLinearGroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R K : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

structure FullNaturalModel (R K : Subgroup G) (F : Type*) [Field F] where
  tau : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F))
  natural : ∀ g v, (tau g v).toAdd = Matrix.mulVec g.val v.toAdd
  projection : U K →* Multiplicative (Fin 2 → F)
  surjective : Function.Surjective projection
  kernel : ∀ u, projection u = 1 ↔ (u : G) ∈ centralizer (K : Set G)
  normalizes : S R ≤ normalizer (K : Set G)
  action : normalizer (K : Set G) →* MulAut (Multiplicative (Fin 2 → F))
  equivariant : ∀ a u, action a (projection u) = projection (normalizerConjugate a u)
  action_kernel : action.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G))
  image : ((S R).subgroupOf (normalizer (K : Set G))).map action = (upperUnipotent F).map tau
  semilinear : ∀ a, ∃ σ : F ≃+* F, ∀ c v,
    (action a (Multiplicative.ofAdd (c • v))).toAdd = σ c • (action a (Multiplicative.ofAdd v)).toAdd

variable [Finite G] {E : Type*} [Field E]

/-- The supplied Sylow is the original S∩K. All full-normalizer coordinates
are constructed from the intrinsic model and the preceding internal action. -/
theorem Setup.full_natural_model
    (h : Setup R K E) (hi : h.coordinates.IsInternal)
    (hSylow : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = S R ⊓ K)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K τ)
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd) :
    Nonempty (FullNaturalModel R K F) := by
  classical
  let N := normalizer (K : Set G)
  obtain ⟨ρ,hρ,hker,himage,hsemi⟩ := exists_full_natural_model_action h.short τ m hτ
  have hρK (k : K) : ρ (inclusion K.le_normalizer k) = τ (modelActor m k) := by
    ext w
    obtain ⟨u,rfl⟩ := modelProjection_surjective m w
    rw [hρ,modelProjection_conjugate]
  obtain ⟨P,hP⟩ := hSylow
  have hPK (k : K) : k ∈ P ↔ (k : G) ∈ S R := by
    constructor
    · intro hk
      exact (hP ▸ mem_map_of_mem K.subtype hk).1
    · intro hk
      have hh : (k : G) ∈ (P : Subgroup K).map K.subtype := hP.symm ▸ ⟨hk,k.property⟩
      obtain ⟨l,hl,he⟩ := hh
      exact (K.subtype_injective he) ▸ hl
  let a := modelActor m
  have ha : Function.Surjective a := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let P' := P.mapSurjective (f := a) ha
  have hSi : ((S R).subgroupOf N).map ρ = (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map τ := by
    apply le_antisymm
    · rintro _ ⟨s,hs,rfl⟩
      obtain ⟨t,ht,he⟩ := hi (⟨s,hs⟩ : S R)
      have hst : ρ s = ρ (inclusion h.normalizes t) := by
        have hparam : h.coordinates.parameter (t⁻¹ * ⟨s,hs⟩) = 1 := by simp [he]
        have hc := (h.coordinates.parameter_kernel _).mp hparam
        have hk : (inclusion h.normalizes t)⁻¹ * s ∈ ρ.ker := by rw [hker]; exact hc
        have hk' : (ρ (inclusion h.normalizes t))⁻¹ * ρ s = 1 := by
          simpa only [MonoidHom.mem_ker,map_mul,map_inv] using hk
        exact (inv_mul_eq_one.mp hk').symm
      rw [hst]
      let k : K := ⟨t,ht⟩
      have heN : inclusion h.normalizes t = inclusion K.le_normalizer k := Subtype.ext rfl
      rw [heN,hρK]
      exact mem_map_of_mem τ (mem_map_of_mem a ((hPK k).mpr t.property))
    · rintro _ ⟨p,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨inclusion K.le_normalizer k,(hPK k).mp hk,hρK k⟩
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) F) P' (upperUnipotentSylow F 2)
  have hPg : (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).map (MulAut.conj g).toMonoidHom = upperUnipotent F :=
    congrArg (fun P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F) => (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) hg
  let b := τ g
  let ρ' := (MulAut.conj b).toMonoidHom.comp ρ
  let q' := b.toMonoidHom.comp (modelProjection m)
  have hq' (u : U K) : q' u = 1 ↔ (u : G) ∈ centralizer (K : Set G) := by
    change b (modelProjection m u) = 1 ↔ _
    rw [b.map_eq_one_iff,modelProjection_kernel]
  have hρ' (n : N) (u : U K) : ρ' n (q' u) = q' (normalizerConjugate n u) := by
    change b (ρ n (b.symm (b (modelProjection m u)))) = b (modelProjection m (normalizerConjugate n u))
    rw [b.symm_apply_apply,hρ]
  have hk' : ρ'.ker = (centralizer (U K : Set G)).subgroupOf N := by
    ext n
    change (MulAut.conj b) (ρ n) = 1 ↔ _
    rw [(MulAut.conj b).map_eq_one_iff]
    exact SetLike.ext_iff.mp hker n
  have hm' : ((S R).subgroupOf N).map ρ' = (upperUnipotent F).map τ := by
    change ((S R).subgroupOf N).map ((MulAut.conj b).toMonoidHom.comp ρ) = _
    rw [← map_map,hSi,map_map]
    have he : (MulAut.conj b).toMonoidHom.comp τ = τ.comp (MulAut.conj g).toMonoidHom := by
      ext z
      simp [b,MulAut.conj_apply]
    rw [he,← map_map,hPg]
  have hsemi' (n : N) : ∃ σ : F ≃+* F, ∀ c v,
      (ρ' n (Multiplicative.ofAdd (c • v))).toAdd = σ c • (ρ' n (Multiplicative.ofAdd v)).toAdd := by
    apply natural_image_normalizer_semilinear τ hτ
      ⟨ρ' n,?_⟩
    have hnb : b ∈ normalizer (τ.range : Set _) := τ.range.le_normalizer ⟨g,rfl⟩
    have hnr : ρ n ∈ normalizer (τ.range : Set _) := by
      rw [← himage]
      let : (K.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer le_rfl
      exact le_normalizer_map ρ (mem_map_of_mem ρ (show n ∈ normalizer (K.subgroupOf N : Set N) from
        by simpa only [(K.subgroupOf N).normalizer_eq_top] using mem_top n))
    change b * ρ n * b⁻¹ ∈ normalizer (τ.range : Set (MulAut (Multiplicative (Fin 2 → F))))
    let Pn := normalizer (τ.range : Set (MulAut (Multiplicative (Fin 2 → F))))
    have hbInv : b⁻¹ ∈ Pn := Pn.inv_mem hnb
    have hbr : b * ρ n ∈ Pn := Pn.mul_mem hnb hnr
    exact Pn.mul_mem hbr hbInv
  exact ⟨⟨τ,hτ,q',b.surjective.comp (modelProjection_surjective m),hq',h.normalizes,ρ',hρ',hk',hm',hsemi'⟩⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
