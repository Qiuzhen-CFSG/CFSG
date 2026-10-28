module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Hyperplane
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# Natural-module calculations on the original ambient action

The recognized group isomorphism and binary linear intertwiner carry the
coordinate F-hyperplane to a literal subspace of V. Its pointwise centralizer
inside L is exactly the image of the model hyperplane centralizer. Thus rank,
fixed codimension, quadraticity and bestness hold for this same subgroup.
All model best offenders transport, giving L ≤ J(G,V). The lower bound applies
to each actual quadratic actor contained in L; no outer-actor estimate is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.1,
printed pp.454–455.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.Linear.Natural

section Transport
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

lemma elementary_map_injective (f : G →* H) (hf : Function.Injective f)
    {A : Subgroup G} (hA : IsElementaryTwo A) : IsElementaryTwo (A.map f) := by
  let : IsElementaryAbelian 2 A := hA.2
  exact ⟨fun hb => hA.1 ((A.map_eq_bot_iff_of_injective hf).mp hb),
    IsElementaryAbelian.map f⟩

lemma quadratic_map_equivariant (f : G →* H) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} (hA : IsQuadratic ρ A) : IsQuadratic σ (A.map f) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  obtain ⟨v, rfl⟩ := E.surjective w
  have h := congrArg E (hA a ha b hb v)
  simpa only [map_sub, hE] using h

lemma weight_map_equivariant (f : G →* H) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    (A : Subgroup G) : weight σ (A.map f) = weight ρ A := by
  unfold weight
  rw [rank_map_injective f hf, ← fixedSpace_map_equivariant ρ σ f E hE,
    LinearEquiv.finrank_map_eq]

lemma best_map_equivariant (f : G →* H) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup G} (hA : IsBestOffender ρ A) : IsBestOffender σ (A.map f) := by
  refine ⟨elementary_map_injective f hf hA.1, ?_⟩
  intro B hB
  have hBA : B.comap f ≤ A := by
    intro b hb
    obtain ⟨a, ha, he⟩ := hB hb
    exact (hf he) ▸ ha
  have hmap : (B.comap f).map f = B :=
    Subgroup.map_comap_eq_self (hB.trans (Subgroup.map_le_range _ _))
  rw [← hmap, weight_map_equivariant f hf E hE, weight_map_equivariant f hf E hE]
  exact hA.2 _ hBA

noncomputable def reverseEquiv (e : ActionEquiv ρ σ) : ActionEquiv σ ρ where
  groupEquiv := e.groupEquiv.symm
  linearEquiv := e.linearEquiv.symm
  intertwines g w := by
    apply e.linearEquiv.injective
    rw [e.linearEquiv.apply_symm_apply, e.intertwines,
      e.groupEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply]

end Transport

section Ambient
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField) (n : ℕ)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F n))

include e

noncomputable def modelEmbedding : Matrix.SpecialLinearGroup (Fin n) F.Carrier →* G :=
  L.subtype.comp e.groupEquiv.symm.toMonoidHom

lemma modelEmbedding_injective : Function.Injective (modelEmbedding ρ L F n e) :=
  L.subtype_injective.comp e.groupEquiv.symm.injective

lemma model_intertwines (g : Matrix.SpecialLinearGroup (Fin n) F.Carrier)
    (v : Fin n → F.Carrier) :
    e.linearEquiv.symm (linearNatural F n g v) =
      ρ (modelEmbedding ρ L F n e g) (e.linearEquiv.symm v) :=
  (reverseEquiv e).intertwines g v

noncomputable def markedHyperplane (j : Fin n) : Submodule (ZMod 2) V :=
  ((coordinateHyperplane F n j).restrictScalars (ZMod 2)).comap e.linearEquiv.toLinearMap

noncomputable def markedCentralizer (j : Fin n) : Subgroup G :=
  subspaceKernel ρ (markedHyperplane ρ L F n e j) L

lemma markedCentralizer_eq_map (j : Fin n) : markedCentralizer ρ L F n e j =
    (hyperplaneCentralizer F n j).map (modelEmbedding ρ L F n e) := by
  ext g
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨e.groupEquiv ⟨g, hg⟩, ⟨Subgroup.mem_top _, ?_⟩, ?_⟩
    · intro w hw
      have hh := hfix (e.linearEquiv.symm w) (by
        change e.linearEquiv (e.linearEquiv.symm w) ∈ (coordinateHyperplane F n j).restrictScalars (ZMod 2)
        simpa only [e.linearEquiv.apply_symm_apply] using hw)
      have he := e.intertwines ⟨g, hg⟩ (e.linearEquiv.symm w)
      change e.linearEquiv (ρ g (e.linearEquiv.symm w)) = _ at he
      rw [hh, e.linearEquiv.apply_symm_apply] at he
      exact he.symm
    · change (e.groupEquiv.symm (e.groupEquiv ⟨g, hg⟩) : G) = g
      rw [e.groupEquiv.symm_apply_apply]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(e.groupEquiv.symm a).property, ?_⟩
    intro v hv
    apply e.linearEquiv.injective
    have he := e.intertwines (e.groupEquiv.symm a) v
    rw [e.groupEquiv.apply_symm_apply] at he
    exact he.trans (ha.2 _ hv)

lemma markedCentralizer_calculation (hn : 2 ≤ n) (j : Fin n) :
    rank (markedCentralizer ρ L F n e j) = F.degree * (n - 1) ∧
    fixedCodim ρ (markedCentralizer ρ L F n e j) = F.degree ∧
    IsQuadratic ρ (markedCentralizer ρ L F n e j) ∧
    IsBestOffender ρ (markedCentralizer ρ L F n e j) := by
  rw [markedCentralizer_eq_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rank_map_injective _ (modelEmbedding_injective ρ L F n e), hyperplaneCentralizer_rank]
  · rw [← fixedCodim_map_equivariant (linearNatural F n) ρ _ e.linearEquiv.symm
      (model_intertwines ρ L F n e)]
    exact subgroup_fixedCodim F n j le_rfl (hyperplaneCentralizer_elementary F n j hn).1
  · exact quadratic_map_equivariant _ e.linearEquiv.symm (model_intertwines ρ L F n e)
      (hyperplaneCentralizer_quadratic F n j)
  · exact best_map_equivariant _ (modelEmbedding_injective ρ L F n e)
      e.linearEquiv.symm (model_intertwines ρ L F n e) (hyperplaneCentralizer_best F n j hn)

lemma component_le_offenderSubgroup (hn : 2 ≤ n) : L ≤ offenderSubgroup ρ := by
  have hmodel : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) ≤
      (offenderSubgroup ρ).comap (modelEmbedding ρ L F n e) := by
    rw [← offenderSubgroup_eq_top F n hn]
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    exact Subgroup.map_le_iff_le_comap.mp
      ((best_map_equivariant _ (modelEmbedding_injective ρ L F n e)
        e.linearEquiv.symm (model_intertwines ρ L F n e) hA).le_offenderSubgroup ρ)
  intro g hg
  have h := hmodel (Subgroup.mem_top (e.groupEquiv ⟨g, hg⟩))
  change (e.groupEquiv.symm (e.groupEquiv ⟨g, hg⟩) : G) ∈ offenderSubgroup ρ at h
  simpa only [e.groupEquiv.symm_apply_apply] using h

lemma inner_actionRatio_ge (hn : 2 ≤ n) {A : Subgroup G}
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A) (hAL : A ≤ L) :
    1 / (n - 1 : ℕ) ≤ actionRatio ρ A := by
  let B := A.subgroupOf L
  have hm : B.map L.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAL
  have he : IsElementaryTwo B := by
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAL⟩
    intro hb
    exact hA.1 (by rw [← hm, hb, Subgroup.map_bot])
  have hqB : IsQuadratic (ρ.comp L.subtype) B := by
    intro a ha b hb v
    exact hq a ha b hb v
  have hbound := quadratic_actionRatio_ge F n hn
    (elementary_map_injective e.groupEquiv.toMonoidHom e.groupEquiv.injective he)
    (quadratic_map_equivariant _ e.linearEquiv e.intertwines hqB)
  unfold actionRatio at hbound ⊢
  rw [← fixedCodim_map_equivariant _ _ _ e.linearEquiv e.intertwines,
    rank_map_injective _ e.groupEquiv.injective] at hbound
  have hc : fixedCodim (ρ.comp L.subtype) B = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, hm]
  have hr : rank B = rank A := by
    rw [← rank_map_injective L.subtype L.subtype_injective, hm]
  simpa only [hc, hr] using hbound

lemma quadraticRatio_le (hn : 2 ≤ n) : quadraticRatio ρ ≤ 1 / (n - 1 : ℕ) := by
  let j : Fin n := ⟨0, by omega⟩
  obtain ⟨hr, hc, hq, hb⟩ := markedCentralizer_calculation ρ L F n e hn j
  apply iInf_le_of_le (markedCentralizer ρ L F n e j)
  apply iInf_le_of_le ⟨hb.1, hq⟩
  have hf : (F.degree : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt F.degree_pos)
  rw [actionRatio, hr, hc, Nat.cast_mul]
  exact le_of_eq (by simpa only [mul_one] using
    (ENNReal.mul_div_mul_left (1 : ℝ≥0∞) ((n - 1 : ℕ) : ℝ≥0∞) hf (by simp)))

end Ambient
end CFSG.Quasithin.ChapterK.Linear.Natural
