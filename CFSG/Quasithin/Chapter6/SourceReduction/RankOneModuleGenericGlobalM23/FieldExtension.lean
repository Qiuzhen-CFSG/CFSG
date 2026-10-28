module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LinearCompletion
public import Theory.GroupTheory.NormalizerActionCore
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.Recognition.QuasithinM23.LinearExtension

/-!
# The original Sylow extension in source 5.2.16(2)

The recognized generated group meets the original T in precisely sourceS,
and its join with T is L ∨ H, of order 40320. Its centerlessness and the
proved trivial two-core make the original conjugation action faithful.
An element of T outside the completion fixes both parabolics; the marked
linear–field calculation identifies the entire extension with PSL₃(4) ⋊ C₂.
The same map preserves both original parabolics and the whole Borel, with
an explicit equation on every element of the original linear subgroup.

Source: Aschbacher–Smith 5.2.16(2), printed p.655 (`refs/quasithin.pdf`).
Ambient generation and M₂₃ recognition are subsequent obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Matrix.PSL3.LinearThree

theorem Preparation.linear_nonmaximal_extension_geometry
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let C := ChapterF.Source.generated ![L,residual H] (sourceS L H)
    C ⊓ (T : Subgroup G) = sourceS L H ∧ Nat.card (L ⊔ H : Subgroup G) = 40320 := by
  let C := ChapterF.Source.generated ![L,residual H] (sourceS L H)
  obtain ⟨e,_,_⟩ := d.linear_nonmaximal_generated_equiv h hH hp E hm hE he hnonmax
  have hCcard : Nat.card C = 20160 := by
    dsimp only [C]
    rw [← ChapterF.Source.parabolics_generate]
    exact (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  obtain ⟨_,_,_,_,_,_,_,hTcard,hScard,_⟩ :=
    d.linear_nonmaximal_core_geometry h hH hp E hm hE he hnonmax
  have hSCT : sourceS L H ≤ C ⊓ (T : Subgroup G) :=
    le_inf le_sup_right (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
  have hCT : C ⊓ (T : Subgroup G) = sourceS L H := by
    apply (eq_of_le_of_card_ge hSCT ?_).symm
    have h₁ := card_dvd_of_le (show C ⊓ (T : Subgroup G) ≤ C from inf_le_left)
    have h₂ := card_dvd_of_le (show C ⊓ (T : Subgroup G) ≤ (T : Subgroup G) from inf_le_right)
    rw [hCcard] at h₁
    rw [hTcard] at h₂
    have hh := Nat.dvd_gcd h₁ h₂
    norm_num at hh
    rw [hScard]
    exact Nat.le_of_dvd (by decide) hh
  refine ⟨hCT,?_⟩
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes C (T : Subgroup G)
    (residual_completion_sylow_normalizes h.sylow_normalizes hH.1.1.2)
  rw [hCcard,hTcard,hCT,hScard,
    residual_completion_sup_sylow h.sylow_normalizes hH.1.1.2] at hc
  omega


private theorem parabolics_normalized
    {G : Type*} [Group G] {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H) (i : Fin 2) :
    (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i : Set G) := by
  have hS := sylow_normalizes_sourceS hTL hTH
  have hK (j : Fin 2) : (T : Subgroup G) ≤ normalizer (![L,residual H] j : Set G) := by
    fin_cases j
    · exact hTL
    · exact hTH.trans (le_normalizer_residual H)
  have hB (j : Fin 2) : (T : Subgroup G) ≤ normalizer
      (ChapterF.Source.borel (![L,residual H] j) (sourceS L H) : Set G) := by
    have hi := (le_inf hS (hK j)).trans inf_normalizer_le_normalizer_inf
    exact (le_inf (hK j) (hi.trans (normalizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact (le_inf ((le_inf (hK i) hS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _))
    (hB (ChapterF.Source.other i))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem marked_conjugation_preserves
    {G K : Type*} [Group G] [Group K] [Finite G]
    (C P : Subgroup G) (e : C ≃* K) (t : G)
    (htC : t ∈ normalizer (C : Set G)) (htP : t ∈ normalizer (P : Set G)) :
    ((P.subgroupOf C).map e.toMonoidHom).map
      (MulAut.congr e (C.normalizerMonoidHom ⟨t,htC⟩)).toMonoidHom =
      (P.subgroupOf C).map e.toMonoidHom := by
  let a := MulAut.congr e (C.normalizerMonoidHom ⟨t,htC⟩)
  let : Finite K := Finite.of_equiv C e.toEquiv
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨C.normalizerMonoidHom ⟨t,htC⟩ x,?_,?_⟩
    · exact (mem_normalizer_iff.mp htP (x:G)).mp hx
    · change e (C.normalizerMonoidHom ⟨t,htC⟩ x) =
        e (C.normalizerMonoidHom ⟨t,htC⟩ (e.symm (e x)))
      rw [e.symm_apply_apply]
  · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]

/-- Source 5.2.16(2), preserving both parabolics and the full original Borel
under the very same extension map. -/
theorem Preparation.linear_nonmaximal_field_extension
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
    let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    let C := P ⊔ Q
    ∃ (e : C ≃* Matrix.PSL3Four.PSL)
      (f : (C ⊔ (T : Subgroup G) : Subgroup G) ≃* Matrix.PSL3Four.FieldExtension),
      (((P.subgroupOf C).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (Q.subgroupOf C).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F) ∨
       ((Q.subgroupOf C).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (P.subgroupOf C).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F)) ∧
      ((P ⊓ Q).subgroupOf C).map e.toMonoidHom = borel Matrix.PSL3Four.F ∧
      ∀ c : C, f ⟨c,mem_sup_left c.property⟩ = Matrix.PSL3Four.linearInclusion (e c) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let C := P ⊔ Q
  let X := C ⊔ (T : Subgroup G)
  have hCeq : C = ChapterF.Source.generated ![L,residual H] (sourceS L H) :=
    ChapterF.Source.parabolics_generate _ _
  have hXeq : X = L ⊔ H := by
    change C ⊔ (T : Subgroup G) = _
    rw [hCeq,residual_completion_sup_sylow h.sylow_normalizes hH.1.1.2]
  obtain ⟨e,hePQ,heB⟩ := d.linear_nonmaximal_generated_equiv h hH hp E hm hE he hnonmax
  change C ≃* Matrix.PSL3Four.PSL at e
  have hcardC : Nat.card C = 20160 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  have hcardX : Nat.card X = 40320 := by
    rw [hXeq]
    exact (d.linear_nonmaximal_extension_geometry h hH hp E hm hE he hnonmax).2
  have hnT : (T : Subgroup G) ≤ normalizer (C : Set G) := by
    rw [hCeq]
    exact residual_completion_sylow_normalizes h.sylow_normalizes hH.1.1.2
  have hnX : X ≤ normalizer (C : Set G) := sup_le C.le_normalizer hnT
  let α : X →* MulAut Matrix.PSL3Four.PSL := (MulAut.congr e).toMonoidHom.comp
    (C.normalizerMonoidHom.comp (inclusion hnX))
  have hαc (c : C) : α ⟨c,mem_sup_left c.property⟩ = MulAut.conj (e c) := by
    ext y
    change e (C.normalizerMonoidHom ⟨c,hnX (mem_sup_left c.property)⟩ (e.symm y)) = _
    change e (c * e.symm y * c⁻¹) = _
    simp [MulAut.conj_apply]
  have hz : center C = ⊥ := by
    let := Atlas.sl_perfect (F := Matrix.PSL3Four.F) 3 (by decide)
    have hz0 : center Matrix.PSL3Four.PSL = ⊥ :=
      Group.IsPerfect.center_quotient_center_eq_bot Matrix.PSL3Four.SL
    apply eq_bot_iff.mpr
    intro c hc
    have hh := ((centerCongr e) ⟨c,hc⟩).property
    change e c ∈ center Matrix.PSL3Four.PSL at hh
    rw [hz0] at hh
    apply mem_bot.mpr
    apply e.injective
    simpa using mem_bot.mp hh
  have hα : Function.Injective α := (MulAut.congr e).injective.comp
    (join_normalizer_action_injective_of_pCore_eq_bot (T : Subgroup G) C T.isPGroup'
      hnT hz (by change pCore 2 X = ⊥; rw [hXeq]; exact d.residual_pair_twoCore_eq_bot))
  have hinner : MulAut.innerSubgroup Matrix.PSL3Four.PSL ≤ α.range := by
    rintro _ ⟨z,rfl⟩
    refine ⟨⟨e.symm z,mem_sup_left (e.symm z).property⟩,?_⟩
    rw [hαc,e.apply_symm_apply]
  have hnot : ¬ (T : Subgroup G) ≤ C := by
    intro ht
    have hh := card_dvd_of_le ht
    have hc := (d.linear_nonmaximal_core_geometry h hH hp E hm hE he hnonmax).2.2.2.2.2.2.2.1
    rw [hc,hcardC] at hh
    norm_num at hh
  obtain ⟨t,ht,htC⟩ := Set.not_subset.mp hnot
  let tx : X := ⟨t,mem_sup_right ht⟩
  have hout : α tx ∉ MulAut.innerSubgroup Matrix.PSL3Four.PSL := by
    rintro ⟨z,hz⟩
    have hh : α ⟨e.symm z,mem_sup_left (e.symm z).property⟩ = α tx := by
      rw [hαc,e.apply_symm_apply,hz]
    have eq := congrArg Subtype.val (hα hh)
    change (e.symm z : G) = t at eq
    exact htC (eq ▸ (e.symm z).property)
  have hfix (i : Fin 2) :
      (((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).subgroupOf C).map
        e.toMonoidHom).map (α tx).toMonoidHom =
      ((ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i).subgroupOf C).map e.toMonoidHom :=
    marked_conjugation_preserves C _ e t (hnT ht)
      (parabolics_normalized h.sylow_normalizes hH.1.1.2 i ht)
  have hfix' (b : Bool) :
      (Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F b).map (α tx).toMonoidHom =
      Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F b := by
    have hpfix := hfix 0
    have hqfix := hfix 1
    change ((P.subgroupOf C).map e.toMonoidHom).map (α tx).toMonoidHom =
      (P.subgroupOf C).map e.toMonoidHom at hpfix
    change ((Q.subgroupOf C).map e.toMonoidHom).map (α tx).toMonoidHom =
      (Q.subgroupOf C).map e.toMonoidHom at hqfix
    rcases hePQ with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · rw [hl] at hpfix
      rw [hr] at hqfix
      cases b
      · exact hqfix
      · exact hpfix
    · rw [hr] at hpfix
      rw [hl] at hqfix
      cases b
      · exact hpfix
      · exact hqfix
  obtain ⟨δ,hδ,hrange⟩ := QuasithinM23.LinearExtension.marked_range α.range hinner
    ((Nat.card_congr (MonoidHom.ofInjective hα).toEquiv).symm.trans hcardX)
    (α tx) ⟨tx,rfl⟩ hout hfix'
  let β := (MulAut.congr δ).toMonoidHom.comp α
  have hβ : Function.Injective β := (MulAut.congr δ).injective.comp hα
  have hrange' : β.range = QuasithinM23.LinearExtension.fieldAut.range := by
    rw [MonoidHom.range_comp]
    exact hrange
  let f : X ≃* Matrix.PSL3Four.FieldExtension := (MonoidHom.ofInjective hβ).trans
    ((MulEquiv.subgroupCongr hrange').trans
      (MonoidHom.ofInjective QuasithinM23.LinearExtension.fieldAut_injective).symm)
  have hf (x : X) : QuasithinM23.LinearExtension.fieldAut (f x) = β x := by
    exact congrArg Subtype.val ((MonoidHom.ofInjective
      QuasithinM23.LinearExtension.fieldAut_injective).apply_symm_apply
      ((MulEquiv.subgroupCongr hrange') ((MonoidHom.ofInjective hβ) x)))
  refine ⟨e.trans δ,f,?_,?_,?_⟩
  · have ht (R : Subgroup C) : R.map (e.trans δ).toMonoidHom =
        (R.map e.toMonoidHom).map δ.toMonoidHom := by rw [map_map]; rfl
    rcases hePQ with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨by rw [ht,hl]; exact hδ true,by rw [ht,hr]; exact hδ false⟩
    · exact Or.inr ⟨by rw [ht,hl]; exact hδ true,by rw [ht,hr]; exact hδ false⟩
  · change ((P ⊓ Q).subgroupOf C).map (δ.toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map,heB]
    rw [←ChapterF.GreenBook.LieModels.LinearThree.parabolic_intersection Matrix.PSL3Four.F,
      map_inf _ _ _ δ.injective]
    exact congrArg₂ (· ⊓ ·) (hδ true) (hδ false)
  · intro c
    apply QuasithinM23.LinearExtension.fieldAut_injective
    rw [hf,QuasithinM23.LinearExtension.fieldAut_linear]
    change MulAut.congr δ (α ⟨c,mem_sup_left c.property⟩) = MulAut.conj (δ (e c))
    rw [hαc]
    ext y
    simp [MulAut.congr_apply,MulAut.conj_apply]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
