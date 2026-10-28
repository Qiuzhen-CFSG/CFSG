module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitary
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourExtension

/-!
# Excluding the degree-two unitary point endpoint

A perfect normal subgroup of the extended point parabolic lies in the
ordinary point parabolic, since its image in the outer group of order two
is trivial. Relative normality preserves the exact intermediate layer.
The ordinary model's Frattini dichotomy then contradicts the two noncentral
layers in the selected diagram factor.

This proves the extended point comparison used in the diagram exclusion
in Aschbacher–Smith, Proposition 5.2.6, printed pp.650–651
(`refs/quasithin.pdf`). The argument uses the literal semidirect extension
and does not require a formula for its two-core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour

/-- Two noncentral layers in a perfect normal subgroup contradict a
core dichotomy in the containing group. The intermediate layer is required
to be normal in that containing group. -/
theorem normal_perfect_embedding_excludes_layer
    {Y X : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] [Group X] [Finite X]
    {N : Subgroup Y} (h : NoncentralCoreLayer N)
    (f : Y →* X) (hf : Function.Injective f) (hn : (N.map f).Normal)
    (hr : f.range.Normal)
    (hD : ∀ D : Subgroup X, D.Normal → D ≤ pCore 2 X →
      ⁅D,solvableResidual X⁆ = ⊥ ∨ D = pCore 2 X) : False := by
  let := hn
  let := hr
  let r := MonoidHom.ofInjective hf
  have hmap : (pCore 2 Y).map f = (pCore 2 f.range).map f.range.subtype := by
    rw [←pCore_map_iso 2 r,map_map]
    rfl
  have hQ : (pCore 2 Y).map f ≤ pCore 2 X := by
    rw [hmap]
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
  let : Group.IsPerfect f.range := by
    rw [MonoidHom.range_eq_map]
    exact Group.IsPerfect.map f
  have hres : f.range ≤ solvableResidual X := le_solvableResidual_of_isPerfect _
  rcases hD (N.map f) hn ((map_mono h.2.1).trans hQ) with hc | he
  · have hh : ⁅N,(⊤ : Subgroup Y)⁆ = ⊥ := by
      apply map_injective hf
      rw [map_commutator,←MonoidHom.range_eq_map,Subgroup.map_bot]
      exact le_bot_iff.mp ((commutator_mono le_rfl hres).trans hc.le)
    exact h.2.2.1 (by
      simpa only [coe_top,centralizer_univ] using commutator_eq_bot_iff_le_centralizer.mp hh)
  · have hle : pCore 2 Y ≤ N :=
      (map_le_map_iff_of_injective hf).mp (he ▸ hQ)
    exact h.2.2.2 ((commutator_le_left _ _).trans hle)

/-- Restrict a perfect normal embedding, and its normal intermediate layer,
to a subgroup containing its image before applying the core dichotomy. -/
theorem restrict_perfect_layer
    {Y X : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] [Group X] [Finite X]
    {N : Subgroup Y} (h : NoncentralCoreLayer N)
    (f : Y →* X) (hf : Function.Injective f) (hn : (N.map f).Normal)
    (hr : f.range.Normal)
    (D : Subgroup X) (hD : f.range ≤ D)
    (hc : ∀ K : Subgroup D, K.Normal → K ≤ pCore 2 D →
      ⁅K,solvableResidual D⁆ = ⊥ ∨ K = pCore 2 D) : False := by
  let := hn
  let := hr
  let j := f.codRestrict D (fun y => hD ⟨y,rfl⟩)
  have hj : Function.Injective j := by
    intro a b hh
    exact hf (congrArg Subtype.val hh)
  have hmap : N.map j = (N.map f).subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,rfl⟩
    · rintro ⟨y,hy,he⟩
      exact ⟨y,hy,Subtype.ext he⟩
  have hrange : j.range = f.range.subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,he⟩
      exact ⟨y,Subtype.ext he⟩
  have hnj : (N.map j).Normal := by rw [hmap]; infer_instance
  have hrj : j.range.Normal := by rw [hrange]; infer_instance
  exact normal_perfect_embedding_excludes_layer h j hj hnj hrj hc

private def pointOrdinaryEmbedding (m : ℕ) (hm : 1 ≤ m) :
    pointParabolic m hm →* Extension.point m hm where
  toFun x := ⟨SemidirectProduct.inl x.val,(Extension.mem_point m hm _).mpr x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

private theorem pointOrdinaryEmbedding_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (pointOrdinaryEmbedding m hm) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Extension.point m hm => z.val.left) h)

private theorem extension_point_no_normal_layer
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {N : Subgroup Y} (h : NoncentralCoreLayer N)
    (m : ℕ) (hm : 1 ≤ m)
    (f : Y →* Extension.point m hm) (hf : Function.Injective f)
    (hn : (N.map f).Normal) (hr : f.range.Normal) : False := by
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv
  let : Finite (Extension.ProjectiveExtension m hm) :=
    Finite.of_injective (fun x : Extension.ProjectiveExtension m hm => (x.left,x.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let j := pointOrdinaryEmbedding m hm
  let D := j.range
  let q : Extension.point m hm →* Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.C2 :=
    (SemidirectProduct.rightHom (φ := Extension.projectiveAction m hm)).comp (Extension.point m hm).subtype
  have hD : f.range ≤ D := by
    rintro x ⟨y,rfl⟩
    have hy : q (f y) = 1 :=
      Abelianization.commutator_subset_ker (q.comp f) Group.IsPerfect.mem_commutator
    refine ⟨⟨(f y).val.left,(Extension.mem_point m hm _).mp (f y).property⟩,?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact hy.symm
  apply restrict_perfect_layer h f hf hn hr D hD
  intro K hK hle
  let := hK
  let e := (MonoidHom.ofInjective (pointOrdinaryEmbedding_injective m hm)).symm
  exact UnitaryFrattini.point_core_dichotomy_of_equiv m hm e K hle

/-- The degree-two extended point row is also impossible. Perfectness
places R in the ordinary point subgroup; relative normality carries both
layers there, where the proved model Frattini dichotomy applies. -/
theorem Preparation.not_unitary_extended_point_parabolic
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((R ⊔ sourceS L H ⊔ A : Subgroup G) ≃* Extension.point m hm) := by
  rintro ⟨e⟩
  let := hp
  let J := R ⊔ sourceS L H ⊔ A
  let N := ((residual H).pCoreIn 2).subgroupOf R
  let f : R →* J := inclusion (show R ≤ J from le_sup_left.trans le_sup_left)
  have hnR : J ≤ normalizer (R : Set G) :=
    sup_le (sup_le R.le_normalizer d.S_normalizes_right) d.cartan_normalizes_right
  have hrf : f.range = R.subgroupOf J := by
    ext x
    exact ⟨fun ⟨y,he⟩ => he ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  have hr : f.range.Normal := by
    rw [hrf]
    exact normal_subgroupOf_of_le_normalizer hnR
  have heN : N.map f = ((residual H).pCoreIn 2 ⊓ R).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans (le_sup_left.trans le_sup_left))]
    change N.map R.subtype = _
    exact subgroupOf_map_subtype _ _
  have hn : (N.map f).Normal := by
    rw [heN]
    exact normal_subgroupOf_of_le_normalizer (d.right_parabolic_normalizes_layer hN)
  let := hn
  let := hr
  let g := e.toMonoidHom.comp f
  have hng : (N.map g).Normal := by
    rw [←map_map]
    exact Normal.map hn e.toMonoidHom e.surjective
  have hrg : g.range.Normal := by
    rw [MonoidHom.range_comp]
    exact Normal.map hr e.toMonoidHom e.surjective
  exact extension_point_no_normal_layer hl m hm g
    (e.injective.comp (inclusion_injective _)) hng hrg

/-- The degree-two exclusion on the literal second source parabolic. -/
theorem Preparation.not_unitary_extended_point_source_parabolic
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) ≃*
      Extension.point m hm) := by
  rw [d.parabolic_one hTL]
  exact d.not_unitary_extended_point_parabolic hN hp hl m hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
