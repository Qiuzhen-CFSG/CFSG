module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryExtension
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPlaneShort.Structure
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Unitary-four plane endpoints and the complete diagram comparison

The determinant-one plane local has an irreducible Hermitian two-core.
Every two-subgroup of the plane parabolic lies in that local factor, so
normality transports its minimal-core property to the full parabolic.
A perfect normal subgroup with two noncentral core layers cannot embed
there. In the degree-two extension, perfectness first kills the outer
coordinate, and relative normality restricts both layers to the ordinary
plane parabolic.

Together with the point-endpoint calculations, these exclude both
orientations of the ordinary and extended unitary amalgams for the actual
selected diagram factor. The inclusion amalgam retains the whole overlap,
and S is the original O₂(N_G(L) ∩ H). This is the unitary comparison in
5.2.6; it does not assert that the right factor equals O²(H), or identify
the ambient completion. The Chapter12 companion applies these results to
the same selected factor while retaining the whole-residual branch.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651, and F.1.12(I)(6),
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour

private theorem core_minimal_of_normal_embedding
    {Y X : Type*} [Group Y] [Group X]
    (f : Y →* X) (hf : Function.Injective f) (hr : f.range.Normal)
    (hQ : pCore 2 X ≤ f.range)
    (hmin : ∀ N : Subgroup Y, N.Normal → N ≤ pCore 2 Y → N = ⊥ ∨ N = pCore 2 Y)
    (N : Subgroup X) [N.Normal] (hN : N ≤ pCore 2 X) :
    N = ⊥ ∨ N = pCore 2 X := by
  let := hr
  let e := MonoidHom.ofInjective hf
  have he : f = f.range.subtype.comp e.toMonoidHom := rfl
  have hcore : (pCore 2 Y).map f = pCore 2 X := by
    rw [he,←map_map,pCore_map_iso,pCore_eq_comap_of_normal,map_comap_eq,range_subtype]
    exact inf_eq_right.mpr hQ
  have hcomap : N.comap f ≤ pCore 2 Y := by
    rw [←comap_map_eq_self_of_injective hf (pCore 2 Y),hcore]
    exact comap_mono hN
  have hmap : (N.comap f).map f = N := by
    rw [map_comap_eq,inf_eq_right.mpr (hN.trans hQ)]
  rcases hmin (N.comap f) inferInstance hcomap with hz | ht
  · left
    rw [←hmap,hz,Subgroup.map_bot]
  · right
    rw [←hmap,ht,hcore]

/-- The actual plane parabolic has a minimal normal two-core, for every
positive field exponent, including the binary ground field. -/
theorem unitary_plane_core_minimal (m : ℕ) (hm : 1 ≤ m)
    (N : Subgroup (planeParabolic m hm)) [N.Normal]
    (hN : N ≤ pCore 2 (planeParabolic m hm)) :
    N = ⊥ ∨ N = pCore 2 (planeParabolic m hm) := by
  let P := planeParabolic m hm
  let K := L2 m hm
  let f : K →* P := inclusion (L2_le_planeParabolic m hm)
  have hr : f.range = K.subgroupOf P := by
    ext x
    exact ⟨fun ⟨y,he⟩ => he ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  have hn : f.range.Normal := by rw [hr]; infer_instance
  have hQ : pCore 2 P ≤ f.range := by
    rw [hr]
    have hh := two_subgroup_le_L2 m hm ((pCore 2 P).map P.subtype)
      (pCore_isPGroup.map P.subtype) (map_subtype_le _)
    exact fun _ hx => hh (mem_map_of_mem P.subtype hx)
  exact core_minimal_of_normal_embedding f (inclusion_injective _) hn hQ
    (L2TwoCore_normal_subgroup m hm) N hN

private theorem unitary_plane_core_minimal_of_equiv
    {X : Type*} [Group X] (m : ℕ) (hm : 1 ≤ m)
    (e : X ≃* planeParabolic m hm) (N : Subgroup X) [N.Normal]
    (hN : N ≤ pCore 2 X) : N = ⊥ ∨ N = pCore 2 X := by
  let D := N.map e.toMonoidHom
  let : D.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  have hD : D ≤ pCore 2 (planeParabolic m hm) := by
    rw [←pCore_map_iso 2 e]
    exact map_mono hN
  rcases unitary_plane_core_minimal m hm D hD with hz | ht
  · left
    exact (map_eq_bot_iff_of_injective _ e.injective).mp hz
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso]
    exact ht

private def planeOrdinaryEmbedding (m : ℕ) (hm : 1 ≤ m) :
    planeParabolic m hm →* Extension.plane m hm where
  toFun x := ⟨SemidirectProduct.inl x.val,(Extension.mem_plane m hm _).mpr x.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

private theorem planeOrdinaryEmbedding_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (planeOrdinaryEmbedding m hm) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Extension.plane m hm => z.val.left) h)

private theorem extension_plane_no_normal_layer
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {N : Subgroup Y} (h : NoncentralCoreLayer N)
    (m : ℕ) (hm : 1 ≤ m)
    (f : Y →* Extension.plane m hm) (hf : Function.Injective f)
    (hn : (N.map f).Normal) (hr : f.range.Normal) : False := by
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv
  let : Finite (Extension.ProjectiveExtension m hm) :=
    Finite.of_injective (fun x : Extension.ProjectiveExtension m hm => (x.left,x.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let j := planeOrdinaryEmbedding m hm
  let D := j.range
  let q : Extension.plane m hm →* Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter.C2 :=
    (SemidirectProduct.rightHom (φ := Extension.projectiveAction m hm)).comp (Extension.plane m hm).subtype
  have hD : f.range ≤ D := by
    rintro x ⟨y,rfl⟩
    have hy : q (f y) = 1 :=
      Abelianization.commutator_subset_ker (q.comp f) Group.IsPerfect.mem_commutator
    refine ⟨⟨(f y).val.left,(Extension.mem_plane m hm _).mp (f y).property⟩,?_⟩
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact hy.symm
  apply restrict_perfect_layer h f hf hn hr D hD
  intro K hK hle
  let := hK
  let e := (MonoidHom.ofInjective (planeOrdinaryEmbedding_injective m hm)).symm
  rcases unitary_plane_core_minimal_of_equiv m hm e K hle with hz | ht
  · exact Or.inl (by rw [hz,commutator_bot_left])
  · exact Or.inr ht

private theorem Preparation.exclude_right_parabolic_layer_model
    {G X : Type*} [Group G] [Finite G] [Group X]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hx : ∀ f : R →* X, Function.Injective f →
      ((((residual H).pCoreIn 2).subgroupOf R).map f).Normal → f.range.Normal → False) :
    ¬ Nonempty ((R ⊔ sourceS L H ⊔ A : Subgroup G) ≃* X) := by
  rintro ⟨e⟩
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
  let g := e.toMonoidHom.comp f
  have hng : (N.map g).Normal := by
    rw [←map_map]
    exact Normal.map hn e.toMonoidHom e.surjective
  have hrg : g.range.Normal := by
    rw [MonoidHom.range_comp]
    exact Normal.map hr e.toMonoidHom e.surjective
  exact hx g (e.injective.comp (inclusion_injective _)) hng hrg

/-- The literal right source parabolic cannot be the ordinary unitary
plane endpoint when its selected factor has the two original core layers. -/
theorem Preparation.not_unitary_plane_source_parabolic
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) ≃*
      planeParabolic m hm) := by
  rw [d.parabolic_one hTL]
  let := hp
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv
  apply d.exclude_right_parabolic_layer_model hN
  intro f hf hn hr
  apply normal_perfect_embedding_excludes_layer hl f hf hn hr
  intro N hN hle
  let := hN
  rcases unitary_plane_core_minimal m hm N hle with hz | ht
  · exact Or.inl (by rw [hz,commutator_bot_left])
  · exact Or.inr ht

/-- The degree-two plane endpoint is also excluded. Perfectness removes
the outer coordinate before the ordinary plane-core comparison. -/
theorem Preparation.not_unitary_extended_plane_source_parabolic
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) ≃*
      Extension.plane m hm) := by
  rw [d.parabolic_one hTL]
  let := hp
  exact d.exclude_right_parabolic_layer_model hN
    (fun f hf hn hr => extension_plane_no_normal_layer hl m hm f hf hn hr)

/-- The two literal source parabolics and their whole intersection, with
both actual inclusion maps. In particular the overlap retains its odd Cartans. -/
@[expose] def sourceParabolicAmalgam
    {G : Type*} [Group G] (L : Fin 2 → Subgroup G) (S : Subgroup G) :
    RankTwoAmalgam (ChapterF.Source.parabolic L S 0)
      (ChapterF.Source.parabolic L S 0 ⊓ ChapterF.Source.parabolic L S 1 : Subgroup G)
      (ChapterF.Source.parabolic L S 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

/-- Both orientations of the ordinary and degree-two unitary amalgams
are excluded for a prepared factor with the original two core layers.
The comparisons are compatible amalgam isomorphisms, not family labels. -/
theorem Preparation.not_unitary_amalgams
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ Nonempty (RankTwoAmalgam.Iso α (amalgam m hm)) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (amalgam m hm).reverse) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm)) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (Extension.amalgam m hm).reverse) := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨e⟩
    exact d.not_unitary_plane_source_parabolic hTL hN hp hl m hm ⟨e.right⟩
  · rintro ⟨e⟩
    exact d.not_unitary_point_source_parabolic hTL hN hp hl m hm ⟨e.right⟩
  · rintro ⟨e⟩
    exact d.not_unitary_extended_plane_source_parabolic hTL hN hp hl m hm ⟨e.right⟩
  · rintro ⟨e⟩
    exact d.not_unitary_extended_point_source_parabolic hTL hN hp hl m hm ⟨e.right⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global




