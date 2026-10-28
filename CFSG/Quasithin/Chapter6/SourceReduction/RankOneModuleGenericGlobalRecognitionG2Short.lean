module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionG2ShortModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryPlane
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.G2
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionPreparation

/-!
# Excluding both G₂ orientations for the selected diagram factor

The right source parabolic normalizes the original layer
R ∩ O₂(O²(H)). Its image is normal under an actual parabolic isomorphism.
The concrete short-parabolic core dichotomy contradicts the selected
perfect factor's two noncentral core layers.

The opposite orientation puts the original left factor at the short
endpoint. Transporting solvable residuals gives its actual isomorphism
with the short local factor. That factor centralizes its core center,
contrary to the original faithful-local hypothesis. At the binary field
the short parabolic is solvable and cannot contain either perfect source
factor. Thus both compatible G₂ amalgam orientations are excluded at
all positive binary exponents, with no assertion about the long model's
core-layer count.

The source inclusion amalgam retains the whole overlap and the original
S = O₂(N_G(L) ∩ H). This is the G₂ comparison in 5.2.6; it does not
identify R with O²(H) or recognize the ambient completion. The Chapter12
extension retains the whole-residual branch, including U₅(4), and the
independent source uniqueness and F.1.12 inputs.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651, and F.1.12(I)(3),
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

/-- The original right parabolic cannot be the short G₂ endpoint when its
selected factor has the two original noncentral core layers. This includes
all finite binary fields; the full order-two-field parabolic is solvable. -/
theorem Preparation.not_g2_short_source_parabolic
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) ≃*
      Atlas.G2.LieParabolicSetup.parabolic₁ (F := F)) := by
  rw [d.parabolic_one hTL]
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
  let g := e.toMonoidHom.comp f
  have hng : (N.map g).Normal := by
    rw [←map_map]
    exact Normal.map hn e.toMonoidHom e.surjective
  have hrg : g.range.Normal := by
    rw [MonoidHom.range_comp]
    exact Normal.map hr e.toMonoidHom e.surjective
  apply normal_perfect_embedding_excludes_layer hl g
    (e.injective.comp (inclusion_injective _)) hng hrg
  intro Q hQ hle
  let := hQ
  exact G2Short.core_dichotomy Q hle

/-- The compatible G₂ amalgam with its short endpoint on the right is
excluded for the selected diagram factor. Both maps use the whole overlap. -/
theorem Preparation.not_g2_short_amalgam
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) :
    ¬ Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) := by
  rintro ⟨e⟩
  exact d.not_g2_short_source_parabolic hTL hN hp hl ⟨e.right⟩


/-- A model centralizing its intrinsic two-core center cannot be the original
faithful factor. This comparison also applies to the triality arms factor. -/
theorem faithful_not_core_center_central
    {G X : Type*} [Group G] [Group X] {L : Subgroup G}
    (hL : faithfulLocal L) (e : L ≃* X)
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X) : False := by
  apply hL.2.2.2
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz
  have hz0 := omegaOneAmbient_le _ hz
  obtain ⟨q,hq,rfl⟩ := hz0.1
  have hqc : (⟨q,hq⟩ : pCore 2 L) ∈ center (pCore 2 L) := by
    rw [mem_center_iff]
    intro r
    exact Subtype.ext (Subtype.ext (hz0.2 r.val.val (mem_map_of_mem L.subtype r.property)))
  have heq : e q ∈ pCore 2 X := by
    rw [←pCore_map_iso 2 e]
    exact mem_map_of_mem _ hq
  have hce : (⟨e q,heq⟩ : pCore 2 X) ∈ center (pCore 2 X) := by
    rw [mem_center_iff]
    intro r
    have hr : r.val ∈ (pCore 2 L).map e.toMonoidHom := by
      rw [pCore_map_iso]
      exact r.property
    obtain ⟨t,ht,he⟩ := hr
    apply Subtype.ext
    change r.val * e q = e q * r.val
    rw [←he]
    change e t * e q = e q * e t
    rw [←map_mul,←map_mul]
    exact congrArg e (congrArg (fun x : pCore 2 L => x.val) (mem_center_iff.mp hqc ⟨t,ht⟩))
  have hzX : e q ∈ center X := hc (mem_map_of_mem _ hce)
  rw [mem_centralizer_iff]
  intro y hy
  apply congrArg Subtype.val (show (⟨y,hy⟩ : L)*q = q*⟨y,hy⟩ from ?_)
  apply e.injective
  simpa only [map_mul] using mem_center_iff.mp hzX (e ⟨y,hy⟩)

/-- The original faithful left factor cannot be the short G₂ endpoint.
Its noncentral core-center action contradicts the actual short local core center. -/
theorem Preparation.not_g2_short_left_parabolic
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R) :
    ¬ Nonempty ((ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) ≃*
      Atlas.G2.LieParabolicSetup.parabolic₁ (F := F)) := by
  open Atlas.G2.LieParabolicSetup in
  rintro ⟨e⟩
  by_cases hq : 2 < Nat.card F
  · let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
    let Q := Atlas.G2.LieParabolicSetup.parabolic₁ (F := F)
    let a : solvableResidual P ≃* L :=
      ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
        (MulEquiv.subgroupCongr (d.parabolic_residuals h hTH hp 0))
    let b : solvableResidual Q ≃* Atlas.G2.LieParabolicSetup.local₁ (F := F) :=
      ((solvableResidual Q).equivMapOfInjective Q.subtype Q.subtype_injective).trans
        (MulEquiv.subgroupCongr (Atlas.G2.HigherFieldResiduals.parabolic₁_residual hq))
    exact faithful_not_core_center_central h.local_mem.2
      (a.symm.trans (e.solvableResidualEquiv.trans b))
      Atlas.G2.LieParabolicSetup.local₁_core_center_le_center
  · have he : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
    let := G2Short.parabolic_solvable_of_card_two he
    exact d.parabolics_not_solvable h hp 0
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- Both compatible orientations of the actual G₂ amalgam are excluded.
The left orientation uses the original faithful core-center action; the right
orientation uses the selected factor's two noncentral layers. -/
theorem Preparation.not_g2_amalgams
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R)) :
    let α := sourceParabolicAmalgam ![L,R] (sourceS L H)
    ¬ Nonempty (RankTwoAmalgam.Iso α (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∧
      ¬ Nonempty (RankTwoAmalgam.Iso α (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) := by
  refine ⟨?_,d.not_g2_short_amalgam h.sylow_normalizes hN hp hl⟩
  rintro ⟨e⟩
  exact d.not_g2_short_left_parabolic h hTH hp ⟨e.left⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
