module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Sections
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.GroupTheory.ConjugateSpanSylow


/-!
# Literal Goldschmidt groups in the rank-three branch of 14.7.70

The two vertices are the subgroups L₁T and YT of the actual I = ⟨L₁T,Y⟩,
where Y is the embedded two-residual of Y_E. The plus map is I → I/O₂(I),
and the prescribed Sylow is the restriction of the original T. The preceding
local geometry is recorded separately from the outputs still needed from
classification: `CoreFacts` and `ParabolicMarking` are intermediate contracts,
not assumed conclusions of the source theorem.

The elementary source argument after the first classification is proved here.
The centralizer of E is a two-group, so core centralization of V_I identifies
O₂(I) = C_I(V_I). If Y⁺ normalized L₁⁺, the preimage L₁O₂(I) would centralize
V₁ and hence its Y-span E. This contradicts the preceding local fact that L₁
does not normalize E. We also retain the exact YT-span E for the terminal
point-seed application of H.5.5.

The local geometry is produced by qt-14-07-rechoice-local-geometry. The genuine
triple, five-chief-factor argument and B.2.14 application must construct
`CoreFacts`; the full B.5/F.6 comparison must construct `ParabolicMarking`.
Neither construction nor the rank-three conclusion is claimed in this module.
Final conditional assembly remains qt-14-07-rechoice-goldschmidt, and the
rank-four contradiction remains qt-14-07-critical-rechoice.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Lemma 14.7.70, printed pp.1074–1075 (PDF pp.1091–1092).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The preceding local geometry, before any Goldschmidt classification. -/
structure Geometry : Prop where
  rank_three : primeRank 2 d.U₀ = 3
  star_central : star F c.Uα ≤ Chapter12.Section08.centerIn (star F (T : Subgroup G))
  Zα_not_le : ¬ c.Zα ≤ V
  elementary : IsElementaryAbelian 2 (E c)
  rank_two : primeRank 2 (E c) = 2
  T_normalizes : (T : Subgroup G) ≤ normalizer (E c : Set G)
  span : E c = conjugateSpanBy (F.Vi 1) (Y c)
  YE_normalizes : YE c ≤ normalizer (E c : Set G)
  full_action : Function.Surjective
    ((E c).normalizerMonoidHom.comp (inclusion YE_normalizes))
  YE_normal : ((YE c).subgroupOf (normalizer (E c : Set G))).Normal
  centralizer_two : IsPGroup 2 (centralizer (E c : Set G))
  L₁_not_normalizes : ¬ F.Li L 1 ≤ normalizer (E c : Set G)

/-- The right generator in the source triple. -/
def YT : Subgroup G := Y c ⊔ (T : Subgroup G)
/-- Both vertices live on the actual generated subgroup I. -/
def left : Subgroup (I c) := (group F L).subgroupOf (I c)
def right : Subgroup (I c) := (YT c).subgroupOf (I c)
/-- The plus map is literally I → I/O₂(I). -/
def plusMap : I c →* ((I c) ⧸ pCore 2 (I c)) := QuotientGroup.mk' (pCore 2 (I c))
def plus (A : Subgroup G) : Subgroup ((I c) ⧸ pCore 2 (I c)) :=
  (A.subgroupOf (I c)).map (plusMap c)

/-- The actual quotient and its two incident parabolics, needed by H.5.5.
This is a classification output, not part of the preceding geometry. -/
structure ParabolicMarking where
  equiv : ((I c) ⧸ pCore 2 (I c)) ≃* Matrix.PSL3Two.SL
  point : (plus c (group F L)).map equiv.toMonoidHom = Matrix.PSL3Two.pointParabolicSL
  line : (plus c (YT c)).map equiv.toMonoidHom = Matrix.PSL3Two.lineParabolicSL

omit [Finite G] in
theorem T_le_I : (T : Subgroup G) ≤ I c := le_sup_right.trans le_sup_left
omit [Finite G] in
theorem Y_le_I : Y c ≤ I c := le_sup_right
omit [Finite G] in
theorem L₁_le_I : F.Li L 1 ≤ I c := le_sup_left.trans le_sup_left

def sylow : Sylow 2 (I c) := T.subtype (T_le_I c)
omit [Finite G] in
@[simp] theorem sylow_coe : (sylow c : Subgroup (I c)) =
    (T : Subgroup G).subgroupOf (I c) := rfl

omit [Finite G] in
theorem YT_le_I : YT c ≤ I c := sup_le (Y_le_I c) (T_le_I c)
omit [Finite G] in
theorem generators : group F L ⊔ YT c = I c := by
  apply le_antisymm
  · exact sup_le le_sup_left (YT_le_I c)
  · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)

omit [Finite G] in
theorem generated : left c ⊔ right c = ⊤ := by
  rw [left, right, ← subgroupOf_sup (show group F L ≤ I c from le_sup_left) (YT_le_I c), generators, subgroupOf_self]

/-- Any genuine triple on these generators has exactly the prescribed
ambient Sylow intersection, not merely an unmarked conjugate Sylow. -/
theorem intersection_eq_sylow (ht : ChapterF.IsGoldschmidtTriple (left c) (right c)) :
    left c ⊓ right c = (sylow c : Subgroup (I c)) := by
  obtain ⟨S, hS⟩ := ht.intersection_sylow
  have hT : (sylow c : Subgroup (I c)) ≤ left c ⊓ right c := by
    intro x hx
    exact ⟨(show (T : Subgroup G) ≤ group F L from le_sup_right) hx,
      (show (T : Subgroup G) ≤ YT c from le_sup_right) hx⟩
  rw [hS] at hT ⊢
  exact (sylow c).is_maximal' S.isPGroup' hT

include d in
theorem point_le_I : F.Vi 1 ≤ I c :=
  ((F.le_seed 1).trans d.natural.chosen.le_sylow).trans (T_le_I c)

include d in
theorem VI_le_I : VI c ≤ I c := conjugateSpanBy_le_self (point_le_I d c)

include d in
theorem VI_normal : ((VI c).subgroupOf (I c)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (VI_le_I d c)).mpr
    (le_normalizer_conjugateSpanBy _ _)

include d in
theorem group_centralizes_point : group F L ≤ centralizer (F.Vi 1 : Set G) := by
  rw [d.point, zpowers_eq_closure, centralizer_closure, ← d.centralizer_eq]
  exact group_le_H

/-- The first classification stage must construct these facts from Geometry
and the precise earlier source implications. They are not local assumptions. -/
structure CoreFacts : Prop where
  triple : ChapterF.IsGoldschmidtTriple (left c) (right c)
  nontrivial : pCore 2 (I c) ≠ ⊥
  elementary : IsElementaryAbelian 2 (VI c)
  centralizes : pCore 2 (I c) ≤ centralizer ((VI c).subgroupOf (I c) : Set (I c))

namespace Geometry
variable {d c} (h : Geometry d c)
include h

theorem T_normalizes_Y : (T : Subgroup G) ≤ normalizer (Y c : Set G) := by
  have hN : normalizer (E c : Set G) ≤ normalizer (YE c : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.YE_normalizes).mp h.YE_normal
  exact (h.T_normalizes.trans hN).trans
    (normalizer_le_normalizer_characteristic_image (YE c) (pResidual 2 (YE c)))

/-- Both generators of YT preserve the actual rank-two subgroup. -/
theorem YT_normalizes_E : YT c ≤ normalizer (E c : Set G) :=
  sup_le ((map_subtype_le (pResidual 2 (YE c))).trans h.YE_normalizes) h.T_normalizes

/-- The line-parabolic seed in H.5.5 is the literal E, even after adding T. -/
theorem span_point_YT : conjugateSpanBy (F.Vi 1) (YT c) = E c := by
  apply le_antisymm
  · exact conjugateSpanBy_le le_sup_left h.YT_normalizes_E
  · rw [h.span]
    exact conjugateSpanBy_mono le_rfl le_sup_left

theorem E_le_VI : E c ≤ VI c := by
  rw [h.span]
  exact conjugateSpanBy_mono le_rfl (Y_le_I c)

theorem E_le_I : E c ≤ I c := h.E_le_VI.trans (VI_le_I d c)

theorem VI_ne_E : VI c ≠ E c := by
  intro he
  apply h.L₁_not_normalizes
  rw [← he]
  exact (L₁_le_I c).trans (le_normalizer_conjugateSpanBy _ _)

omit h in
include d in
/-- The nontrivial core gives the genuine local family and full-known-simple SQTK. -/
theorem local_and_sqtk (hne : pCore 2 (I c) ≠ ⊥) :
    I c ∈ Chapter1.HOver G (T : Set G) ∧ IsSQTK KnownSimple.IsKnownSimple (I c) := by
  have hi : I c ∈ Chapter1.H G := by
    intro he
    exact hne (((pCore 2 (I c)).map_eq_bot_iff_of_injective (I c).subtype_injective).mp he)
  exact ⟨⟨hi, T_le_I c⟩, Chapter3.sqtk_of_mem_H d.counterexample.qtke hi⟩

/-- Once B.2.14 supplies core centralization, the two-group centralizer of E
identifies the entire kernel on the literal conjugate span. -/
theorem core_eq_centralizer
    (hcore : pCore 2 (I c) ≤ centralizer ((VI c).subgroupOf (I c) : Set (I c))) :
    pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) := by
  apply le_antisymm hcore
  let C := centralizer ((VI c).subgroupOf (I c) : Set (I c))
  let f : C →* centralizer (E c : Set G) :=
    ((I c).subtype.comp C.subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_iff.mpr
      intro e he
      have heI := h.E_le_I he
      have hc := mem_centralizer_iff.mp x.property (⟨e, heI⟩ : I c) (h.E_le_VI he)
      exact congrArg Subtype.val hc)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralizer (E c : Set G) => (z : G)) he
  have hp : IsPGroup 2 C := h.centralizer_two.of_injective f hf
  let := VI_normal d c
  exact le_sSup ⟨inferInstance, hp⟩

end Geometry

omit [Finite G] in
private theorem centralizes_span_of_normalizes_image
    {A B Z : Subgroup G} {D : Type*} [Group D] (f : G →* D)
    (hA : A ≤ centralizer (Z : Set G))
    (hker : f.ker ≤ centralizer (Z : Set G))
    (hn : B.map f ≤ normalizer (A.map f : Set D)) :
    A ≤ centralizer (conjugateSpanBy Z B : Set G) := by
  have hN : B ≤ normalizer ((A.map f).comap f : Set G) := by
    apply le_normalizer_iff.mpr
    intro b hb x hx
    change f (b * x * b⁻¹) ∈ A.map f
    rw [map_mul, map_mul, map_inv]
    exact le_normalizer_iff.mp hn (f b) (mem_map_of_mem f hb) (f x) hx
  have hC : (A.map f).comap f ≤ centralizer (Z : Set G) := by
    rw [comap_map_eq]
    exact sup_le hA hker
  exact (le_comap_map f A).trans
    (le_centralizer_conjugateSpanBy_of_normalizes _ _ _ hN hC)

/-- If Y⁺ normalized L₁⁺, its preimage L₁O₂(I) would centralize E.
This proves the source nonnormality assertion using the actual plus map. -/
theorem Y_plus_not_normalizes_L₁ (h : Geometry d c)
    (hcore : pCore 2 (I c) ≤ centralizer ((VI c).subgroupOf (I c) : Set (I c))) :
    ¬ plus c (Y c) ≤ normalizer (plus c (F.Li L 1) : Set ((I c) ⧸ pCore 2 (I c))) := by
  intro hn
  let A := (F.Li L 1).subgroupOf (I c)
  let B := (Y c).subgroupOf (I c)
  let Z := (F.Vi 1).subgroupOf (I c)
  have hA : A ≤ centralizer (Z : Set (I c)) := by
    intro a ha
    apply mem_centralizer_iff.mpr
    intro z hz
    apply Subtype.ext
    exact mem_centralizer_iff.mp (group_centralizes_point d ((show F.Li L 1 ≤ group F L from le_sup_left) ha)) z hz
  have hker : (plusMap c).ker ≤ centralizer (Z : Set (I c)) := by
    rw [plusMap, QuotientGroup.ker_mk']
    exact hcore.trans (centralizer_le (fun x hx => le_conjugateSpanBy _ _ hx))
  have hc := centralizes_span_of_normalizes_image (plusMap c) hA hker hn
  have hspan : (conjugateSpanBy Z B).map (I c).subtype = E c := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le (point_le_I d c),
      map_subgroupOf_eq_of_le (Y_le_I c), ← h.span]
  apply h.L₁_not_normalizes
  apply le_trans _ (centralizer_le_normalizer (E c : Set G))
  intro a ha
  apply mem_centralizer_iff.mpr
  intro e he
  rw [← hspan] at he
  obtain ⟨x, hx, rfl⟩ := he
  have hh := mem_centralizer_iff.mp
    (hc (show (⟨a, L₁_le_I c ha⟩ : I c) ∈ A from ha)) x hx
  exact congrArg Subtype.val hh

/-- In particular the actual L₁-image is nontrivial. -/
theorem L₁_plus_ne_bot (h : Geometry d c)
    (hcore : pCore 2 (I c) ≤ centralizer ((VI c).subgroupOf (I c) : Set (I c))) :
    plus c (F.Li L 1) ≠ ⊥ := by
  intro he
  apply Y_plus_not_normalizes_L₁ d c h hcore
  rw [he, normalizer_eq_top]
  exact le_top

/-- The first-stage output discharges the kernel input to the nonnormality
argument and supplies the full SQTK condition for the second classification. -/
theorem core_consequences (h : Geometry d c) (k : CoreFacts c) :
    IsSQTK KnownSimple.IsKnownSimple (I c) ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      ¬ plus c (Y c) ≤ normalizer (plus c (F.Li L 1) : Set ((I c) ⧸ pCore 2 (I c))) := by
  exact ⟨(Geometry.local_and_sqtk (d := d) (c := c) k.nontrivial).2,
    h.core_eq_centralizer k.centralizes,
    Y_plus_not_normalizes_L₁ d c h k.centralizes⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt
