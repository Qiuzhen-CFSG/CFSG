module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourRigidity
public import Theory.GroupAction.RankTwoCosetCover.QuadrangleMatching

/-!
# Full nonbinary unitary-four extension recognition

The actual order-bound completion and the original extension have the same
marked reflection relation. Their paired completion inherits the whole
overlap and native five-path action, and this common Weyl relation makes
it a quadrangle. The two genuine covers are therefore isomorphisms.
This proves identification with the original extension in this nonbinary
family, a strengthening justified by the proved canonical alignment, not
by source Remark F.4.9. In particular it gives the requested some-extension
recognition and exact order, retaining q = 4 and even outer degree.

For a simple ambient completion, the normal faithful native PSU₄ subgroup
is the whole group. Source: Aschbacher–Smith F.4.8–10,13,16–17,24,
printed pp.278–283,287. No polygon classification axiom is used.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "J" => UnitaryFourFlag.form F σ hσ

private theorem reversed_fourth {G : Type*} [Group G] (s t : G)
    (h : (t*s)^4=1) : (s*t)^4=1 := by
  calc
    (s*t)^4 = (s*(t*s)*s⁻¹)^4 := by congr 1; group
    _ = s*((t*s)^4)*s⁻¹ := conj_pow
    _ = 1 := by rw [h]; simp

/-- The marked common-cover proof identifies this nonbinary completion with
the original extension. This strengthening is justified by the actual proved
canonical Weyl relation; it is not an invocation of source Remark F.4.9. -/
theorem nonempty_mulEquiv_extension (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* E.carrier) := by
  let : Finite (ProjectiveGroup m hm) := Finite.of_surjective (projection m hm)
    (project_surjective F J)
  let d := E.completion (parabolics_generate m hm)
  have hd := E.completion_overlap (parabolics_generate m hm)
  let s := E.nativeLeft (point m hm)
  let t := E.nativeRight (plane m hm)
  apply c.nonempty_mulEquiv_of_matching_quadrangle d ho hd
    (four_completion_quadrangle m hm hmgt E c ho hcard).1
    (four_completion_quadrangle m hm hmgt E d hd le_rfl).1
    (four_completion_rootPathTransitive_five m hm E (c.pairCompletion d) (c.pair_whole_overlap d ho)) s t
  · change E.nativeLeft (point m hm)^2=1
    rw [←map_pow,point_sq,map_one]
  · change E.nativeRight (plane m hm)^2=1
    rw [←map_pow,plane_sq,map_one]
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.left_injective hb)
    change b.val=MulAut.conj (point m hm).val at he
    have hmem : MulAut.conj (point m hm).val∈E.right := he ▸ b.property.2
    have hp := (E.conj_mem_right_iff (four_conj_injective m hm) _).mp hmem
    exact middleSwap_not_mem_plane F σ hσ ((mem_map_iff_mem (projection_injective m hm)).mp hp)
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.right_injective
      ((DFunLike.congr_fun c.compatible b).symm.trans hb))
    change b.val=MulAut.conj (plane m hm).val at he
    have hmem : MulAut.conj (plane m hm).val∈E.left := he ▸ b.property.1
    have hp := (E.conj_mem_left_iff (four_conj_injective m hm) _).mp hmem
    exact pairSwap_not_mem_point F σ hσ ((mem_map_iff_mem (projection_injective m hm)).mp hp)
  · exact reversed_fourth _ _ (rotation_fourth_eq_one m hm hmgt E c ho hcard)
  · exact reversed_fourth _ _ (rotation_fourth_eq_one m hm hmgt E d hd le_rfl)

/-- F.4.24 for the full nonbinary U₄ extension, including the actual q=4
and even outer-degree cases. The output is a faithful type-preserving
automorphism extension containing the whole native inner group. -/
theorem recognized_extension (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    Nat.card M=Nat.card E.carrier ∧
    ∃ a : M →* MulAut (ProjectiveGroup m hm), Function.Injective a ∧
      inner (ProjectiveGroup m hm)≤a.range ∧
      ∀ g : M, PreservesTypes (pointParabolic m hm) (planeParabolic m hm) (a g) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_extension m hm hmgt E c ho hcard
  let a := E.carrier.subtype.comp e.toMonoidHom
  refine ⟨Nat.card_congr e.toEquiv,a,E.carrier.subtype_injective.comp e.injective,?_,?_⟩
  · have hr : a.range=E.carrier := by
      rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.surjective,←MonoidHom.range_eq_map,
        range_subtype]
    rw [hr]
    exact E.contains_inner
  · intro g
    exact E.preserves_types _ (e g).property

/-- Ambient simplicity makes the recognized faithful normal native group all
of the completion, without a simplicity certificate for the native model. -/
theorem nonempty_mulEquiv_native_of_simple (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M] [IsSimpleGroup M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* ProjectiveGroup m hm) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_extension m hm hmgt E c ho hcard
  let d := E.completion (parabolics_generate m hm)
  have hbase : E.baseHom.range=E.innerGenerated d := by
    change E.baseHom.range=(E.innerLeft d).range ⊔ (E.innerRight d).range
    have hl : E.innerLeft d=E.baseHom.comp (pointParabolic m hm).subtype := rfl
    have hr : E.innerRight d=E.baseHom.comp (planeParabolic m hm).subtype := rfl
    rw [hl,hr,MonoidHom.range_comp,MonoidHom.range_comp,range_subtype,range_subtype,
      ←Subgroup.map_sup,parabolics_generate,←MonoidHom.range_eq_map]
  let f : ProjectiveGroup m hm →* M := e.symm.toMonoidHom.comp E.baseHom
  have hfi : Function.Injective f := e.symm.injective.comp (E.baseHom_injective (four_conj_injective m hm))
  have hnorm : f.range.Normal := by
    rw [MonoidHom.range_comp,hbase]
    exact (E.innerGenerated_normal d (four_conj_injective m hm)).map e.symm.toMonoidHom e.symm.surjective
  have hne : f.range≠⊥ := by
    intro hb
    have he : f (point m hm).val=1 := mem_bot.mp (hb ▸ (show f (point m hm).val∈f.range from ⟨_,rfl⟩))
    have hp : (point m hm).val=1 := hfi (he.trans (map_one f).symm)
    have hmem : (point m hm).val∈planeParabolic m hm := hp ▸ one_mem _
    exact middleSwap_not_mem_plane F σ hσ ((mem_map_iff_mem (projection_injective m hm)).mp hmem)
  have htop : f.range=⊤ := hnorm.eq_bot_or_eq_top.resolve_left hne
  exact ⟨(MulEquiv.ofBijective f ⟨hfi,MonoidHom.range_eq_top.mp htop⟩).symm⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
