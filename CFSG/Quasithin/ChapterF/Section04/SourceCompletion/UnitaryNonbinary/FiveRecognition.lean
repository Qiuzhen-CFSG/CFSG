module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveRigidity
public import Theory.GroupAction.RankTwoCosetCover.QuadrangleMatching

/-!
# Recognition of full PSU₅(4) extension completions

The actual marked Weyl relation holds in the completion and in the native
extension. Their paired common cover inherits the five-path action; the
matching involutions make both covering maps isomorphisms. This identifies
the completion with a faithful type-preserving extension containing PSU₅(4)
and proves equality of the full carrier orders. The stronger identification
with the given extension follows from proved alignment, not Remark F.4.9.

Ambient simplicity then makes the faithful normal native subgroup the whole
group. The field has order sixteen and the scalar kernel has order five.
Source: Aschbacher–Smith F.4.8–10,13,16–17,24, pp.278–283,287.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive
variable (U : GreenBook.UnitaryFive.Model 4)

private theorem reversed_fourth {G : Type*} [Group G] (s t : G)
    (h : (t*s)^4=1) : (s*t)^4=1 := by
  calc
    (s*t)^4 = (s*(t*s)*s⁻¹)^4 := by congr 1; group
    _ = s*((t*s)^4)*s⁻¹ := conj_pow
    _ = 1 := by rw [h]; simp

/-- The marked common-cover proof identifies this PSU₅(4) completion with
the original extension. This strengthening is justified by the actual proved
canonical Weyl relation; it is not an invocation of source Remark F.4.9. -/
theorem nonempty_mulEquiv_extension (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* E.carrier) := by
  obtain ⟨t,ht⟩ := Chapter5.UnitaryNativeLift.Five.exists_trace_parameter U
  let d := E.completion (Chapter5.UnitaryNativeLift.Five.parabolics_generate U)
  have hd := E.completion_overlap (Chapter5.UnitaryNativeLift.Five.parabolics_generate U)
  let s := E.nativeLeft (point U t ht)
  let r := E.nativeRight (plane U t ht)
  apply c.nonempty_mulEquiv_of_matching_quadrangle d ho hd
    (five_completion_quadrangle U E c ho hcard).1
    (five_completion_quadrangle U E d hd le_rfl).1
    (five_completion_rootPathTransitive_five U E (c.pairCompletion d) (c.pair_whole_overlap d ho)) s r
  · change E.nativeLeft (point U t ht)^2=1
    rw [←map_pow,point_sq,map_one]
  · change E.nativeRight (plane U t ht)^2=1
    rw [←map_pow,plane_sq,map_one]
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.left_injective hb)
    change b.val=MulAut.conj (point U t ht).val at he
    have hmem : MulAut.conj (point U t ht).val∈E.right := he ▸ b.property.2
    have hp := (E.conj_mem_right_iff (five_conj_injective U) _).mp hmem
    exact Chapter5.UnitaryNativeLift.Five.point_out U t ht hp
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.right_injective
      ((DFunLike.congr_fun c.compatible b).symm.trans hb))
    change b.val=MulAut.conj (plane U t ht).val at he
    have hmem : MulAut.conj (plane U t ht).val∈E.left := he ▸ b.property.1
    have hp := (E.conj_mem_left_iff (five_conj_injective U) _).mp hmem
    exact Chapter5.UnitaryNativeLift.Five.plane_out U t ht hp
  · exact reversed_fourth _ _ (rotation_fourth_eq_one U t ht E c ho hcard)
  · exact reversed_fourth _ _ (rotation_fourth_eq_one U t ht E d hd le_rfl)

/-- F.4.24 for the full PSU₅(4) extension, including arbitrary even outer degree. The output is a faithful type-preserving
automorphism extension containing the whole native inner group. -/
theorem recognized_extension (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    Nat.card M=Nat.card E.carrier ∧
    ∃ a : M →* MulAut (U.Carrier), Function.Injective a ∧
      inner (U.Carrier)≤a.range ∧
      ∀ g : M, PreservesTypes (U.leftParabolic) (U.rightParabolic) (a g) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_extension U E c ho hcard
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
theorem nonempty_mulEquiv_native_of_simple (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M] [IsSimpleGroup M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* U.Carrier) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_extension U E c ho hcard
  let d := E.completion (Chapter5.UnitaryNativeLift.Five.parabolics_generate U)
  have hbase : E.baseHom.range=E.innerGenerated d := by
    change E.baseHom.range=(E.innerLeft d).range ⊔ (E.innerRight d).range
    have hl : E.innerLeft d=E.baseHom.comp (U.leftParabolic).subtype := rfl
    have hr : E.innerRight d=E.baseHom.comp (U.rightParabolic).subtype := rfl
    rw [hl,hr,MonoidHom.range_comp,MonoidHom.range_comp,range_subtype,range_subtype,
      ←Subgroup.map_sup,Chapter5.UnitaryNativeLift.Five.parabolics_generate,←MonoidHom.range_eq_map]
  let f : U.Carrier →* M := e.symm.toMonoidHom.comp E.baseHom
  have hfi : Function.Injective f := e.symm.injective.comp (E.baseHom_injective (five_conj_injective U))
  have hnorm : f.range.Normal := by
    rw [MonoidHom.range_comp,hbase]
    exact (E.innerGenerated_normal d (five_conj_injective U)).map e.symm.toMonoidHom e.symm.surjective
  obtain ⟨t,ht⟩ := Chapter5.UnitaryNativeLift.Five.exists_trace_parameter U
  have hne : f.range≠⊥ := by
    intro hb
    have he : f (point U t ht).val=1 := mem_bot.mp (hb ▸ (show f (point U t ht).val∈f.range from ⟨_,rfl⟩))
    have hp : (point U t ht).val=1 := hfi (he.trans (map_one f).symm)
    have hmem : (point U t ht).val∈U.rightParabolic := hp ▸ one_mem _
    exact Chapter5.UnitaryNativeLift.Five.point_out U t ht hmem
  have htop : f.range=⊤ := hnorm.eq_bot_or_eq_top.resolve_left hne
  exact ⟨(MulEquiv.ofBijective f ⟨hfi,MonoidHom.range_eq_top.mp htop⟩).symm⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
