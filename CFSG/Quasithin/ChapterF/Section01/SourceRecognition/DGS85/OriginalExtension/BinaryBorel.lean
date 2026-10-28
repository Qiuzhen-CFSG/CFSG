module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration

/-!
# No original enlargement when the reduced Borel is a two-group

The reduced Borel is normal in the original one, and the original Borel is
its product with S. Thus a reduced two-group Borel makes the original Borel
a two-group. Its two-core is the whole Borel; since that core is contained
in S, the original S and the reduced S coincide. Both endpoints and the
full overlap consequently coincide, preserving all reduced markings.

This is the F.1.1 specialization of the K = 1 conclusion in DGS (15.1)(d),
printed p.226. It uses the actual source reduction; it asserts no recognition
of a binary structural type as a concrete group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryBorel
open SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
  (hB : IsPGroup 2 (commonBorel L (reducedSylow L S)))

include h hB
/-- The normal reduced Borel and the original S generate a two-group. -/
theorem original_borel_isPGroup : IsPGroup 2 (commonBorel L S) := by
  rw [← reduced_borel_supplement h]
  exact hB.to_sup_of_normal_left' h.S_isP
    ((show S ≤ commonBorel L S from le_sup_right).trans (borel_normalizes_reduced h))

/-- No original Sylow enlargement remains when the full reduced Borel is a
two-group; the comparison is between the literal original subgroups. -/
theorem original_sylow_eq_reduced : S = reducedSylow L S := by
  have hb := original_borel_isPGroup h hB
  have htop : pCore 2 (commonBorel L S) = ⊤ := by
    apply top_unique
    exact le_sSup ⟨inferInstance,hb.to_subgroup _⟩
  have hc : reducedSylow L S = commonBorel L S := by
    change (pCore 2 (commonBorel L S)).map (commonBorel L S).subtype = _
    rw [htop, ← MonoidHom.range_eq_map, range_subtype]
  exact le_antisymm ((show S ≤ commonBorel L S from le_sup_right).trans hc.symm.le)
    (reducedSylow_le h)

/-- Identity on every original ambient element restores the whole diagram. -/
@[expose] def originalIsoReduced : Iso (originalAmalgam L S) (reducedAmalgam L S) :=
  NativeRestoration.originalIsoReduced (original_sylow_eq_reduced h hB)

/-- All original Borel elements are already in the reduced Borel. -/
theorem original_borel_eq_reduced :
    commonBorel L S = commonBorel L (reducedSylow L S) :=
  congrArg (commonBorel L) (original_sylow_eq_reduced h hB)

/-- A supplied reduced marking is unchanged on both endpoints and the full
middle after restoration. This applies in either supplied orientation. -/
theorem originalIsoReduced_trans_reduced
    {A D C : Type*} [Group A] [Group D] [Group C]
    {α : RankTwoAmalgam A D C} (e : Iso (reducedAmalgam L S) α) :
    (∀ x : parabolic L (reducedSylow L S) 0,
      ((originalIsoReduced h hB).trans e).left
        (inclusion (reduced_parabolic_le h 0) x) = e.left x) ∧
    (∀ x : commonBorel L (reducedSylow L S),
      ((originalIsoReduced h hB).trans e).middle
        (inclusion (reduced_commonBorel_le h) x) = e.middle x) ∧
    (∀ x : parabolic L (reducedSylow L S) 1,
      ((originalIsoReduced h hB).trans e).right
        (inclusion (reduced_parabolic_le h 1) x) = e.right x) :=
  NativeRestoration.originalIsoReduced_trans_reduced h
    (original_sylow_eq_reduced h hB) e

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.BinaryBorel
