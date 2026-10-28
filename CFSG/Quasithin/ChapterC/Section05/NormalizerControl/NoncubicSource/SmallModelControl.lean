module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.Ambient
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.AlternatingSevenCentralCoverControl
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
/-!
# Exact normalizer bounds for the remaining small C.5.12 models

The marked normal component is A₇, its perfect central three-cover, or
PSL₂(25). Actual isomorphism transport preserves the Sylow stabilizer, and
the proved model theorems make its normalizer preserve S∩C(L). The ambient
conjugation kernel remains present; there is no faithful ambient-action premise.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {D : Type*} [Group D] [Finite D]
theorem psl25_model_sylow_stabilizer (hm : ClassicalGroup.IsPSL D 2 25)
    (T : Sylow 2 D) : IsPGroup 2 (MulAction.stabilizer (MulAut D) (T : Subgroup D)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hu := Theory.SpecificGroups.Classical.SylowMarkedSL2.psl25_sylow_stabilizer_isPGroup hF U
  let φ : MulAut D ≃* MulAut PSL(2,F) := MulAut.congr e
  let A := MulAction.stabilizer (MulAut D) (T : Subgroup D)
  let ψ : A →* MulAction.stabilizer (MulAut PSL(2,F)) (U : Subgroup PSL(2,F)) :=
    (φ.toMonoidHom.comp A.subtype).codRestrict _ (fun a => by
      change (U : Subgroup PSL(2,F)).map (φ a).toMonoidHom = U
      change ((T : Subgroup D).map e.toMonoidHom).map (φ a).toMonoidHom =
        (T : Subgroup D).map e.toMonoidHom
      rw [Subgroup.map_map]
      have he : (φ a).toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.val.toMonoidHom := by
        ext x
        change e (a.val (e.symm (e x))) = e (a.val x)
        rw [e.symm_apply_apply]
      rw [he,← Subgroup.map_map]
      exact congrArg (Subgroup.map e.toMonoidHom) a.property)
  exact hu.of_injective ψ (by
    intro a b he
    exact Subtype.ext (φ.injective (congrArg Subtype.val he)))

theorem psl25_model_normalizer_centralizer
    {H : Type*} [Group H] [Finite H] (D : Subgroup H) [D.Normal]
    (hm : ClassicalGroup.IsPSL D 2 25) (S : Sylow 2 H)
    (L : Subgroup H) (hLD : L ≤ D) (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) :
    normalizer (S : Set H) ≤ normalizer ((S : Subgroup H) ⊓ centralizer (L : Set H) : Set H) :=
  Theory.SpecificGroups.Classical.SylowMarkedSL2.normalizer_le_normalizer_centralizer_of_two_group_action
    D S (psl25_model_sylow_stabilizer hm) L hLD hSL
theorem small_model_normalizer_centralizer
    {H : Type*} [Group H] [Finite H] (D : Subgroup H) [D.Normal]
    (hm : Chapter1.Section02.LocalModels.IsAlternating D 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover D 7 ∨ ClassicalGroup.IsPSL D 2 25)
    (S : Sylow 2 H) (L : Subgroup H) (hLD : L ≤ D)
    (hSL : (S : Subgroup H) ≤ normalizer (L : Set H)) :
    normalizer (S : Set H) ≤ normalizer ((S : Subgroup H) ⊓ centralizer (L : Set H) : Set H) := by
  rcases hm with hm | hm | hm
  · obtain ⟨e⟩ := hm
    have hn := AlternatingSevenNormal.sylow_normalizer_le D e S
    have hnL := hn.trans (sup_le hSL ((centralizer_le hLD).trans (Subgroup.centralizer_le_normalizer _)))
    exact (le_inf le_rfl (hnL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  · obtain ⟨hq,_,⟨e⟩⟩ := hm
    let : Group.IsPerfect D := hq.1
    exact AlternatingSevenCentralCover.sylow_normalizer_le_marked_centralizer D e S L hLD hSL
  · exact psl25_model_normalizer_centralizer D hm S L hLD hSL
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
