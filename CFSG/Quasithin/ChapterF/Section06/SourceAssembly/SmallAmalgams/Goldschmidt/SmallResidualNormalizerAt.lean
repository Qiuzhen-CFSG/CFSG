module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SmallResidualNormalizer
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Reorientation

/-!
# The shared cubic normalizer argument in either orientation

Reorient the original cubic action to apply the normal-Sylow-three argument
at either endpoint, preserving the literal ambient Sylow image. The false
endpoint uses the original theorem, while the true endpoint uses the proved
swap of the same action and tree.

Source: Goldschmidt (4.4), *Automorphisms of trivalent graphs* (1980), p.393.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.normal_three_of_opposite_normalized_sylow_at
    (h : CubicTreeAction F) (i : Bool) (H : Subgroup G) (hHA : H ≤ F i)
    (P : Sylow 2 H)
    (hPT : (P : Subgroup H).map H.subtype ≤ F false ⊓ F true)
    (hBN : F (!i) ≤ normalizer ((P : Subgroup H).map H.subtype : Set G))
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    ∀ S : Sylow 3 H, S.Normal := by
  cases i
  · exact h.normal_three_of_opposite_normalized_sylow H hHA P hPT hBN e
  · exact h.swap.normal_three_of_opposite_normalized_sylow H hHA P
      (by simpa only [RankTwo.swapFamily, Bool.not_false, Bool.not_true, inf_comm] using hPT)
      hBN e

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
