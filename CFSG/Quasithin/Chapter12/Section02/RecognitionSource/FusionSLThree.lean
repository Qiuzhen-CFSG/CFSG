module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionFixedLine
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeFusion

/-!
# Global TI for the original nonsplit binary SL₃ extension

The actual marked extension has a fixed subgroup of order two and one
L-orbit outside it. Under NoEscape the fixed involution is weakly closed
by the centralizer-order argument of FusionFixedLine. Thus its two nonzero
orbits cannot fuse, and local TI becomes global TI on the same V.

The extension datum concerns the original quotient L/O₂(L) and the original
V. Recovering this natural-quotient marking from the indecomposable
rank-four row of 12.2.2 remains an explicit representation-theoretic step;
this theorem does not claim the full unmarked row (b).
Source: Aschbacher--Smith 12.2.16, p.800, using B.4.8(2), p.91.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 Section04.SmallFusion
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked central-extension case has global TI without a global fusion premise. -/
theorem globalTI_of_slThree_extension
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222 K) (hnone : NoEscape L V)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) : IsTISubgroup V := by
  obtain ⟨z,hz1,hall⟩ := (Nat.card_eq_two_iff' (1 : fixedSubgroup L V)).mp
    (E.fixed_card_eq_two hne)
  have hz1' : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = (z : G) := by
    intro w hw hL
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hall ⟨w,hw,hL⟩
        (fun he => hw1 (congrArg Subtype.val he))))
  apply globalTI_of_transitive_off_fixed_line h D structural hnone
    z.property.1 hz1' z.property.2 hfixed
  intro x y hx hy hx1 hy1 hxz hyz
  exact E.transitive_nonfixed hne x y hx hy
    (fun hc => hxz ((hfixed x hx hc.2).resolve_left hx1))
    (fun hc => hyz ((hfixed y hy hc.2).resolve_left hy1))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
