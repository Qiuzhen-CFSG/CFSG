module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection
public import Theory.GroupTheory.ElementaryThompsonFrattini
/-!
# The central omega subgroup of the Baumann subgroup

The Baumann subgroup lies between J(T) and T, so it has the same elementary
Thompson subgroup. Its central omega subgroup is therefore contained in
alpha(T). Conversely alpha(T) is elementary and central in its own centralizer.
This identifies the actual E in the positive fixed-center argument of 10.2.1.

Source: Aschbacher–Smith B.2.2–3 and 10.2.1, printed pp.74–75 and743.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]
theorem omegaCenter_baumann_eq_thompsonAlpha (T : Subgroup G) :
    omegaOneCenterAmbient (baumann T) = thompsonAlpha T := by
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hA => hA.1
  have hJB : elementaryAbelianMaxJ T ≤ baumann T := by
    apply le_inf hJT
    apply le_centralizer_iff.mpr
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hJ : elementaryAbelianMaxJ (baumann T) = elementaryAbelianMaxJ T :=
    elementaryAbelianMaxJ_eq_of_intermediate T (baumann T) hJB inf_le_left
  apply le_antisymm
  · simpa only [hJ, thompsonAlpha] using omegaCenter_le_omegaCenter_maxJ (baumann T)
  · intro z hz
    obtain ⟨hzJ,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨⟨hJT hzJ,?_⟩,hz2,?_⟩
    · intro w hw
      exact hzC w ((mem_omegaOneCenterAmbient_iff _ _).mp hw).1
    · intro b hb
      exact (hb.2 z hz).symm
end CFSG.Quasithin.ChapterB
