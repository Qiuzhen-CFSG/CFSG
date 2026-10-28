module
public import Theory.SpecificGroups.AlternatingEight.ReducedCover
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The kernel bound for perfect central covers of A₈

A finite perfect central cover is quasisimple. Schur's universal double
cover maps onto it, so the original covering kernel has order dividing two.
The bound retains the given covering homomorphism.

Source: GLS III, Theorem5.2.3, applied to the original central attachment
in Aschbacher--Smith12.6.26, printed p.833.
-/

public section
namespace AlternatingEight
open Subgroup Theory.GroupTheory GLS3.Chapter5.SchurPresentation
/-- Schur's double cover bounds the kernel of every finite perfect central cover of A₈. -/
theorem central_cover_kernel_card_le_two
    {J : Type*} [Group J] [Finite J] (f : PerfectCentralCovering.Cover J (alternatingGroup (Fin 8))) :
    Nat.card f.toMonoidHom.ker ≤ 2 := by
  let : IsQuasisimple J := f.isQuasisimple
  let g : Covering J (alternatingGroup (Fin 8)) := f.toCovering
  have hc := theorem_5_2_3_b_universality 3 (by decide) (by decide)
  have hd := kernel_card_dvd_of_surjective_factor
    (schurAlternatingCovering 3).toMonoidHom g.toMonoidHom
    (hc.lift g).toMonoidHom (hc.lift g).surjective
    (congrArg Covering.toMonoidHom (hc.lift_fac g))
  rw [natCard_ker_schurAlternatingCovering] at hd
  exact Nat.le_of_dvd (by decide) hd
end AlternatingEight

