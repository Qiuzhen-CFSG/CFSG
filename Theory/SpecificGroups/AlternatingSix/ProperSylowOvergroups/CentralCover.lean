module

public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Theory.GroupTheory.GeneralizedFitting.SolvableCentralLift
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Proper Sylow overgroups in perfect central covers of A₆

A proper subgroup of a perfect group cannot surject through a central
kernel: adjoining central elements cannot enlarge its derived subgroup.
Thus a proper Sylow-two overgroup maps to a proper Sylow-two overgroup
of A₆. The proved solvability and odd-core restrictions there lift to
F*(X) ≤ O₂(X)(X ∩ Z(L)), through the literal restricted homomorphism.

The argument includes subgroups omitting the centre and does not require
a splitting or a classification of central lifts.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.13,
printed p.74 (PDF p.85), the proper-overgroup step for the A₆ cover.
-/

public section
open Subgroup Theory.GroupTheory
namespace AlternatingSix.ProperSylowOvergroups
variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

/-- The corrected proper-overgroup bound in any actual perfect central cover of A₆. -/
theorem centralCover_fitting_bound
    (f : L →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center L) (S : Sylow 2 L) (X : Subgroup L)
    (hSX : (S : Subgroup L) ≤ X) (hX : X ≠ ⊤) :
    generalizedFitting X ≤ pCore 2 X ⊔ (center L).subgroupOf X := by
  let Y := X.map f
  let Q := S.mapSurjective hf
  have hQY : (Q : Subgroup (alternatingGroup (Fin 6))) ≤ Y := map_mono hSX
  have hY : Y ≠ ⊤ := by
    intro he
    apply hX
    apply top_unique
    apply perfect_le_of_map_le_of_central_kernel f hk (⊤ : Subgroup L) X
    change _ ≤ Y
    rw [he]
    exact le_top
  let q : X →* Y := f.subgroupMap X
  have hker : q.ker ≤ (center L).subgroupOf X := by
    intro x hx
    exact hk (congrArg Subtype.val hx)
  have hcentral : q.ker ≤ center X := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hker hx) y.val)
  let : Group.IsSolvable Y := isSolvable Q Y hQY hY
  exact (generalizedFitting_le_twoCore_sup_central_kernel q
    (f.subgroupMap_surjective X) hcentral (fun p hp hn => by
      let : Fact p.Prime := ⟨hp⟩
      exact odd_pCore_eq_bot Q Y hQY hY p hn)).trans (sup_le_sup_left hker _)
end AlternatingSix.ProperSylowOvergroups
