module

public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Nonsolvable
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.Kernel

/-!
# The full kernel of a nonsolvable reduced omega action

For the original reduced normal module moved by the Thompson subgroup,
the orbit centralizer is exactly the minimal-parabolic core in the
nonsolvable case. The faithful quotient is an FF action with trivial
solvable radical. Mapping the original core to that radical gives the
reverse containment to the reduced-kernel theorem.

This concerns the full centralizer, not just its Sylow intersection.
It does not identify this kernel with the two-core of the original group.
Source: Aschbacher--Smith B.6.8--10 and E.2.3.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G]

theorem nonsolvable_core_eq_centralizer
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    ChapterB.minimalParabolicCore T hP = centralizer (U : Set G) := by
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans_eq he.symm
  obtain ⟨hk,hp⟩ := ChapterB.minimalParabolic_reduced_image T hP q hq
    hU.quotient_pCore_eq_bot hn
  have hi : ¬ Group.IsSolvable (G ⧸ C) := by
    intro hi
    let := hi
    let := ChapterB.minimalParabolic_core_solvable T hP
    let : Group.IsSolvable q.ker :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
    exact hs (Group.isSolvable_of_ker_le_range q.ker.subtype q (by rw [range_subtype]))
  let ρ := NormalElementaryQuotient.representation U q hq (QuotientGroup.ker_mk' C)
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hff,_,_,_⟩ := ChapterB.lemma_B_2_7 U q hq
      (QuotientGroup.ker_mk' C) T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  let c : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (G ⧸ C) := {
    Cover := G
    kernel := C
    sqtk := hG
    equiv := MulEquiv.refl _ }
  have hz := ChapterB.minimalParabolic_nonsolvable_ff_radical_eq_bot ρ
    (T.mapSurjective hq) hp hi hU.quotient_pCore_eq_bot
    (NormalElementaryQuotient.representation_injective U q hq (QuotientGroup.ker_mk' C))
    hff ⟨c⟩
  have hm := ChapterB.minimalParabolicCore_map_core T hP q hq hk
  rw [ChapterB.minimalParabolic_nonsolvable_core_eq_radical _ _ hi,hz] at hm
  have hle := (Subgroup.map_eq_bot_iff _).mp hm
  rw [QuotientGroup.ker_mk'] at hk hle
  exact le_antisymm hle hk

end CFSG.Quasithin.ChapterE.ThompsonAction
