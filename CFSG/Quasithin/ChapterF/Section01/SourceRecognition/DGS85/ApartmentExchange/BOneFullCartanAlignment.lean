module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanTransport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.NaturalExchange

/-!
# Aligned source paths for the whole-Cartan roots

The whole-Cartan reflection profile records an actual source path and the
root element used to construct the reflection.  The transport theorem needs
the three geometric markings of that same path: its selected length, its
predecessor at the marked edge, and pointwise fixation by the compatible
Cartan.  This module packages precisely those source clauses and applies the
transport to both orientations at once.

The central factor in the nontrivial-center branch is retained.  The
centerless specialization removes it only from the source center hypothesis;
it does not identify a local permutation kernel with `O₂` or add an exchange
or quotient-root-sign premise.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and
(14.1)--(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (d : ∀ i : Bool, FullCartanReflectionProfile.{uF} h c i)

local notation "n" => fullCartanPathLength d
local notation "hn" => fullCartanPathLength_gt d
local notation "t" => fullCartanReflections d
local notation "ρ" => fullCartanPathRoots d

/-- The exact path markings needed to transport a supplied source root to the
constructed whole-Cartan root.  Each field refers to the path stored in the
same profile `d i`.
-/
structure FullCartanPathAlignment where
  length : ∀ i, (d i).path.length = fullCartanPathLength d
  previous : ∀ i,
    (d i).path.penultimate =
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i)
  fixed : ∀ i,
    cartan c ≤ pathFixer (X := (reducedAmalgam L S).Universal) (d i).path

variable {d}

include h c in
/-- Natural coordinates on the two canonical length-`2 n` exchange paths
give chosen-apartment exchange for the same whole-Cartan reflection group.
The coordinate witnesses and quotient root signs remain explicit. -/
theorem fullCartan_natural_exchange
    (htwo : ∀ i : Bool, Nonempty (NaturalPathCoordinates.{uF}
      (exchangePath c n hn t (fullCartanReflections_fix d)
        (fullCartanReflections_move d) (fullCartanReflections_normalize d) i) n
      (cartan c)))
    (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length = n + 1 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p))) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c ρ)) n := by
  have hgroup : apartmentGroup c ρ = reflectionGroup c t := by
    apply le_antisymm
    · rw [apartmentGroup]
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | ⟨i, rfl⟩)
      · exact Subgroup.subset_closure (Or.inl hx)
      · exact Subgroup.subset_closure (Or.inr ⟨i, (fullCartanRoots_reflection d i).symm⟩)
    · rw [reflectionGroup]
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | ⟨i, rfl⟩)
      · exact Subgroup.subset_closure (Or.inl hx)
      · exact Subgroup.subset_closure (Or.inr ⟨i, (fullCartanRoots_reflection d i)⟩)
  rw [hgroup]
  intro a b p hp hl hT g hg hmove
  exact source_natural_exchange h c n hn t (fullCartanReflections_fix d)
    (fullCartanReflections_move d) (fullCartanReflections_square d)
    (fullCartanReflections_normalize d) (fullCartanProfiles_path_transitive d)
    (fullCartanProfiles_thickness d) hodd htwo p hp hl hT g hg hmove

include d in
/-- Exact source-root conjugacy for either orientation, with the actor-center
factor retained in the formula. -/
theorem fullCartanRoots_actual_conjugacy_of_alignment
    (a : FullCartanPathAlignment d) (i : Bool) :
    ∃ y ∈ (fullCartanPathRoots d i).root, orderOf y = 2 ∧
      ∃ z ∈ centerIn (universalBOneActor h i (d i).data),
        bOne_tree_map h z ∈ Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
        ∃ g ∈ universalBOneActor h i (d i).data,
          g * (z * y) * g⁻¹ = (fullCartanPathRoots d i).reflection := by
  exact fullCartanRoots_actual_conjugacy d i (a.length i) (a.previous i) (a.fixed i)

include d in
/-- Simultaneous source-root conjugacy for the two marked orientations. -/
theorem fullCartanRoots_actual_conjugacy_both
    (a : FullCartanPathAlignment d) :
    ∀ i : Bool,
      ∃ y ∈ (fullCartanPathRoots d i).root, orderOf y = 2 ∧
        ∃ z ∈ centerIn (universalBOneActor h i (d i).data),
          bOne_tree_map h z ∈ Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
          ∃ g ∈ universalBOneActor h i (d i).data,
            g * (z * y) * g⁻¹ = (fullCartanPathRoots d i).reflection := by
  intro i
  exact fullCartanRoots_actual_conjugacy_of_alignment a i

include d in
/-- In a centerless actor, the same aligned paths give exact conjugacy by an
actor element. -/
theorem fullCartanRoots_actual_conjugacy_of_alignment_of_center_eq_bot
    (a : FullCartanPathAlignment d) (i : Bool)
    (hcenter : centerIn (d i).data.actor = ⊥) :
    ∃ y ∈ (fullCartanPathRoots d i).root, orderOf y = 2 ∧
      ∃ g ∈ universalBOneActor h i (d i).data,
        g * y * g⁻¹ = (fullCartanPathRoots d i).reflection := by
  exact fullCartanRoots_actual_conjugacy_of_center_eq_bot d i
    (a.length i) (a.previous i) (a.fixed i) hcenter

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
