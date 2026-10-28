module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SourceDegrees
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourceConsumer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarked
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Sieve
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueFourNormal

/-!
# Assembly of the original terminal component catalogue

The larger-actor degree theorem and four-dimensional component recognition,
together with the original A₆ exclusion, give an actual A₅ local lift or the
G₂(2)' quotient row. The original quotient sieve excludes the latter.

In the small-actor branch we select the original homogeneous constituent
with its orthogonal data. The completed exchanged-image theorem handles a
point outside that constituent. Only recognition on the marked constituent
remains an explicit input. This input belongs to the marked-image producer;
no degree, exchanged-image, kernel, or A₆ callback remains. The final sieve
returns the actual A₅ or L₂(8) lift on the original ambient carrier.

This is a conditional catalogue assembly, not terminal solvability. Its
remaining marked recognition and the A₅/L₂(8) exclusions are discharged by
the terminal-solvability owner and its independent source producers.
Source: Aschbacher–Smith 14.3.13–15, printed pp.993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The source quotient sieve excludes the degree-six full G₂(2) row.
Thus every original nonsolvable larger-actor action has degree four. -/
theorem degree_eq_four : finrank (ZMod 2) (Additive F.Uhat) = 4 := by
  rcases s.degree_cases with ⟨hd,_⟩ | ⟨hd,hm,⟨eG⟩⟩
  · exact hd
  · obtain ⟨K,hK,hn,⟨eK⟩,hk⟩ := source_component_large_actor_of_six_three
      s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups
      s.seed_card s.centralizer_quotient.some F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hm eG
    exact (source_excluded_quotient_row_false s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
      s.not_model F g K hK (hK.eq_conjugateSpanBy_of_image_normal hn)
      (Or.inl ⟨(hK.twoCoreQuotientEquivDot_of_restricted_kernel hk).trans eK⟩)).elim

/-- The original larger-actor branch supplies an actual ambient A₅ lift.
Both the A₆ image and the full G₂(2) alternative are excluded internally. -/
theorem exists_a5_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) := by
  let e := s.centralizer_quotient.some
  rcases s.component_of_source_four (fun K hK he =>
      source_terminal_a6_false s.simple T s.empty s.maximal s.unique_overgroup
        s.many_overgroups s.seed_card e s.not_model F s.nonabelian g
        s.parabolic_mem s.normalizer_not_mem hK he.some) with
    ⟨D,hD,hmove,he⟩ | ⟨K,hK,hn,⟨eK⟩,hk⟩
  · obtain ⟨K,hKH,hlocal,hcomp,himage,_,hspan⟩ :=
      Recognition.terminal_component_lift s.simple F (by decide) D hD
    change F.terminalDot K = D at himage
    exact ⟨K,⟨hKH,hlocal,hcomp,himage.symm ▸ hD,himage.symm ▸ hmove,hspan⟩,
      himage.symm ▸ he⟩
  · exact (source_excluded_quotient_row_false s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card e s.not_model F g K hK
      (hK.eq_conjugateSpanBy_of_image_normal hn)
      (Or.inl ⟨(hK.twoCoreQuotientEquivDot_of_restricted_kernel hk).trans eK⟩)).elim

/-- The larger-actor A₅ lift is normalized. Its exclusion therefore uses
only the normalized field-four branch, not tensor recognition. -/
theorem exists_normalized_a5_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∧
      K = conjugateSpanBy K (T : Subgroup G) := by
  obtain ⟨K,hK,⟨e5⟩⟩ := s.exists_a5_lift
  exact ⟨K,hK,⟨e5⟩,
    hK.eq_conjugateSpanBy_of_a5_of_four s.hypothesis s.degree_eq_four e5⟩

end LargeActorSource

section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hyp

/-- Any genuinely exchanged A₅ lift belongs to the small-actor branch.
This conclusion precedes, and does not assume, its tensor realization. -/
theorem source_exchanged_a5_small_actor_of_non_normalized
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K ≠ conjugateSpanBy K (T : Subgroup G)) :
    finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1 := by
  by_contra hm
  let s : LargeActorSource T M Mc F g B v :=
    ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,
      hK.terminal_not_solvable,hyp,hm⟩
  exact hspan (hK.eq_conjugateSpanBy_of_a5_of_four hyp s.degree_eq_four e5)

/-- The complete original catalogue join, conditional only on the marked
constituent recognition owned by `qt-e-14315-component-marked-images`. -/
theorem source_component_catalogue_of_marked_images
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (hmarked : ∀ (L : Subgroup F.TerminalHdot)
      (I : Submodule (ZMod 2) (Additive F.Uhat))
      (s : MarkedSource T M Mc F g B v L I), s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K := by
  classical
  by_cases hm : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  · have hfit := Recognition.original_terminal_fitting_centralizer_ne_bot
      hG T hempty hM hu hmany hcard e F hne g hgP hgH hn
    obtain ⟨L,hL,hmove,hs,ho⟩ := hyp.exists_moved_component_orthogonal_selection hn hfit
    obtain ⟨hfix,hcom,I,hI,hirr,hspan,hdis,hform,hdim,hind⟩ := hs
    by_cases hv : v ∈ I
    · let s : MarkedSource T M Mc F g B v L I :=
        ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm,
          hL,hmove,ho,hfix,hcom,hI,hirr,hspan,hdis,hform,hdim,hind,hv⟩
      exact s.local_lift_of_image_cases (hmarked L I s)
    · exact source_exchanged_component_local_lift hG T hempty hM hu hmany hcard e hnot
        F hne g hgP hgH hn hyp hm hL hmove ho hfix hcom hI hirr hspan hdis
        hform hdim hind hv
  · let s : LargeActorSource T M Mc F g B v :=
      ⟨hG,hempty,hM,hu,hmany,hcard,⟨e⟩,hnot,hne,hgP,hgH,hn,hyp,hm⟩
    obtain ⟨K,hK,he,_⟩ := s.exists_normalized_a5_lift
    exact ⟨K,hK,Or.inr (Or.inl (Or.inl he))⟩

/-- The actual source sieve removes all completed large rows and A₆.
Its two surviving rows are exactly the remaining A₅ and L₂(8) exclusions. -/
theorem source_component_a5_or_eight_of_marked_images
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    (hmarked : ∀ (L : Subgroup F.TerminalHdot)
      (I : Submodule (ZMod 2) (Additive F.Uhat))
      (s : MarkedSource T M Mc F g B v L I), s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      (Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 5)) ∨ EightImageRow F K) := by
  obtain ⟨K,hK,hcases⟩ := source_component_catalogue_of_marked_images
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hyp hn hmarked
  rcases source_component_cases_reduce hG T hempty hM hu hmany hcard e hnot
      F g K hK hcases with hs | h8
  · rcases hs with h5 | h6
    · exact ⟨K,hK,Or.inl h5⟩
    · exact (source_terminal_a6_false hG T hempty hM hu hmany hcard e hnot
        F hne g hgP hgH hK h6.some).elim
  · exact ⟨K,hK,Or.inr h8⟩

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
