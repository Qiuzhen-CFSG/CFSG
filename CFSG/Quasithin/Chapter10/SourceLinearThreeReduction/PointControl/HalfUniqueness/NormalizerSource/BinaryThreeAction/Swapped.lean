module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.Linear
/-!
# The full swapped input for a strict normalizer enlargement

Recover component detection before discarding its orbit, complement and
commutator data. An invariant component is excluded by the already proved
Held and binary-linear normalizer calculations. Hence every remaining
strict enlargement supplies a genuine swapped Sylow input, with the same
original residual and its literal normal closure. This stronger interface
retains the two conjugate factors required by both rank-one calculations.

Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748, with the corrected
Held alternative retained and discharged.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H : Subgroup G}

/-- Failure of normalization supplies all original swapped-component hypotheses. -/
theorem Data.exists_swapped_input (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hN : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G)) :
    ∃ P I : Subgroup G, SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) := by
  obtain ⟨P,hi⟩ := h.exists_localInput
  have hE := Chapter1.RadicalExclusions.sqtk_of_mem_H D.simpleQTKE (h.enlargement_mem_H hn)
  have hT := SourceLinearThreeReplacement.Overgroups.Closure.sylowIn_overgroup
    (h.sylow_le.trans (show H ≤ enlargement T L H from le_sup_right))
  let hA := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases hi.normal_or_detected_containment hA hC hE hT with
    hnorm | ⟨I,hI,hIn,hcomm,hP,hX⟩
  · exact (hN (le_sup_left.trans
      ((normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hi.overgroup)).mp hnorm))).elim
  have he : enlargedResidual T L H = componentOrbit I (T : Subgroup G) :=
    SourceLinearThreeReplacement.Overgroups.Closure.normalClosure_eq_of_commutator
      hi.complement_le hX
      ((componentOrbit_le_sup I (T : Subgroup G)).trans
        (sup_le hI.mem.1 (le_sup_right.trans hi.overgroup))) hIn hcomm
  by_cases hfixed : (T : Subgroup G) ≤ normalizer (I : Set G)
  · have horbit : componentOrbit I (T : Subgroup G) = I :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer I T I le_rfl hfixed)
        (le_componentOrbit I T)
    rw [horbit] at hIn hcomm hP hX
    have halt := InvariantThree.Source.alternatives_knownSimple hi hE hT hI.mem.1 hIn
      hI.quasisimple hP hcomm
    have hKI : enlargedResidual T L H = I := he.trans horbit
    have hqK : IsQuasisimple (XiQuotient (enlargedResidual T L H)) := hKI.symm ▸ hI.quasisimple
    rcases halt with halt | hheld
    · have hw : Nonempty (XiQuotient (residual H ⊔ (T : Subgroup G)) ≃*
          SourceLinearThreeReplacement.Overgroups.Closure.ParabolicWreath) := by
        rw [h.residual_sup_sylow]
        obtain ⟨e⟩ := h.quotient
        obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
        exact ⟨e.trans (RegularWreathProduct.congr eSL
          (MulEquiv.refl (Multiplicative (ZMod 2))))⟩
      obtain ⟨k,hk,hm,_⟩ :=
        SourceLinearThreeReplacement.Overgroups.Closure.invariantWreathSieve T
          (residual H) P (enlargement T L H) I hi hE hI.mem hI.quasisimple hIn
          hfixed hP hX hcomm hw halt
      exact (hN (h.normalizes_residual_of_binary_linear hn hqK hk (hKI.symm ▸ hm))).elim
    · exact (hN (h.normalizes_residual_of_held hn hqK (hKI.symm ▸ hheld.2.2.2))).elim
  · refine ⟨P,I,?_,he⟩
    exact { toLocalInput := hi
            sqtk := hE
            component := hI.mem
            quasisimple := hI.quasisimple
            orbit_normal := hIn
            complement_le_orbit := hP
            orbit_commutator := hcomm
            noncentral := hI.noncentral_component_core
            not_invariant := hfixed
            sylow_two := hT }
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
