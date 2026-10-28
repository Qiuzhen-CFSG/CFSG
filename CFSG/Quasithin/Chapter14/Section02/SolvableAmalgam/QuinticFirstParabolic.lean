module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolicData
public import Theory.SpecificGroups.Tits.FirstParabolicPresentation
public import Theory.SpecificGroups.ReeTwo.GeneratingRecognition
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.GeneratingRelations
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.IntrinsicCentralizer
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.IntrinsicRigidity
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.KernelOrder

/-!
# Reconstructing the original first parabolic from local relations

Generating roots satisfying the full Ree relations identify the whole first
parabolic and contradict the original centralizer exclusion. In the other
branch, Parrott's 28 local relations and generation give a surjection onto H.
The original index |H:T|=5 and the lower bound |T|≥2048 remove its kernel,
yielding an isomorphism from the actual Tits first parabolic. The existing
source rigidity theorem then supplies the literal second-vertex data.

The original Sylow lower bound is now proved and consumed below. The
intrinsic-centralizer route constructs the tuple and actor. Intrinsic core
rigidity now proves the full-centralizer equality from the core upper bound.
Only the unconditional bound |O₂(H)|≤512 remains with this task.
`KernelOrder` identifies it with |G_H^[2]|≤32. The final reduction below
constructs the whole first parabolic or retains |G_H^[2]|≥64 explicitly;
this does not complete 14.2.21. Earlier public APIs
with explicit lower bounds or centralizer equality are preserved.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21,
pp.988--989; Parrott (1972), §5, p.683. The concrete Tits quotient is Sz(2),
with two-core order512, as proved by the imported corrected model.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The literal index-five source converts the Sylow lower bound into the
cardinality premise for the relation-defined Tits map. -/
theorem index_five_first_of_generators
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlower : 2048 ≤ Nat.card (T : Subgroup G))
    (d : Tits.FirstParabolicPresentation.Generators H) :
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) := by
  have hcount := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at hcount
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hcount
  rw [hi] at hcount
  obtain ⟨eH, _⟩ := d.exists_equiv (by omega)
  exact ⟨eH⟩

/-- Under the original ambient hypotheses, a full-Ree generating root tuple
is impossible. Faithfulness comes from its surviving central root. -/
theorem source_full_ree_generators_excluded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (d : ReeTwo.Centralizer.Generators H) : False := by
  exact source_full_ree_parabolic_exclusion hG T hempty hM hu hmany hcard e H hH
    ⟨ReeTwo.ParabolicMarkedComparison.Verified.firstEquiv.symm.trans d.equiv⟩

/-- Conditional final assembly from the two independent source obligations:
the actual generating relations and the common-Sylow lower bound. -/
theorem source_tits_first_of_presentations
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlower : 2048 ≤ Nat.card (T : Subgroup G))
    (hrelations : Nonempty (ReeTwo.Centralizer.Generators H) ∨
      Nonempty (Tits.FirstParabolicPresentation.Generators H)) :
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) := by
  rcases hrelations with hree | htits
  · obtain ⟨d⟩ := hree
    exact (source_full_ree_generators_excluded hG T hempty hM hu hmany hcard e H hH d).elim
  · obtain ⟨d⟩ := htits
    exact index_five_first_of_generators T H hH.1.1.2 hi hlower d

/-- The reconstructed whole first endpoint feeds the existing literal source
consumer, without adding a second-endpoint or overlap-compatibility premise. -/
theorem source_quintic_data_of_presentations
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlower : 2048 ≤ Nat.card (T : Subgroup G))
    (hrelations : Nonempty (ReeTwo.Centralizer.Generators H) ∨
      Nonempty (Tits.FirstParabolicPresentation.Generators H)) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) := by
  have hfirst := source_tits_first_of_presentations hG T hempty hM hu hmany
    hcard e H hH hi hlower hrelations
  exact ⟨hfirst, source_tits_first_second_data hG T hempty hM hu hmany hcard e H hH hi hfirst⟩

/-- Whole-first-parabolic recognition with the numerical premise discharged
by the original source theorem. Only the actual generating relations remain. -/
theorem source_tits_first_of_generating_relations
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hrelations : Nonempty (ReeTwo.Centralizer.Generators H) ∨
      Nonempty (Tits.FirstParabolicPresentation.Generators H)) :
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) :=
  source_tits_first_of_presentations hG T hempty hM hu hmany hcard e H hH hi
    (source_quintic_sylow_lower hG T hempty hM hu hmany hcard e H hH hi) hrelations

/-- Intrinsic centralizer structure constructs the generators and identifies
the whole first parabolic. The Sylow bound is proved from the original source. -/
theorem source_tits_first_of_intrinsic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hintrinsic : ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z) :
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) :=
  source_tits_first_of_generating_relations hG T hempty hM hu hmany hcard e H hH hi
    (QuinticFirstParabolic.source_generating_relations_of_intrinsic
      hG T hempty hM hu hmany hcard e H hH hi hintrinsic)

/-- The intrinsic construction feeds the literal source rigidity and cubic
partner data. Final discharge of the intrinsic premise remains in this task. -/
theorem source_quintic_data_of_intrinsic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hintrinsic : ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) := by
  have hfirst := source_tits_first_of_intrinsic hG T hempty hM hu hmany hcard e H hH hi hintrinsic
  exact ⟨hfirst, source_tits_first_second_data hG T hempty hM hu hmany hcard e H hH hi hfirst⟩

/-- The complete local reconstruction from centralizer equality and the
original core upper bound. Class three, five-fixed points, quotient model,
Sylow generators, Weyl actor, generation and whole-group injectivity are all
proved in this chain. This earlier interface retains centralizer equality
explicitly; `source_quintic_data_of_core_upper_bound` below derives it. -/
theorem source_quintic_data_of_core_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hHMc : H = Mc) (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) :=
  source_quintic_data_of_intrinsic hG T hempty hM hu hmany hcard e H hH hi
    (QuinticFirstParabolic.source_intrinsic_of_core_bound
      hG T hempty hM hu hmany hcard e H hH hi hHMc hQupper)

/-- The core upper bound suffices for a genuine isomorphism of the whole first parabolic. -/
theorem source_tits_first_of_core_upper_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) :=
  source_tits_first_of_intrinsic hG T hempty hM hu hmany hcard e H hH hi
    (QuinticFirstParabolic.source_intrinsic_of_core_upper_bound
      hG T hempty hM hu hmany hcard e H hH hi hQupper)

/-- Whole-first-parabolic recognition and the literal source data from only
an upper bound on the original two-core. Intrinsic rigidity proves H=Mc;
the numerical lower bound, all generators and all relations are discharged.
The unconditional source upper bound remains the task's sole extra premise. -/
theorem source_quintic_data_of_core_upper_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) :=
  source_quintic_data_of_intrinsic hG T hempty hM hu hmany hcard e H hH hi
    (QuinticFirstParabolic.source_intrinsic_of_core_upper_bound
      hG T hempty hM hu hmany hcard e H hH hi hQupper)

/-- The literal radius-two kernel bound supplies the intrinsic core bound
and hence the entire first-parabolic reconstruction. The kernel bound
remains to be discharged from the original geometry in this task. -/
theorem source_quintic_data_of_second_kernel_upper
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hKupper :
      let X := sourceResidual M Mc ⊔ (T : Subgroup G)
      Nat.card (ChapterF.Section07.Geometry.ballKernel X H
        (ChapterF.Section07.Geometry.base X H true) 2) ≤ 32) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3)) :=
  source_quintic_data_of_core_upper_bound hG T hempty hM hu hmany hcard e H hH hi
    ((QuinticFirstParabolic.source_core_upper_iff_second_kernel_upper
      hG T hempty hM hu hmany hcard e H hH hi).mpr hKupper)

/-- Unconditional reduction of the original quintic branch. The small
second kernel gives the whole Tits first parabolic and all original source
data. The remaining alternative has core order at least 1024 and literal
radius-two kernel order at least 64; this theorem does not exclude it. -/
theorem source_quintic_data_or_large_second_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    (Nonempty (Tits.ExceptionalParabolics.first ≃* H) ∧
      H = Mc ∧ M = X ∧ H = centralizer (centralInvolutions T : Set G) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card X = 6144 ∧
      Nat.card (pCore 2 X) = 1024 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Equiv.Perm (Fin 3))) ∨
      (1024 ≤ Nat.card (pCore 2 H) ∧
        64 ≤ Nat.card (ChapterF.Section07.Geometry.ballKernel X H
          (ChapterF.Section07.Geometry.base X H true) 2)) := by
  rcases QuinticFirstParabolic.source_second_kernel_order_gap
      hG T hempty hM hu hmany hcard e H hH hi with hsmall | hlarge
  · exact Or.inl (source_quintic_data_of_core_upper_bound
      hG T hempty hM hu hmany hcard e H hH hi hsmall.1.le)
  · exact Or.inr hlarge

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
