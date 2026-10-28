module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.CoverModels
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.PrimeCore.OffendingPrime
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterExponent

/-!
# The offending prime in the semisimple component-product case

The actual covering list gives component centers of order one or three.
The commuting product calculation proves that the whole center has exponent
three. The original covering kernel lies in that center, and the offending
prime divides its order. Thus the offending prime is three without using
the still separate prime-core reduction A.2.11.

Source: Aschbacher–Smith A.2.12(I), printed p.36.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.center_isThreeGroup_of_semisimple_not_quasisimple
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u}) :
    IsPGroup 3 (center G) := by
  intro z
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change (z : G) ^ 3 = 1
  apply center_pow_eq_one_of_component_centers hsemi 3 ?_ z z.property
  intro C hC x hx
  have hc : Nat.card (center C) ∣ 3 := by
    rcases h.component_center_card_and_coverModel ih hsemi hn hcovers hC with he | he
    · rw [he]
      exact one_dvd 3
    · rw [he.1]
  exact orderOf_dvd_iff_pow_eq_one.mp ((center C).orderOf_dvd_natCard hx |>.trans hc)

theorem CounterexampleToTheoremA.prime_dvd_center_of_semisimple
    {K : GroupClass.{u}} (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) (hsemi : IsSemisimple G) :
    p ∣ Nat.card (center G) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  apply (h.prime_dvd_cover_kernel ih f hf).trans
  apply card_dvd_of_le
  rw [← fittingSubgroup_eq_center_of_componentLayer_eq_top hsemi,
    ← h.center_preimage_eq_fitting ih f hf]
  intro x hx
  change f x ∈ center S
  rw [show f x = 1 from hx]
  exact one_mem _

theorem CounterexampleToTheoremA.prime_eq_three_of_semisimple_not_quasisimple
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) (hn : ¬ IsQuasisimple G)
    (hcovers : SQTKStructure.OrdinarySource.RemainingOddCoverInputs.{u}) : p = 3 := by
  obtain ⟨n, hn⟩ :=
    (h.center_isThreeGroup_of_semisimple_not_quasisimple ih hsemi hn hcovers).exists_card_eq
  have hd := h.prime_dvd_center_of_semisimple ih.theoremA hsemi
  rw [hn] at hd
  exact (Nat.dvd_prime Nat.prime_three).mp (h.2.2.2.2.1.dvd_of_dvd_pow hd)
    |>.resolve_left h.2.2.2.2.1.ne_one

end CFSG.Quasithin.ChapterA.Section02
