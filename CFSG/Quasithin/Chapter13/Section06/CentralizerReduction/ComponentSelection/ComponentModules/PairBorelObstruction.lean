module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.Centralizers
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation
public import Theory.SpecificGroups.SymmetricFive.OddSquareKernel

/-!
# The final paired Borel contradiction on the original A₅ module

A subgroup normalizing V acts on its genuine five-point coordinates. If
the centralizer of the B-conjugate span of the marked seed is a two-group,
then the kernel of this five-point action is a two-group as well: the span
lies in V. No nontrivial odd square can divide |B|, contradicting the paired
rank-one Borel torus. The Borel construction and its seed kernel are kept
as literal subgroup hypotheses for their source producers.

Source: Aschbacher--Smith, final paragraph of 13.6.14, pp.929--930.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The paired torus contradicts the actual normalizer action on V. -/
theorem pairBorel_card_contradiction_source
    (d : A5Module.FlagSource T L V V₁ V₂) (B : Subgroup G)
    (hBN : B ≤ normalizer (V : Set G))
    (hseed : IsPGroup 2 ((centralizer
      (conjugateSpanBy (zpowers (A5Module.markedZ d.flag.module)) B : Set G)).subgroupOf B))
    {m : ℕ} (ho : Odd m) (hm : m ≠ 1) (hcard : m ^ 2 ∣ Nat.card B) : False := by
  let f := d.normalizerAction.comp (inclusion hBN)
  have hzV : A5Module.markedZ d.flag.module ∈ V :=
    d.flag.module.range_eq.le ⟨_,rfl⟩
  have hspan : conjugateSpanBy (zpowers (A5Module.markedZ d.flag.module)) B ≤ V :=
    conjugateSpanBy_le (zpowers_le.mpr hzV) hBN
  have hk : f.ker ≤ (centralizer
      (conjugateSpanBy (zpowers (A5Module.markedZ d.flag.module)) B : Set G)).subgroupOf B := by
    intro b hb
    exact (centralizer_le hspan)
      ((Chapter13.Section05.A5Source.actor_eq_one_iff d (inclusion hBN b)).mp hb)
  exact SymmetricFive.odd_square_not_dvd_card_of_two_kernel f (hseed.to_le hk) ho hm hcard

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
