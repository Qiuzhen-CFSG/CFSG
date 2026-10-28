module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.Transport
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The genuine triality fixed-component reduction

The cubic short-root subgroup excludes order 360 when the exponent is at
least two. At exponent one the actual arm Levi has order 504, which cannot
divide 360. Thus simplicity of a smaller field model excludes an A₆ component
of that model, without requiring the order of the whole triality carrier.
The other branch uses the three-rank bound on the derived fixed group.

The three explicit inputs below are still model obligations: the inner
centralizer rank, actual outer fixed-group descent, and simplicity of the
smaller carriers. Inherited simplicity of the original carrier is not used
as a substitute for the last input. All carriers use the pinned D4 graph-field
construction, including exponent one.

Source: Aschbacher–Smith E.6.23, printed p.254, and 16.1.4(1,4), p.1171,
`refs/quasithin.pdf`. The order obstruction specializes the genuine Levi/root
method in `SevenLifting/Inspection/BinaryLie/Triality/CarrierObstruction.lean`.
-/

public section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Triality

/-- No genuine binary triality carrier has order 360, including exponent one. -/
theorem card_ne_six (n : ℕ) (hn : 0 < n) :
    Nat.card (BinaryCarrier n hn) ≠ 360 := by
  intro hc
  by_cases h : n = 1
  · subst n
    let P := binaryParameters 1 hn
    let U := levi P .arms
    have hU : Nat.card U = 504 := by
      rw [Nat.card_congr (leviArmsEquivPSL2 P rfl).toEquiv]
      have he := Atlas.ExceptionalSupport.card_psl_mul (F := ExtensionField P) 2
      have hF : Nat.card (ExtensionField P) = 8 := card_extensionField P
      norm_num [hF, Fin.prod_univ_succ] at he
      omega
    have hd := U.card_subgroup_dvd_card
    change Nat.card U ∣ Nat.card (BinaryCarrier 1 hn) at hd
    norm_num [hU, hc] at hd
  · have hd : 2 ^ (3 * n) ∣ Nat.card (BinaryCarrier n hn) := by
      rw [← EvenInvolutionGeometry.shortRootSubgroup_card n hn]
      exact (EvenInvolutionGeometry.shortRootSubgroup n hn).card_subgroup_dvd_card
    have h64 : 64 ∣ 360 := (pow_dvd_pow 2 (by omega : 6 ≤ 3 * n)).trans (hc ▸ hd)
    norm_num at h64

/-- The local rank conclusion consumed from the inner root-parabolic geometry. -/
@[expose] def InnerFixedRank : Prop :=
  ∀ (n : ℕ) (hn : 0 < n),
    IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
    ∀ a : MulAut (BinaryCarrier n hn), orderOf a = 2 →
      a ∈ MulAut.innerSubgroup (BinaryCarrier n hn) →
      primeRank 3 (commutator a.fixedSubgroup) ≤ 1

/-- Descent must identify the literal fixed subgroup with the smaller genuine
carrier. The normalization and coefficient-coverage premises remain to be proved. -/
@[expose] def OuterFixedModels : Prop :=
  ∀ (n : ℕ) (hn : 0 < n),
    IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
    ∀ a : MulAut (BinaryCarrier n hn), orderOf a = 2 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier n hn) →
      ∃ (m : ℕ) (hm : 0 < m), n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm)

/-- Conditional triality assembly; every remaining input is a concrete model
fact, and no order or simplicity hypothesis is silently inherited by a fixed group. -/
theorem excludesFixedSix_of_involution_data
    (hinner : InnerFixedRank) (houter : OuterFixedModels)
    (hsmall : ∀ (m : ℕ) (hm : 0 < m), IsSimpleGroup (BinaryCarrier m hm))
    (n : ℕ) (hn : 0 < n) [IsSimpleGroup (BinaryCarrier n hn)]
    [Group.IsPerfect (BinaryCarrier n hn)] : ExcludesFixedSix (BinaryCarrier n hn) := by
  intro a ha S hS
  by_cases hi : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn)
  · exact alternatingGroup.SixSubgroupObstructions.not_six_of_derived_fixed_rank a
      (hinner n hn inferInstance inferInstance a ha hi) S hS
  · obtain ⟨m, hm, _, ⟨e⟩⟩ := houter n hn inferInstance inferInstance a ha hi
    let : IsSimpleGroup (BinaryCarrier m hm) := hsmall m hm
    exact not_six_of_simple_fixed_model (card_ne_six m hm) a e S hS

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.Triality
