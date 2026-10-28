module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Alternating
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.DegreeThree
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Symplectic
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.G2
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Triality
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Ree
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Five
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.HigmanSims
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.JankoFour
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Rudvalis
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.JankoTwo
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.MathieuTwentyFour
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.MathieuTwentyTwo
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Source

/-!
# Literal Theorem C dispatch for the seven-component argument

Every constructor of the actual Theorem C catalogue is retained. The proved
alternating, odd-field, binary rank-one, classical rank-two, Ree, small
endpoint, linear-five and available sporadic leaves are instantiated here.
Held is returned with its actual model equivalence for the separate ambient
argument, since unrestricted Held inspection is false.

The remaining structure contains only concrete fixed-group/descent facts.
No field assumes an inspection or a seven-component exclusion. These facts
are still explicit and must be constructed before source E.6.18 is complete.

Source: Aschbacher–Smith, Theorem C and E.6.18, printed pp.33,252.
-/

public section
open Subgroup Theory.GroupTheory
open Triality.Standard
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
open Chapter1.Section02.LocalModels

/-- The precise outstanding concrete model facts. These are not inspections
or component-exclusion callbacks; each is shared with other model consumers. -/
structure SevenInspectionModelFacts : Prop where
  g2 : BinaryLie.G2.OuterInvolutionDescent
  trialityModels : ∀ (n : ℕ) (hn : 0 < n),
    IsSimpleGroup (BinaryCarrier n hn) ∧ Group.IsPerfect (BinaryCarrier n hn)
  trialityInner : ∀ (n : ℕ) (hn : 0 < n),
    IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
    ∀ a : MulAut (BinaryCarrier n hn), orderOf a = 2 →
      a ∈ MulAut.innerSubgroup (BinaryCarrier n hn) →
      primeRank 3 (commutator a.fixedSubgroup) ≤ 1
  trialityOuter : ∀ (n : ℕ) (hn : 0 < n),
    IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
    ∀ a : MulAut (BinaryCarrier n hn), orderOf a = 2 →
      a ∉ MulAut.innerSubgroup (BinaryCarrier n hn) →
      ∃ (m : ℕ) (hm : 0 < m), m < n ∧
        Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm)
  m24 : ¬ 9 ∣ Nat.card Sporadic.Mathieu.M24InvolutionCentralizers.centralizer2B
  ru : ¬ 9 ∣ Nat.card (Rudvalis.InvolutionCentralizers.Centralizer Rudvalis.a)

/-- All Theorem C constructors are retained. Every proved leaf is instantiated;
Held is returned with its genuine model equivalence for the ambient argument. -/
theorem inspection_or_held_of_model_facts
    (d : SevenInspectionModelFacts) {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) (hqt : IsStronglyQuasithin S)
    (hmodel : TheoremCModel S) :
    SevenActionInspection S ∨ Nonempty (S ≃* Held.He) := by
  cases hmodel with
  | alternating n hn iso => exact Or.inl (sevenActionInspection_of_isAlternating iso hn.2)
  | linear_odd p e hp ho he hsimple iso =>
      exact Or.inl (OddLie.sevenActionInspection_linear_two hp ho he hsimple iso)
  | three_odd p hp ho unitary iso =>
      exact Or.inl (OddLie.sevenActionInspection_three_odd hnc hp ho unitary iso)
  | rank_one iso => exact Or.inl (BinaryLie.bender_of_unitary
      (fun _ hn hm => BinaryLie.unitary_rank_one hn hm) iso)
  | rank_two iso =>
      apply Or.inl
      exact BinaryLie.rank_two_of_family_inspections
        (fun _ hn hm => BinaryLie.linear_rank_two hn hm)
        (fun _ hn hm => BinaryLie.symplectic hn hm)
        (fun _ hn hm => BinaryLie.g2_of_outerInvolutionDescent d.g2 hn hm)
        (fun _ hn hm => BinaryLie.triality_of_involution_data d.trialityModels
          d.trialityInner d.trialityOuter _ hn hm)
        (fun _ hn hm => BinaryLie.ree hnc hn hm) iso
  | binary_linear n hn iso =>
      exact Or.inl (BinaryLie.binary_linear_of_five BinaryLie.binary_five hn iso)
  | sporadic name hne iso =>
      obtain ⟨e⟩ := iso
      cases name with
      | m11 => exact Or.inl (SporadicInspection.of_equiv e SporadicInspection.m11)
      | m12 => exact Or.inl (SporadicInspection.of_equiv e SporadicInspection.m12)
      | m22 => exact Or.inl (SporadicInspection.of_equiv e SporadicInspection.mathieu_twenty_two)
      | m23 => exact Or.inl (SporadicInspection.of_equiv e SporadicInspection.m23)
      | m24 => exact Or.inl (SporadicInspection.of_equiv e (SporadicInspection.m24_of_second_centralizer d.m24))
      | j2 => exact Or.inl (SporadicInspection.of_equiv e SporadicInspection.janko_two)
      | j3 => exact (hne rfl).elim
      | j4 => exact Or.inl (SporadicInspection.janko_four hnc hqt e)
      | hs =>
          let : IsSimpleGroup Sporadic.LeechRelated.HS.Carrier :=
            (MulEquiv.isSimpleGroup_congr e).mp inferInstance
          let : Group.IsPerfect S := by
            constructor
            rcases (inferInstance : (commutator S).Normal).eq_bot_or_eq_top with hb | ht
            · exact (hnc ((commutator_eq_bot_iff S).mp hb)).elim
            · exact ht
          let : Group.IsPerfect Sporadic.LeechRelated.HS.Carrier :=
            Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
          exact Or.inl (SporadicInspection.of_equiv e (SporadicInspection.higman_sims
            Chapter16.OtherPreliminaries.JankoTwoHigmanSims.source_hs_involution_alternative))
      | he => exact Or.inr ⟨e⟩
      | ru => exact Or.inl (SporadicInspection.rudvalis_of_second_centralizer hnc e d.ru)
  | janko_one iso => exact Or.inl (sevenActionInspection_of_janko_one iso.some)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
