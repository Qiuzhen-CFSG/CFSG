module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.GroupTheory.SolvableOuterQuotient
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Triality.CarrierObstruction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Triality.Descent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Triality.ParabolicRank

/-!
# The triality induction for the seven-component inspection

Choose an involution central in the actual two-subgroup of automorphisms.
For an inner involution, the derived centralizer rank bound excludes a
perfect seven subgroup. For an outer involution, a genuine isomorphism of
its fixed group to a smaller binary triality carrier permits induction.
Restriction of the whole actor preserves precisely the common fixed group
and its embedded ordinary component. A trivial restricted action is handled
by the carrier obstruction, including the field of order two.

The source theorem is not yet asserted. The conditional induction below
still requires simplicity/perfectness of the smaller carriers, the inner
fixed-group rank calculation, and actual outer fixed-group descent. The
latter must include automorphism coverage and normalization; the existing
conditional coefficient results alone do not discharge it.

Source: Aschbacher–Smith E.6.18, printed p.252, and Theorem C / Remark A.2.4,
printed p.33, `refs/quasithin.pdf`. All carriers are the pinned graph-field
construction from `Triality.StandardModel`, never the auxiliary matrix model.
-/

public section

open Subgroup Theory.GroupTheory
open Triality.Standard
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie

/-- Conditional strong induction on the binary exponent. Every remaining
premise describes a concrete model fact, independently of seven components. -/
theorem triality_of_involution_data
    (hmodels : ∀ (n : ℕ) (hn : 0 < n),
      IsSimpleGroup (BinaryCarrier n hn) ∧ Group.IsPerfect (BinaryCarrier n hn))
    (hinner : ∀ (n : ℕ) (hn : 0 < n),
      IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
      ∀ a : MulAut (BinaryCarrier n hn), orderOf a = 2 →
        a ∈ MulAut.innerSubgroup (BinaryCarrier n hn) →
        primeRank 3 (commutator a.fixedSubgroup) ≤ 1)
    (houter : ∀ (n : ℕ) (hn : 0 < n),
      IsSimpleGroup (BinaryCarrier n hn) → Group.IsPerfect (BinaryCarrier n hn) →
      ∀ a : MulAut (BinaryCarrier n hn), orderOf a = 2 →
        a ∉ MulAut.innerSubgroup (BinaryCarrier n hn) →
        ∃ (m : ℕ) (hm : 0 < m), m < n ∧
          Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm))
    {S : Type*} [Group S] (f : ℕ) (hf : 1 ≤ f)
    (hS : IsTrialityGroupAt (2 ^ f) S) : SevenActionInspection S := by
  have all (n : ℕ) : ∀ hn : 0 < n, SevenActionInspection (BinaryCarrier n hn) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let := (hmodels n hn).1
      let := (hmodels n hn).2
      intro P hp L hLF hL hs
      by_contra hP
      obtain ⟨r, hr, hc⟩ := TrialityCase.exists_central_involution P hp hP
      by_cases hi : (r : MulAut (BinaryCarrier n hn)) ∈ MulAut.innerSubgroup _
      · exact TrialityCase.no_seven_of_derived_fixed_rank P r
          (hinner n hn inferInstance inferInstance r hr hi) L hLF hL hs
      · obtain ⟨m, hm, hmn, ⟨e⟩⟩ := houter n hn inferInstance inferInstance r hr hi
        let := (hmodels m hm).1
        obtain ⟨Q, hQ, D, hDF, hD, hsD⟩ :=
          TrialityCase.descend_seven_component P hp r hc L hLF hL hs
        have hsmall := SporadicInspection.of_equiv e (ih m hmn hm)
        apply TrialityCase.no_seven_fixed_of_inspection hsmall ?_ Q hQ D hDF hD hsD
        intro J hJ hsJ
        exact TrialityCase.no_seven_components m hm (J.map e.toMonoidHom)
          (hJ.map_equiv e) (hsJ.of_equiv (e.subgroupMap J))
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff S f hf).mp hS
  exact SporadicInspection.of_equiv e (all f hf)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
