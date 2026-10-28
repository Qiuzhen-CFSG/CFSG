module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.Reduction
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.GroupTheory.SylowFiveKernelConjugacy

/-!
# Eliminating the Suzuki-two action in the escaping intersection

Original 15.2.14(2b) leaves the actual Sz(2) image or the genuine natural
Omega action. In a group of order twenty, the unique Sylow-five subgroup
is cyclic and has two-group quotient. Its two-residual is therefore cyclic.
The original residual-normalizer obstruction excludes that row.

The explicit action alternatives are earlier source inputs, produced by
qt-e-152-plane-geometry and qt-e-152-small-parabolic. No index or S₃
quotient is assumed. Source: Aschbacher--Smith 15.2.14(2b), 15.2.17(1),
and 15.2.18(3), printed pp.1112--1113.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor

private theorem cyclic_twoResidual_of_card_twenty {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D = 20) : IsCyclic (pResidual 2 D) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 D := Classical.choice inferInstance
  let : Subsingleton (Sylow 5 D) := Sylow.subsingleton_five_of_card_twenty hc
  let : (P : Subgroup D).Normal := P.normal_of_subsingleton
  have hP : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity,hc]
    decide +kernel
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hquot : IsPGroup 2 (D ⧸ (P : Subgroup D)) := by
    apply IsPGroup.of_card (n := 2)
    have hm := (P : Subgroup D).card_mul_index
    rw [hP,hc,index_eq_card] at hm
    norm_num at hm ⊢
    omega
  have hle : pResidual 2 D ≤ P := sInf_le ⟨inferInstance,hquot⟩
  exact isCyclic_of_injective (inclusion hle) (inclusion_injective hle)

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The literal earlier 15.2.14(2b) alternatives force genuine Omega when NI
escapes MI. The Sz(2) isomorphism is with the concrete Suzuki matrix group. -/
theorem omega_of_restricted_actions (hI : PlaneEscapes Mc ZS I)
    (ha : letI := hsource.prepared.elementary;
      Nonempty (internalActionImage M V hsource.prepared.normalized ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized))
    (hout : ¬ M ⊓ I ≤ Mc ⊓ I) :
    letI := hsource.prepared.elementary;
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) := by
  let := hsource.prepared.elementary
  apply omega_of_not_le_partner d hI _ hout
  rcases ha with he | ho
  · obtain ⟨e⟩ := he
    exact Or.inl (cyclic_twoResidual_of_card_twenty
      ((Nat.card_congr e.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card))
  · exact Or.inr ho

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.OmegaAction
