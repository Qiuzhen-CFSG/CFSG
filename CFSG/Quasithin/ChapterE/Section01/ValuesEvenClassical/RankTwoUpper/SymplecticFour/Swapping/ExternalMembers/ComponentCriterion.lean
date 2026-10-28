module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Nonbinary
public import Theory.GroupTheory.SolvableResidual.PerfectQuotient
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.Nonbinary

/-!
# Suzuki core quotients and bounded-rank E-members

A finite local group with simple perfect two-core quotient has radical equal
to its two-core. Its solvable residual surjects onto the quotient, so the
remaining quotient is a two-group and the two-residual equals the solvable
residual. The quotient itself is the single component in the literal local
tau orbit. An actual Suzuki quotient bounds the image of an elementary
actor by the field exponent. The local group need not be perfect.

The final constructor verifies every E0/E2 and quotient-rank clause; Sylow
intersection, ambient tau containment and nontrivial quotient action remain
explicit inputs. ExternalMembers applies it to the original actor's chosen
involution centralizer. This does not construct that centralizer's model.

Source: Aschbacher--Smith, E.1.1--2, E.1.5 and E.1.14(1), printed
pp.209--210,214; the Suzuki rank calculation is Huppert--Blackburn III, XI.3.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers

private theorem radical_eq_core {K : Type*} [Group K] [Finite K]
    [IsSimpleGroup (K ⧸ pCore 2 K)] [Group.IsPerfect (K ⧸ pCore 2 K)] :
    solvableRadical K = pCore 2 K := by
  let D := solvableResidual K
  let : IsSimpleGroup (D ⧸ pCore 2 D) :=
    (solvableResidualPCoreQuotientEquiv 2 (G := K)).isSimpleGroup
  exact PerfectCoreTwoExtension.extension_radical_eq_core D
    (quotient_solvableResidual_isPGroup_of_perfect_pCore_quotient 2)

/-- The local group need not be perfect: its simple perfect core quotient
forces equality of the two-residual and solvable residual. -/
theorem componentCase_of_simple_core_quotient
    {G : Type*} [Group G] [Finite G] (T A K : Subgroup G)
    [IsSimpleGroup (K ⧸ pCore 2 K)] [Group.IsPerfect (K ⧸ pCore 2 K)]
    (hA : ¬ A.subgroupOf K ≤ pCore 2 K) : ECaseComponent T A K := by
  have hrad := radical_eq_core (K := K)
  let er := QuotientGroup.quotientMulEquivOfEq hrad
  let : IsSimpleGroup (K ⧸ solvableRadical K) := er.isSimpleGroup
  let : Group.IsPerfect (K ⧸ solvableRadical K) :=
    Group.IsPerfect.ofSurjective (f := er.symm.toMonoidHom) er.symm.surjective
  let Q := K ⧸ solvableRadical K
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · let := center_eq_top_iff.mp h
      exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hcomp : IsComponent Q ⊤ :=
    ⟨(inferInstance : (⊤ : Subgroup Q).Normal).isSubnormal, inferInstance⟩
  have hlayer : componentLayer Q = ⊤ := top_unique (le_sSup hcomp)
  have hr : pResidual 2 K = solvableResidual K :=
    (PerfectCoreTwoExtension.residuals (solvableResidual K)
      (quotient_solvableResidual_isPGroup_of_perfect_pCore_quotient 2)).1
  have ha : (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K)) ≠ ⊥ := by
    intro h
    apply hA
    have hh := (Subgroup.map_eq_bot_iff _).mp h
    simpa only [QuotientGroup.ker_mk', hrad] using hh
  let : IsSimpleGroup (⊤ : Subgroup Q) := topEquiv.isSimpleGroup
  have hcomm : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q),
      (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))⁆ :=
    SimpleSocle.commutator_eq ⊤ (by simpa only [coe_top, centralizer_univ] using hz) _ ha
  refine ⟨?_, ?_, hr, ⊤, hcomp, ?_, Or.inl hcomm⟩
  · rw [hrad]
    let S : Sylow 2 (pCore 2 K) := (pCore_isPGroup.to_subgroup ⊤).toSylow (by simp)
    exact ⟨S, inferInstanceAs (⊤ : Subgroup (pCore 2 K)).Normal⟩
  · change HasTwoGroupQuotient (componentLayer Q)
    rw [hlayer]
    let := QuotientGroup.subsingleton_quotient_top (G := Q)
    exact ⟨inferInstance, IsPGroup.of_subsingleton 2 _⟩
  · change componentLayer Q = conjugateJoin _ ⊤
    rw [RankOneUpper.conjugateJoin_eq_of_normal, hlayer]

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual

/-- A Suzuki quotient bounds the literal radical-quotient image of every
elementary actor, even when the local group itself is not perfect. -/
theorem suzuki_quotient_rank {G : Type*} [Group G] [Finite G]
    (m : ℕ) (hm : 0 < m) (A K : Subgroup G) [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (e : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) ≤
      2 * m + 1 := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (SuzukiMatrixGroup m) := ⟨suzuki_commutator_eq_top m hm⟩
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let : Group.IsPerfect (K ⧸ pCore 2 K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let r := (QuotientGroup.quotientMulEquivOfEq (radical_eq_core (K := K))).trans e
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (a.map r.toMonoidHom) := IsElementaryAbelian.map _
  calc
    Group.rank a = Group.rank (a.map r.toMonoidHom) :=
      Group.rank_congr (a.equivMapOfInjective r.toMonoidHom r.injective)
    _ ≤ primeRank 2 (SuzukiMatrixGroup m) :=
      (a.map r.toMonoidHom).rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 _)
    _ = 2 * m + 1 := suzuki_two_rank m hm

/-- E0, the actual Suzuki core quotient and nontrivial action on that quotient
give all the bounded-rank E-member clauses. -/
theorem isEMemberAt_of_suzuki_core_quotient
    {G : Type*} [Group G] [Finite G] (m : ℕ) (hm : 0 < m)
    (T : Sylow 2 G) (A K : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hAK : A ≤ K)
    (htau : tau (T : Subgroup G) A ≤ K)
    (hSyl : ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (e : (K ⧸ pCore 2 K) ≃* SuzukiMatrixGroup m)
    (hA : ¬ A.subgroupOf K ≤ pCore 2 K) :
    IsEMemberAt (2 * m + 1) (T : Subgroup G) A K := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : Group.IsPerfect (SuzukiMatrixGroup m) := ⟨suzuki_commutator_eq_top m hm⟩
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  let : Group.IsPerfect (K ⧸ pCore 2 K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hc := componentCase_of_simple_core_quotient (T : Subgroup G) A K hA
  exact ⟨⟨inferInstance, hAT, hAK, le_inf (tau_le _ _) htau, hSyl, Or.inr hc⟩,
    Or.inr ⟨hc, suzuki_quotient_rank m hm A K hAK e⟩⟩

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
