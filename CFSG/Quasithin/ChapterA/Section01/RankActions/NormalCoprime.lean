module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Coprime commutators in a normal solvable quasithin subgroup

Let C be normal, solvable and strongly quasithin. An actor A in C whose
order is prime to six moves every normalized two-subgroup into O₂(C).
Normality first puts [R,A] inside C; coprime commutator idempotence then
allows the literal A.1.26(2) source theorem to be applied inside C.

Source: Aschbacher–Smith, A.1.26(2), as used in 5.1.17, printed p.641
(refs/quasithin.pdf).
-/

public section
open scoped commutatorElement
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem odd_isPPerfect (A : Subgroup G) (ha : Nat.Coprime 2 (Nat.card A)) :
    IsPPerfect 2 A := by
  apply (pResidual_eq_top_iff 2 A).mp
  apply top_unique
  intro a _
  exact mem_pResidual_of_orderOf_coprime (ha.of_dvd_right (orderOf_dvd_natCard a))

theorem normal_solvable_coprime_commutator_le_core
    (C A R : Subgroup G) [C.Normal] [Group.IsSolvable C]
    (hsq : IsStronglyQuasithin C) (hAC : A ≤ C)
    (hA : Nat.Coprime (Nat.card A) 6)
    (hR : IsPGroup 2 R) (hAR : A ≤ normalizer (R : Set G)) :
    ⁅R,A⁆ ≤ C.pCoreIn 2 := by
  have hA2 : Nat.Coprime 2 (Nat.card A) :=
    (hA.of_dvd_right (by decide : 2 ∣ 6)).symm
  have hA3 : ¬ 3 ∣ Nat.card A :=
    Nat.prime_three.coprime_iff_not_dvd.mp (hA.of_dvd_right (by decide : 3 ∣ 6)).symm
  have hp := odd_isPPerfect A hA2
  have hRC : ⁅R,A⁆ ≤ C := (commutator_mono le_rfl hAC).trans (commutator_le_right R C)
  have hRR : ⁅R,A⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hAR
  have he : ⁅⁅R,A⁆,A⁆ = ⁅R,A⁆ := commutator_isPPerfect_idempotent A R hp hR hAR
  have hpi : IsPiPerfect twoThreePrimes A := by
    apply (piResidual_eq_top_iff _ _).mp
    rw [piResidual_twoThree_eq_pResidual_two hA3,(pResidual_eq_top_iff _ _).mpr hp]
  have hpiC : piResidual twoThreePrimes (A.subgroupOf C) = ⊤ :=
    (piResidual_eq_top_iff _ _).mpr
      (hpi.of_surjective (subgroupOfEquivOfLe hAC).symm.toMonoidHom
        (subgroupOfEquivOfLe hAC).symm.surjective)
  have hcomm : ⁅R,A⁆.subgroupOf C = ⁅⁅R,A⁆.subgroupOf C,A.subgroupOf C⁆ := by
    apply map_injective C.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hRC,map_subgroupOf_eq_of_le hAC,he]
  have hbound := lemma_A_1_26_2_of_stronglyQuasithin hsq (A.subgroupOf C)
    (⁅R,A⁆.subgroupOf C) hpiC (hR.to_le hRR).comap_subtype hcomm
  have hm := map_mono (f := C.subtype) hbound
  rwa [map_subgroupOf_eq_of_le hRC] at hm
end CFSG.Quasithin.ChapterA
