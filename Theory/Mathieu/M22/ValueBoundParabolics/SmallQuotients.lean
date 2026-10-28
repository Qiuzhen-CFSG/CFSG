module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.PrimeRankNonabelianCube
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.SpecificGroups.SymmetricFourSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The symmetric quotients in the M₂₂ generating family

The intrinsic generalized Fitting subgroups of S₅ and S₃ are their actual
alternating subgroups. For S₅, A₅ is quasisimple, the quotient has order two,
and the two-core is trivial. For S₃, every prime core and every component
lies in A₃, while the normal nilpotent subgroup A₃ lies in the Fitting subgroup.

A Sylow two-subgroup of S₃ has order two. Embedding S₄ into S₅ by fixing
the fifth point supplies a dihedral Sylow subgroup of order eight, whose
abelian subgroups have rank at most two. These give precisely the local
generalized-Fitting conditions and rank bounds needed for the two quotients.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.3(2),
printed pp. 241–242 (PDF pp. 252–253).
-/

public section

namespace Sporadic.Mathieu.M22ValueBound.SmallQuotients
open Subgroup Theory.GroupTheory Equiv
open scoped IsMulCommutative

private theorem alternatingFive_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem symmetricFive_twoCore : pCore 2 (Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Perm (Fin 5))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hdiv : 60 ∣ Nat.card (pCore 2 (Perm (Fin 5))) := by
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Perm (Fin 5))).exists_card_eq
  have hthree : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 60) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

private theorem alternating_quotient_isTwoGroup (n : ℕ) [Nontrivial (Fin n)] :
    IsPGroup 2 (Perm (Fin n) ⧸ alternatingGroup (Fin n)) := by
  apply IsPGroup.of_card (n := 1)
  change (alternatingGroup (Fin n)).index = 2
  exact alternatingGroup.index_eq_two

/-- The intrinsic generalized Fitting subgroup of S₅ is its alternating subgroup. -/
theorem symmetricFive_generalizedFitting_eq_alternating :
    generalizedFitting (Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  let := alternatingFive_quasisimple
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (alternating_quotient_isTwoGroup 5) symmetricFive_twoCore

/-- The first local quotient has quasisimple generalized Fitting subgroup. -/
theorem symmetricFive_generalizedFitting_isQuasisimple :
    IsQuasisimple (generalizedFitting (Perm (Fin 5))) := by
  rw [symmetricFive_generalizedFitting_eq_alternating]
  exact alternatingFive_quasisimple

private theorem symmetricThree_twoCore : pCore 2 (Perm (Fin 3)) = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Perm (Fin 3)))
    Function.surjective_id (by simp only [MonoidHom.ker_id]; exact IsPGroup.of_subsingleton 2 _)
  simpa only [MonoidHom.ker_id] using h.symm

/-- The intrinsic generalized Fitting subgroup of S₃ is its alternating subgroup. -/
theorem symmetricThree_generalizedFitting_eq_alternating :
    generalizedFitting (Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply sup_le
    · rw [fitting_eq_sup_pCore]
      apply iSup_le
      intro p
      by_cases hp : p.val.val = 2
      · rw [hp, symmetricThree_twoCore]
        exact bot_le
      · let : Fact (Nat.Prime p.val.val) := ⟨(Nat.mem_primeFactors.mp p.val.property).1⟩
        let f := QuotientGroup.mk' (alternatingGroup (Fin 3))
        have hi : IsPGroup 2 ((pCore p.val.val (Perm (Fin 3))).map f) :=
          (alternating_quotient_isTwoGroup 3).to_subgroup _
        have hdis := IsPGroup.disjoint_of_ne p.val.val 2 hp
          ((pCore p.val.val (Perm (Fin 3))).map f) _ (pCore_isPGroup.map f) hi
        have hz : (pCore p.val.val (Perm (Fin 3))).map f = ⊥ := by simpa using hdis.eq_bot
        simpa only [Subgroup.map_eq_bot_iff, f, QuotientGroup.ker_mk'] using hz
    · apply sSup_le
      intro M hM
      let : IsQuasisimple M := hM.2
      exact le_of_isPerfect_of_index_eq_two M _ alternatingGroup.index_eq_two
  · apply le_trans _ (fitting_le_generalizedFitting _)
    have hp : IsPGroup 3 (alternatingGroup (Fin 3)) :=
      IsPGroup.of_card (n := 1) (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide)
    let : Group.IsNilpotent (alternatingGroup (Fin 3)) := hp.isNilpotent
    exact le_sSup ⟨inferInstance, inferInstance⟩

/-- The second local quotient has generalized Fitting subgroup of prime order. -/
theorem symmetricThree_generalizedFitting_card_prime :
    (Nat.card (generalizedFitting (Perm (Fin 3)))).Prime := by
  rw [symmetricThree_generalizedFitting_eq_alternating, nat_card_alternatingGroup,
    Nat.card_fin]
  decide

/-- The two-rank of the second local quotient is at most one. -/
theorem symmetricThree_primeRank_le_one : primeRank 2 (Perm (Fin 3)) ≤ 1 := by
  let P : Sylow 2 (Perm (Fin 3)) := Classical.choice inferInstance
  apply P.primeRank_le_one_of_isCyclic
  apply isCyclic_of_prime_card (p := 2)
  rw [P.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
  decide +kernel

/-- The two-rank of the first local quotient is at most two. -/
theorem symmetricFive_primeRank_le_two : primeRank 2 (Perm (Fin 5)) ≤ 2 := by
  let P : Sylow 2 (Perm (Fin 4)) := Classical.choice inferInstance
  let f : Perm (Fin 4) →* Perm (Fin 5) :=
    Perm.viaEmbeddingHom ⟨Fin.castSucc, Fin.castSucc_injective 4⟩
  have hf : Function.Injective f := Perm.viaEmbeddingHom_injective _
  let e : P ≃* (P : Subgroup (Perm (Fin 4))).map f :=
    Subgroup.equivMapOfInjective _ _ hf
  have hc : Nat.card ((P : Subgroup (Perm (Fin 4))).map f) = 8 := by
    rw [← Nat.card_congr e.toEquiv, P.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
    decide +kernel
  let Q : Sylow 2 (Perm (Fin 5)) := Sylow.ofCard ((P : Subgroup (Perm (Fin 4))).map f) (by
    rw [hc, Nat.card_perm, Nat.card_fin]
    decide +kernel)
  obtain ⟨d⟩ := Perm.sylow_two_equiv_dihedral_four P
  apply primeRank_le_two_of_nonabelian_sylow_cube Q hc
  intro hcomm
  let : IsMulCommutative ((P : Subgroup (Perm (Fin 4))).map f) := hcomm
  have hd : IsMulCommutative (DihedralGroup 4) :=
    IsMulCommutative.of_comm fun x y => by
      apply (e.symm.trans d).symm.injective
      simp only [map_mul]
      exact mul_comm ((e.symm.trans d).symm x) ((e.symm.trans d).symm y)
  exact DihedralGroup.not_commutative (by decide) (by decide) hd

end Sporadic.Mathieu.M22ValueBound.SmallQuotients
