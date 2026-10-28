module

public import Stellmacher.Recognition.GTwoWreathed
public import ABG.ChapterII.Section3.CharacteristicPower
public import ABG.ChapterII.Section3.SolvableCharacteristicPower
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Full involution-centralizer data in the order-32 G₂ branch

For a finite simple N₂ group of the original G₂ local type, a supplied
Sylow 2-subgroup of order 32 gives the following data for the full
centralizer of every involution: it is a Q-group, its source characteristic
power is three, and it has an actual wreathed Sylow subgroup of height two.
The retained terminal hypothesis that all two-local odd cores are trivial
also makes this full centralizer's odd core trivial.

The original local data supply the wreathed Sylow presentation. Simplicity
excludes normal index two, so the complete QD fusion theorem applies.
Conjugate the central involution of the supplied Sylow subgroup to the
given involution and restrict that same conjugate Sylow to its centralizer;
this preserves the precise height. The involution centralizer is two-local,
so N₂ gives solvability and the retained odd-core hypothesis applies.
The proved Q-group source-power existence theorem and solvability then
force its actual characteristic field order to be three.

Sources: Stellmacher (8.6)(a1,a2), journal p. 41, and the terminal two-local
odd-core reduction; ABG II.1 fusion, II.2 Proposition 1 and II.3 Definition 1,
article pp. 15 and 23. No local vertex is assumed equal to this centralizer.
The order-64 alternative and actual unitary/global model recognition remain
separate implications.
-/

namespace Stellmacher.Recognition
open ABG

/-- Full centralizer data from the original G₂ type and retained terminal hypotheses. -/
public theorem involutionCentralizer_data_of_gTwo_card32
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hType : IsOfGTwoTwoDerivedType G)
    (hcard : Nat.card S = 32) (hN : IsNTwoGroup G)
    (hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥)
    (x : G) (hx : orderOf x = 2) :
    IsQGroup (Subgroup.centralizer ({x} : Set G)) ∧
      pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ ∧
      HasSourceQCharacteristicPower (Subgroup.centralizer ({x} : Set G)) 3 ∧
      ∃ T : Sylow 2 (Subgroup.centralizer ({x} : Set G)), IsWreathedOfHeight T 2 := by
  classical
  have hS := wreathed_of_gTwoTwoDerived_type_of_card32 S hType hcard
  have hno : HasNoNormalIndexTwoSubgroup G := by
    intro K hKn hKi
    rcases hKn.eq_bot_or_eq_top with rfl | rfl
    · rw [Subgroup.index_bot] at hKi
      have hdvd := (S : Subgroup G).card_subgroup_dvd_card
      rw [hcard, hKi] at hdvd
      norm_num at hdvd
    · simp at hKi
  have hQD : IsQDGroup G :=
    (isQDGroup_iff_no_normal_index_two S (Or.inr ⟨2, hS⟩)).mpr hno
  let C := Subgroup.centralizer ({x} : Set G)
  have hCtwo : IsTwoLocal C := Theory.GroupTheory.isTwoLocal_involution_centralizer hx
  have hQ : IsQGroup C := (qd_involutionCentralizer_isQGroup hQD x hx).1
  have hCcore : pPrimeCore 2 C = ⊥ := hcore C hCtwo
  let : Group.IsSolvable C := hN C hCtwo
  obtain ⟨q, hq, _⟩ := exists_sourceCharacteristicPower hQD
  have hqC : HasSourceQCharacteristicPower C q := hq.at_involution hQD x hx
  have hq3 : HasSourceQCharacteristicPower C 3 := hqC.eq_three_of_isSolvable ▸ hqC
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hcov⟩ := hclass
  obtain ⟨i, hzi⟩ := hcov P.x ((Subgroup.orderOf_coe P.x).trans P.x_orderOf)
  obtain ⟨j, hxj⟩ := hcov x hx
  have hzx : IsConj (P.x : G) x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hzx
  let e := S.equivSMul g
  have hT : IsWreathedOfHeight (g • S : Sylow 2 G) 2 := wreathed_equiv e hS
  have hzc : e P.x ∈ Subgroup.center (g • S : Sylow 2 G) := by
    apply Subgroup.mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp P.x_mem_center s)
  have he : ((e P.x : (g • S : Sylow 2 G)) : G) = x := hg
  have hTC : ((g • S : Sylow 2 G) : Subgroup G) ≤ C := by
    intro t ht
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hzc (⟨t, ht⟩ : (g • S : Sylow 2 G)))
    change t * (e P.x).val = (e P.x).val * t at hh
    simpa only [he] using hh
  let T := (g • S : Sylow 2 G).subtype hTC
  let eT : T ≃* (g • S : Sylow 2 G) := Subgroup.subgroupOfEquivOfLe hTC
  exact ⟨hQ, hCcore, hq3, T, wreathed_equiv eT.symm hT⟩

end Stellmacher.Recognition
