module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.ConjugatePair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Quotient
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.Quasithin.EvenCharacteristic

/-!
# Core generation from the parabolic action

If a conjugate of `O₂(I)` lies in `O₂(I)`, equality follows from finiteness.
Since `S` has index two in `T`, the whole of `T` then normalizes `O₂(I)`.
The unique maximal two-local overgroup of `Y₊T`, obtained from 15.3.2(4),
forces `L ≤ M`, contradicting the outside-component hypothesis.

Consequently the conjugate core has nonzero image in `I*`. Irreducibility
of the actual parabolic core image implies that this image is all of `P*`.
Lifting through the action kernel gives `P = O₂(I) O₂(I)ᵗ`. The two cores
are the two action centralizers, so the quotient product theorem applies.

The kernel identification and irreducible parabolic action remain explicit
premises. They must be proved by the degree-eight geometry before this
conditional reduction establishes source 15.3.32(6).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(6), printed p.1133.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
variable {G : Type*} [Group G] [Finite G]
/-- The equal-core branch contradicts the unique maximal two-local containing `Y₊T`. -/
theorem core_conjugate_not_le (d : LocalData G) {I : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    ¬ (I.pCoreIn 2).conjBy t ≤ I.pCoreIn 2 := by
  intro hle
  have heq : (I.pCoreIn 2).conjBy t = I.pCoreIn 2 :=
    eq_of_le_of_card_ge hle (by
      change Nat.card (I.pCoreIn 2) ≤ Nat.card ((I.pCoreIn 2).map (MulAut.conj t).toMonoidHom)
      rw [card_map_of_injective (MulAut.conj t).injective])
  have hIQ : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hSQ : d.S ≤ normalizer (I.pCoreIn 2 : Set G) :=
    (le_sup_right.trans hI.1.2).trans hIQ
  have hTQ : (d.T : Subgroup G) ≤ normalizer (I.pCoreIn 2 : Set G) := by
    intro x hx
    by_cases hxS : x ∈ d.S
    · exact hSQ hxS
    · have hxt : x * t⁻¹ ∈ d.S := by
        apply (d.S.subgroupOf (d.T : Subgroup G)).mul_mem_iff_of_index_two hindex
          (a := (⟨x, hx⟩ : d.T)) (b := (⟨t, ht⟩ : d.T)⁻¹) |>.mpr
        change x ∈ d.S ↔ t⁻¹ ∈ d.S
        simp only [d.S.inv_mem_iff, hxS, htS]
      simpa only [inv_mul_cancel_right] using
        (normalizer (I.pCoreIn 2 : Set G)).mul_mem (hSQ hxt)
          (mem_normalizer_iff_map_conj_eq.mpr heq)
  have hN := normalizer_le_of_unique_maximalTwoLocal hunique.2.2
    (isPGroup_pCoreIn 2 I) hI.1.1
    (sup_le (hYL.trans ((component_le c).trans hIQ)) hTQ)
  exact c.outside ((component_le c).trans (hIQ.trans hN))

/-- Irreducibility of the actual image of the parabolic two-core in `I*`.
For its elementary abelian model this is exactly absence of a proper nonzero
invariant binary subspace. -/
def StarCoreIrreducible (d : LocalData G) (I N : Subgroup G) : Prop :=
  ∀ A : Subgroup (d.Star I), A ≤ d.starImage I (N.pCoreIn 2) →
    d.starImage I N ≤ normalizer (A : Set (d.Star I)) →
    A = ⊥ ∨ A = d.starImage I (N.pCoreIn 2)

/-- The nonzero conjugate-core image generates the whole irreducible parabolic core. -/
theorem core_eq_sup_conjugate_of_irreducible (d : LocalData G) {I N : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S)
    (hSN : d.S ≤ N) (hNI : N ≤ I)
    (hTN : (d.T : Subgroup G) ≤ normalizer (N : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M)
    (hkernel : (d.starMap I).ker.map I.subtype = I.pCoreIn 2)
    (hirr : StarCoreIrreducible d I N)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    N.pCoreIn 2 = I.pCoreIn 2 ⊔ (I.pCoreIn 2).conjBy t := by
  let Q := I.pCoreIn 2
  let P := N.pCoreIn 2
  let f := d.starMap I
  have hIQ : I ≤ normalizer (Q : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hQS : Q ≤ d.S := hS ▸ pCoreIn_le_sylow I S
  have hQP : Q ≤ P := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    (hQS.trans hSN) (hNI.trans hIQ)
  have hTP : (d.T : Subgroup G) ≤ normalizer (P : Set G) :=
    hTN.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hQtP : Q.conjBy t ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hTP ht x).mp (hQP hx)
  have hPI : P ≤ I := (pCoreIn_le 2 N).trans hNI
  have hQtI : Q.conjBy t ≤ I := hQtP.trans hPI
  have hNQt : N ≤ normalizer (Q.conjBy t : Set G) :=
    normalizes_conjugate_of_normalizes (hTN ht) (hNI.trans hIQ)
  have hstable : d.starImage I N ≤
      normalizer (d.starImage I (Q.conjBy t) : Set (d.Star I)) := by
    have hcomap : N.subgroupOf I ≤ normalizer ((Q.conjBy t).subgroupOf I : Set I) :=
      (comap_mono hNQt).trans (le_normalizer_comap I.subtype)
    exact (map_mono hcomap).trans (le_normalizer_map f)
  have hne : d.starImage I (Q.conjBy t) ≠ ⊥ := by
    intro hzero
    have hle : (Q.conjBy t).subgroupOf I ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp hzero
    have hm := map_mono (f := I.subtype) hle
    rw [map_subgroupOf_eq_of_le hQtI, hkernel] at hm
    exact core_conjugate_not_le d hI c hYL hindex hunique t ht htS hm
  have himage : d.starImage I (Q.conjBy t) = d.starImage I P :=
    (hirr _ (map_mono (comap_mono hQtP)) hstable).resolve_left hne
  have hle : P.subgroupOf I ≤ (Q.conjBy t).subgroupOf I ⊔ f.ker :=
    map_le_map_iff.mp himage.ge
  have hm := map_mono (f := I.subtype) hle
  rw [map_subgroupOf_eq_of_le hPI, Subgroup.map_sup, map_subgroupOf_eq_of_le hQtI,
    hkernel, sup_comm] at hm
  exact le_antisymm hm (sup_le hQP hQtP)

/-- Identify both action centralizers with the two conjugate local cores. -/
theorem core_eq_actionCentralizers_of_irreducible (d : LocalData G) {I N : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S)
    (hSN : d.S ≤ N) (hNI : N ≤ I)
    (hTN : (d.T : Subgroup G) ≤ normalizer (N : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hunique : Chapter4.UniqueMaximalOvergroup (d.Yplus ⊔ (d.T : Subgroup G)) d.M)
    (hirr : StarCoreIrreducible d I N)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    let U := d.componentModule I c.L
    N ⊓ centralizer (U : Set G) ≤ d.S ∧
    N ⊓ centralizer (U.conjBy t : Set G) ≤ d.S ∧
    pCore 2 N = actionCentralizer N U ⊔ actionCentralizer N (U.conjBy t) := by
  let U := d.componentModule I c.L
  have hQS : I.pCoreIn 2 ≤ d.S := hS ▸ pCoreIn_le_sylow I S
  have hCU : N ⊓ centralizer (U : Set G) = I.pCoreIn 2 := by
    apply le_antisymm ((inf_le_inf_right _ hNI).trans hcentralizer.le)
    exact le_inf (hQS.trans hSN) (hcentralizer.ge.trans inf_le_right)
  have hmapN : N.map (MulAut.conj t).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (hTN ht)
  have hCV : N ⊓ centralizer (U.conjBy t : Set G) = (I.pCoreIn 2).conjBy t := by
    have he := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) hCU
    rw [map_inf _ _ _ (MulAut.conj t).injective, hmapN,
      Theory.Quasithin.map_centralizer] at he
    exact he
  have hTS : (d.T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).mp
      (normal_of_index_eq_two hindex)
  have hQtS : (I.pCoreIn 2).conjBy t ≤ d.S := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hTS ht x).mp (hQS hx)
  refine ⟨hCU ▸ hQS, hCV ▸ hQtS, ?_⟩
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_sup]
  change N.pCoreIn 2 =
    ((centralizer (U : Set G)).subgroupOf N).map N.subtype ⊔
      ((centralizer (U.conjBy t : Set G)).subgroupOf N).map N.subtype
  rw [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_comm _ N, hCU,
    inf_comm _ N, hCV]
  exact core_eq_sup_conjugate_of_irreducible d hI c hYL S hS hSN hNI hTN hindex
    hunique (star_kernel_eq_core_of_centralizer d c S hS hcentralizer) hirr t ht htS

/-- Conclusion (6) from the centralizer identification and irreducibility,
with the core-generation and kernel premises discharged. -/
theorem lemma_15_3_32_6_of_irreducible (d : LocalData G) {I N : Subgroup G}
    (hI : I ∈ d.Hplus) (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (a : NaturalEightAction I (d.componentModule I c.L))
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = d.S)
    (hSN : d.S ≤ N) (hNI : N ≤ I)
    (hTN : (d.T : Subgroup G) ≤ normalizer (N : Set G))
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hnoncentral : ¬ d.Yplus ≤ centralizer (d.V : Set G))
    (hcases : ∀ X : Subgroup G, (d.T : Subgroup G) ≤ X → X ≤ d.M →
      twoResidualAmbient X ≤ centralizer (d.V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X d.M)
    (hirr : StarCoreIrreducible d I N)
    (hcentralizer : I ⊓ centralizer (d.componentModule I c.L : Set G) = I.pCoreIn 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G)) (htS : t ∉ d.S) :
    let U := d.componentModule I c.L
    letI := pairKernel_normal (hNI.trans a.normalizes)
      (normalizes_conjugate_of_normalizes (hTN ht) (hNI.trans a.normalizes))
    let q := pairPlusMap N U (U.conjBy t)
    let A := ((d.S ⊓ centralizer (U : Set G)).subgroupOf N).map q
    let B := ((d.S ⊓ centralizer (U.conjBy t : Set G)).subgroupOf N).map q
    (pairKernel N U (U.conjBy t)).map N.subtype =
        d.S ⊓ centralizer ((U ⊔ U.conjBy t : Subgroup G) : Set G) ∧
      (pCore 2 N).map q = A ⊔ B ∧ Disjoint A B ∧
      ∃ e : A × B ≃* (pCore 2 N).map q,
        ∀ a b, (e (a, b) : PairPlus N U (U.conjBy t)) =
          (a : PairPlus N U (U.conjBy t)) * b := by
  obtain ⟨hCU, hCV, hcore⟩ := core_eq_actionCentralizers_of_irreducible d hI c hYL
    S hS hSN hNI hTN hindex (unique_yplus_join_sylow d hnoncentral hcases)
    hirr hcentralizer t ht htS
  exact lemma_15_3_32_6_of_core_generation N d.S _ _ hSN (hNI.trans a.normalizes)
    (normalizes_conjugate_of_normalizes (hTN ht) (hNI.trans a.normalizes)) hCU hCV hcore


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
