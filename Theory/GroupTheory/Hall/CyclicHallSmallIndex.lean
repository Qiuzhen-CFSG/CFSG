module
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PermutingSupCard
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Finite.Perm

/-!
# Cyclic odd Hall subgroups in overgroups of index at most three

Let a solvable finite group have trivial two-core and a subgroup M of index
at most three with a cyclic odd Hall subgroup. The normal core N of M has
trivial two-core, and its odd core lies in its cyclic odd Hall subgroup.
Fitting self-centralization then makes every two-subgroup of N abelian.
The coset action bounds the index of N in each two-subgroup by two.

For pairwise permuting products DP and EP, with E of order three normalizing
D, the whole actor (D join P) join E has D join P of index at most three.
Consequently its two-core is nontrivial if P has no abelian subgroup of index
at most two. This is used for the full J₄ Sylow in Aschbacher--Smith 5.1.13,
printed p.637, refs/quasithin.pdf. The cyclic odd-core argument follows the
proof in `WreathedCyclicHall.lean`, without importing its wreathed hypotheses.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.CyclicHallSmallIndex
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normal_le_hall (D N : Subgroup G) [N.Normal]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (hN : Odd (Nat.card N)) : N ≤ D := by
  have hcop : Nat.Coprime (Nat.card N) D.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpD
    have hp2 : p = 2 := Classical.not_not.mp
      (hD.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpD)
    exact hN.not_two_dvd_nat (hp2 ▸ hpN)
  have hd : D.relIndex N ∣ D.index := by
    rw [←relIndex_sup_of_normalizes N D le_normalizer_of_normal]
    exact relIndex_dvd_index_of_le le_sup_right
  exact relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card D N) hd)

private theorem abelian_of_core_eq_bot
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (hc : pCore 2 G = ⊥)
    (P : Subgroup G) (hP : IsPGroup 2 P) : IsMulCommutative P := by
  have hOD : pPrimeCore 2 G ≤ D := odd_normal_le_hall D _ hD
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : IsCyclic (pPrimeCore 2 G) :=
    isCyclic_of_injective (inclusion hOD) (inclusion_injective hOD)
  have hd : _root_.commutator G ≤ pPrimeCore 2 G :=
    (commutator_le_centralizer_of_isCyclic_normal (pPrimeCore 2 G)).trans
      (centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs hc)
  have hcomm : ⁅P,P⁆ ≤ pPrimeCore 2 G :=
    (commutator_mono (show P ≤ ⊤ from le_top) le_top).trans hd
  have hdis : Disjoint P (pPrimeCore 2 G) := by
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact pPrimeCore_coprime_card.pow_left k
  exact commutator_self_eq_bot_iff.mp
    (le_bot_iff.mp ((le_inf (commutator_le_self P) hcomm).trans hdis.le_bot))

/-- A cyclic odd Hall subgroup in a subgroup of index at most three forces
an abelian subgroup of index at most two in every two-subgroup, if O₂ is trivial. -/
theorem exists_abelian_index_le_two
    (hs : Group.IsSolvable G) (M D : Subgroup G) (hDM : D ≤ M)
    [IsCyclic D] (hD : IsHallSubgroup OddHall.oddPrimes (D.subgroupOf M))
    (hindex : M.index ≤ 3) (hc : pCore 2 G = ⊥)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative A ∧ A.index ≤ 2 := by
  let := hs
  let N := M.normalCore
  let A := N.subgroupOf P
  let Q := P.subgroupOf N
  have hDN : IsHallSubgroup OddHall.oddPrimes (D.subgroupOf N) :=
    OddHall.hall_restrict_of_normalizes hD hDM M.normalCore_le le_normalizer_of_normal
  let j : D.subgroupOf N →* D :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : IsCyclic (D.subgroupOf N) := isCyclic_of_injective j (by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : D => (z : G)) he)))
  have hcN : pCore 2 N = ⊥ := by
    rw [pCore_eq_comap_of_normal, hc]
    exact N.subtype.ker_eq_bot N.subtype_injective
  have hab : IsMulCommutative Q := abelian_of_core_eq_bot
    (inferInstance : Group.IsSolvable N) (D.subgroupOf N) hDN hcN Q hP.comap_subtype
  have habA : IsMulCommutative A := by
    refine isMulCommutative_iff.mpr ?_
    intro x y
    exact Subtype.ext (Subtype.ext (congrArg (fun q : Q => (q.val.val : G))
      (isMulCommutative_iff.mp hab ⟨⟨x.val.val,x.property⟩,x.val.property⟩
        ⟨⟨y.val.val,y.property⟩,y.val.property⟩)))
  have hfac : N.index ∣ 6 := by
    have hh : M.normalCore.index ∣ M.index.factorial := by
      rw [normalCore_eq_ker,index_ker,index_eq_card,←Nat.card_perm]
      exact card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ M)).range
    exact hh.trans (Nat.factorial_dvd_factorial hindex)
  have hdiv : A.index ∣ 6 := (N.relIndex_dvd_index_of_normal P).trans hfac
  obtain ⟨k,hk⟩ := (hP.to_quotient A).exists_card_eq
  change Nat.card (P ⧸ A) = 2^k at hk
  rw [←index_eq_card] at hk
  have hi : A.index ≤ 2 := by
    rw [hk] at hdiv ⊢
    rcases k with _ | _ | k
    · decide
    · decide
    · have hh : 4 ∣ 6 := (pow_dvd_pow 2 (show 2 ≤ k+2 by omega)).trans hdiv
      norm_num at hh
  exact ⟨A,inferInstance,habA,hi⟩
end Theory.GroupTheory.CyclicHallSmallIndex

namespace Theory.GroupTheory.CyclicHallSmallIndex
variable {G : Type*} [Group G] [Finite G]

/-- The odd factor in a permuting product with a two-group is an odd Hall subgroup. -/
theorem oddHall_of_permutes (D P : Subgroup G)
    (hD : Odd (Nat.card D)) (hP : IsPGroup 2 P)
    (hp : (D : Set G) * (P : Set G) = (P : Set G) * (D : Set G)) :
    IsHallSubgroup OddHall.oddPrimes (D.subgroupOf (D ⊔ P)) := by
  obtain ⟨k,hk⟩ := hP.exists_card_eq
  have hdis : Disjoint D P := by
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_right.mpr hD).pow_right k
  have hcard := card_sup_eq_mul_of_permutes_of_disjoint D P hp hdis
  have hDcard : Nat.card (D.subgroupOf (D ⊔ P)) = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe (show D ≤ D ⊔ P from le_sup_left)).toEquiv
  have hi : (D.subgroupOf (D ⊔ P)).index = 2^k := by
    have hh := (D.subgroupOf (D ⊔ P)).card_mul_index
    rw [hDcard,hcard,hk] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  constructor
  · intro p hd he
    have he' : p.val = 2 := he
    rw [hDcard,he'] at hd
    exact hD.not_two_dvd_nat hd
  · intro p hd he
    rw [hi] at hd
    exact he (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two hd)

/-- Pairwise permuting Hall products give a subgroup of index at most three
in the whole actor; normalization is required only for the two odd factors. -/
theorem product_index_le_three (D P E : Subgroup G)
    (hDE : E ≤ normalizer (D : Set G)) (hE : Nat.card E = 3)
    (hDP : (D : Set G) * (P : Set G) = (P : Set G) * (D : Set G))
    (hEP : (E : Set G) * (P : Set G) = (P : Set G) * (E : Set G)) :
    (D ⊔ P).relIndex ((D ⊔ P) ⊔ E) ≤ 3 := by
  let M := D ⊔ P
  let K := M ⊔ E
  have hME : (M : Set G) * (E : Set G) = (E : Set G) * (M : Set G) := by
    rw [show (M : Set G) = (D : Set G) * (P : Set G) from
      coe_sup_eq_mul_of_permutes D P hDP]
    rw [mul_assoc,←hEP,←mul_assoc,←set_mul_normalizer_comm (E : Set G) D hDE,mul_assoc]
  let m : M × E → K := fun x => ⟨x.1.val*x.2.val,mul_mem_sup x.1.property x.2.property⟩
  have hm : Function.Surjective m := by
    intro x
    have hx : x.val ∈ (M : Set G) * (E : Set G) := by
      rw [←coe_sup_eq_mul_of_permutes M E hME]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  have hb := Nat.card_le_card_of_surjective m hm
  rw [Nat.card_prod,hE] at hb
  have hc := (M.subgroupOf K).card_mul_index
  have hmc : Nat.card (M.subgroupOf K) = Nat.card M :=
    Nat.card_congr (subgroupOfEquivOfLe (show M ≤ K from le_sup_left)).toEquiv
  rw [hmc] at hc
  have hmpos : 0 < Nat.card M := Nat.card_pos
  change (M.subgroupOf K).index ≤ 3
  nlinarith

omit [Finite G] in
private theorem permutes_subgroupOf (D P K : Subgroup G) (hD : D ≤ K) (hP : P ≤ K)
    (hp : (D : Set G) * (P : Set G) = (P : Set G) * (D : Set G)) :
    (D.subgroupOf K : Set K) * (P.subgroupOf K : Set K) =
      (P.subgroupOf K : Set K) * (D.subgroupOf K : Set K) := by
  apply Set.image_injective.mpr K.subtype_injective
  simpa only [Set.image_mul,←coe_map,map_subgroupOf_eq_of_le hD,
    map_subgroupOf_eq_of_le hP] using hp

/-- A whole solvable Hall actor has nontrivial two-core when its supplied
two-subgroup has no abelian subgroup of index at most two. -/
theorem twoCore_ne_bot_of_products (D P E : Subgroup G) [IsCyclic D]
    (hD : Odd (Nat.card D)) (hP : IsPGroup 2 P)
    (hDE : E ≤ normalizer (D : Set G)) (hE : Nat.card E = 3)
    (hDP : (D : Set G) * (P : Set G) = (P : Set G) * (D : Set G))
    (hEP : (E : Set G) * (P : Set G) = (P : Set G) * (E : Set G))
    (hsol : Group.IsSolvable ((D ⊔ P) ⊔ E : Subgroup G))
    (hna : ∀ A : Subgroup P, A.index ≤ 2 → ¬ IsMulCommutative A) :
    pCore 2 ((D ⊔ P) ⊔ E : Subgroup G) ≠ ⊥ := by
  intro hc
  let M := D ⊔ P
  let K := M ⊔ E
  have hDK : D ≤ K := le_sup_left.trans le_sup_left
  have hPK : P ≤ K := le_sup_right.trans le_sup_left
  let D' := D.subgroupOf K
  let P' := P.subgroupOf K
  let M' := M.subgroupOf K
  have heM : D' ⊔ P' = M' := (subgroupOf_sup hDK hPK).symm
  let eD := subgroupOfEquivOfLe hDK
  let eP := subgroupOfEquivOfLe hPK
  let : IsCyclic D' := isCyclic_of_injective eD.toMonoidHom eD.injective
  have hh : IsHallSubgroup OddHall.oddPrimes (D'.subgroupOf M') := by
    rw [←heM]
    apply oddHall_of_permutes D' P'
      (by change Odd (Nat.card (D.subgroupOf K)); rw [Nat.card_congr eD.toEquiv]; exact hD) hP.comap_subtype
    exact permutes_subgroupOf D P K hDK hPK hDP
  obtain ⟨A,_,ha,hi⟩ := exists_abelian_index_le_two hsol M' D'
    (by rw [←heM]; exact le_sup_left) hh
    (product_index_le_three D P E hDE hE hDP hEP) hc P' hP.comap_subtype
  let := ha
  apply hna (A.map eP.toMonoidHom)
  · exact (index_map_of_bijective (f := eP.toMonoidHom) eP.bijective A).le.trans hi
  · exact A.map_isMulCommutative eP.toMonoidHom
end Theory.GroupTheory.CyclicHallSmallIndex
