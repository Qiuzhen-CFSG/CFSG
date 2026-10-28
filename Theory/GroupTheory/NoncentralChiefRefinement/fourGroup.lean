module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Counting
public import Theory.GroupTheory.NoncentralChiefRefinement.OrderBound
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Chief factors of four-groups and quotients of twice odd order

A normal four-group disjoint from the ambient center has no intermediate
normal subgroup: a subgroup of order two would be central. It therefore
supplies one literal noncentral binary chief factor. Conversely a binary
noncentral section has order divisible by four, so an ambient group whose
order is not divisible by four has only central binary chief factors.

Source application: Aschbacher--Smith, 13.7.10(8), printed p.942.
-/

@[expose] public section
open Subgroup
namespace NoncentralChiefRefinement
variable {K : Type*} [Group K] [Finite K]
theorem four_chief_of_trivial_center (Z : NormalNode K)
    (hcard : Nat.card Z.val=4) (hz : Z.val⊓center K=⊥) : (⊥ : NormalNode K) ⋖ Z := by
  have hn : Z≠⊥ := by
    intro he
    have hc : Nat.card Z.val=1 := he ▸ card_bot
    omega
  refine ⟨bot_lt_iff_ne_bot.mpr hn,?_⟩
  intro W hW0 hWZ
  have hc : Nat.card W.val∣2^2 := by
    simpa [hcard] using card_dvd_of_le hWZ.le
  obtain ⟨k,hk,hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hc
  interval_cases k
  · have he : W=⊥ := Subtype.ext (eq_bot_of_card_eq W.val (by simpa using hkc))
    exact hW0.ne he.symm
  · have hcw : W.val≤center K := central_of_normal_card_two W.val (by simpa using hkc)
    have he : W=⊥ := Subtype.ext (le_antisymm ((le_inf (show W.val≤Z.val from hWZ.le) hcw).trans hz.le) bot_le)
    exact hW0.ne he.symm
  · have he : W=Z := Subtype.ext (eq_of_le_of_card_ge hWZ.le (by simpa [hcard] using hkc.ge))
    exact hWZ.ne he

omit [Finite K] in
/-- A normal four-group disjoint from the ambient center is one noncentral binary chief factor. -/
theorem four_noncentral_of_trivial_center (Z : NormalNode K)
    (hcard : Nat.card Z.val=4) (hz : Z.val⊓center K=⊥) : IsNoncentralTwo ⊥ Z := by
  constructor
  · have hp : IsPGroup 2 Z.val := IsPGroup.of_card (n:=2) hcard
    exact hp.of_surjective (QuotientGroup.mk' ((⊥ : NormalNode K).val.subgroupOf Z.val))
      (QuotientGroup.mk'_surjective _)
  · intro hc
    have hcomm : ⁅(⊤ : Subgroup K),Z.val⁆=⊥ := le_antisymm
      ((isCentral_iff_commutator_le _ _).mp hc) bot_le
    have hzc : Z.val≤center K := by
      simpa only [coe_top,centralizer_univ] using
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    have he : Z.val=⊥ := by simpa only [inf_eq_left.mpr hzc] using hz
    rw [he,card_bot] at hcard
    contradiction

/-- An explicit one-step chief series through the original four-group. -/
theorem exists_four_chief_refinement (Z : NormalNode K)
    (hcard : Nat.card Z.val=4) (hz : Z.val⊓center K=⊥) :
    ∃s:ChiefSeries K,s.head=⊥ ∧ s.last=Z ∧ s.length=1 ∧ s.noncentralTwoCount=1 := by
  classical
  let s : ChiefSeries K := (RelSeries.singleton _ (⊥ : NormalNode K)).snoc Z
    (four_chief_of_trivial_center Z hcard hz)
  refine ⟨s,rfl,rfl,rfl,?_⟩
  rw [ChiefSeries.noncentralTwoCount_eq_sum]
  change (∑i:Fin 1, if IsNoncentralTwo (⊥ : NormalNode K) Z then 1 else 0)=1
  simp only [four_noncentral_of_trivial_center Z hcard hz,if_true,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

/-- An ambient order with no factor four has only central binary chief factors. -/
theorem centralTwoChiefFactors_of_not_four_dvd (h4 : ¬4∣Nat.card K) : HasCentralPChiefFactors 2 K := by
  intro A B hA hB hAB _ hp
  let : A.Normal := hA
  let : B.Normal := hB
  by_contra hc
  let a : NormalNode K := ⟨A,hA⟩
  let b : NormalNode K := ⟨B,hB⟩
  have hn : IsNoncentralTwo a b := ⟨hp,hc⟩
  have hge := hn.four_le_card a b
  change 4≤Nat.card (B⧸A.subgroupOf B) at hge
  obtain ⟨n,hncard⟩ := hp.exists_card_eq
  rw [hncard] at hge
  have hn2 : 2≤n := by
    by_contra hh
    have hh' : n<2 := by omega
    interval_cases n <;> norm_num at hge
  have hd : 4∣Nat.card (Section a b) := by
    rw [hncard]
    exact pow_dvd_pow 2 hn2
  have hdiv : Nat.card (Section a b)∣Nat.card B :=
    ⟨Nat.card A,(section_card_mul a b hAB.le).symm⟩
  exact h4 (hd.trans (hdiv.trans (card_subgroup_dvd_card B)))

end NoncentralChiefRefinement
