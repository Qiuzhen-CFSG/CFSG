module

public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# Prime rank under homomorphisms and adjoining a central involution

An elementary abelian subgroup has order equal to the product of its
kernel and image orders. Applying the elementary-cardinality criterion
therefore bounds prime rank by the sum of the kernel and target ranks.
The same count with a subgroup intersection gives the index bound.
An independent centralizing involution extends each elementary abelian
two-subgroup by a direct factor of order two.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.3.9, printed p.1180, inequalities (i) and (!).
-/

public section

open Subgroup
namespace Theory.GroupTheory
open scoped IsMulCommutative

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
private theorem elementary_intersection {p : ℕ} (E C : Subgroup G)
    [IsElementaryAbelian p E] : IsElementaryAbelian p (E.subgroupOf C) := by
  refine {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative C E
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (A := E) x.1.1 x.2

/-- Prime rank is bounded by the ranks of the kernel and the target. -/
theorem primeRank_le_ker_add {p : ℕ} [Fact p.Prime] (f : G →* H) :
    primeRank p G ≤ primeRank p f.ker + primeRank p H := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  let fE : E →* H := f.comp E.subtype
  let A : Subgroup f.ker := E.subgroupOf f.ker
  have hA : IsElementaryAbelian p A := elementary_intersection _ _
  have hB : IsElementaryAbelian p (E.map f) := IsElementaryAbelian.map f
  have hAc := (primeRank_le_iff_elementary_card_le f.ker).mp le_rfl A hA
  have hBc := (primeRank_le_iff_elementary_card_le H).mp le_rfl (E.map f) hB
  let e : fE.ker ≃* A :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hcard : Nat.card E = Nat.card A * Nat.card (E.map f) := by
    rw [← fE.ker.card_mul_index, index_ker, Nat.card_congr e.toEquiv]
    simp only [fE, MonoidHom.range_comp, range_subtype]
  rw [hcard, pow_add]
  exact Nat.mul_le_mul hAc hBc

/-- An independent centralizing involution adds one to two-rank. -/
theorem primeRank_succ_le_sup_zpowers (K : Subgroup G) (t : G) (ht : orderOf t = 2)
    (hKt : K ≤ centralizer ({t} : Set G)) (htK : t ∉ K) :
    primeRank 2 K + 1 ≤ primeRank 2 (K ⊔ zpowers t : Subgroup G) := by
  let J := K ⊔ zpowers t
  let tJ : J := ⟨t, (le_sup_right : zpowers t ≤ J) (mem_zpowers t)⟩
  change primeRank 2 K + 1 ≤ primeRank 2 J
  have htJ : orderOf tJ = 2 := (orderOf_coe tJ).symm.trans ht
  have hpos : 1 ≤ primeRank 2 J := by
    let : IsElementaryAbelian 2 (zpowers tJ) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (htJ ▸ pow_orderOf_eq_one tJ)
    exact IsElementaryAbelian.primeRank_ge_of_card (zpowers tJ) (by
      simpa only [Nat.card_zpowers, pow_one] using htJ)
  suffices primeRank 2 K ≤ primeRank 2 J - 1 by omega
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro E hE
  let := hE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  let e : K →* J := inclusion le_sup_left
  let A := E.map e
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map e
  have hAcard : Nat.card A = 2 ^ n := by
    rw [card_map_of_injective (inclusion_injective le_sup_left)]
    exact hn
  have htA : tJ ∉ A := by
    rintro ⟨x, _, hx⟩
    have hxv : (x : G) = t := congrArg (fun a : J => (a : G)) hx
    exact htK (hxv ▸ x.property)
  have hAt : A ≤ centralizer ({tJ} : Set J) := by
    rintro x ⟨y, _, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hKt y.property)
  have hbound := IsElementaryAbelian.primeRank_ge_of_fixed_join A tJ htJ htA hAt hAcard
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- A subgroup of small index gives an additive prime-rank bound. -/
theorem primeRank_le_add_of_index_le {p n : ℕ} [Fact p.Prime] (C : Subgroup G)
    (hC : C.index ≤ p ^ n) : primeRank p G ≤ primeRank p C + n := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  have hEC : IsElementaryAbelian p (E.subgroupOf C) := elementary_intersection _ _
  have hcard := (primeRank_le_iff_elementary_card_le C).mp le_rfl (E.subgroupOf C) hEC
  let e : C.subgroupOf E ≃ E.subgroupOf C :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hswap := Nat.card_congr e
  have hi : (C.subgroupOf E).index ≤ p ^ n := by
    have hi : C.relIndex E ≤ C.index := by
      simpa only [relIndex_top_right] using
        (relIndex_le_of_le_right (H := C) (K := E) (L := ⊤) le_top (by
          simpa only [relIndex_top_right] using C.index_ne_zero_of_finite))
    exact hi.trans hC
  rw [← (C.subgroupOf E).card_mul_index, pow_add]
  exact Nat.mul_le_mul (hswap ▸ hcard) hi

end Theory.GroupTheory
