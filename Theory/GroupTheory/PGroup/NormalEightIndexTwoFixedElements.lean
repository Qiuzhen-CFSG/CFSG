module

public import Theory.GroupTheory.PGroup.NormalEightCriticalSubgroup
public import Theory.GroupTheory.PGroup.HomocyclicDeepInvolution
public import Theory.GroupTheory.PGroup.NormalEightCentralAction
public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupAction.C4SquareCThreeCentralizer

/-!
# Fixed elements of outside involutions in the abelian index-two case

Let an abelian critical subgroup C of a finite two-group be homocyclic of
rank two, of exponent at least four, and of index two. Suppose central omega
has order four and there is no normal elementary subgroup of order eight.
An abstract automorphism of order three acting freely on C forces each
outside involution to centralize only elements of C with square one.

Conjugation by the outside involution commutes with the cubic action on C:
the automorphism preserves C and both outside elements have the same coset.
Restrict the two actions to the characteristic four-torsion subgroup, which
is C4 × C4. The cubic restriction is nontrivial by its fixed-point-free
hypothesis. If the involution restriction were trivial, the deep-involution
calculation and the normal-eight obstruction would put the involution in C
(the exponent-four case follows directly from critical self-centralization).
The C4 × C4 centralizer theorem therefore bounds its fixed elements by the
two-torsion. Repeated squaring gives the same bound throughout C. This avoids
any matrix calculation at an arbitrary homocyclic exponent.

Source context: the homocyclic abelian index-two case of MacWilliams,
Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3, and
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386.
No realization of the cubic automorphism by ambient conjugation is used.
-/

open Subgroup

namespace IsCriticalPSubgroup

private theorem square_eq_one_of_four_torsion_fixed_bound
    {D : Type*} [Group D] (hD : IsPGroup 2 D) (b : MulAut D)
    (hfour : ∀ d : D, d ^ 4 = 1 → b d = d → d ^ 2 = 1)
    (d : D) (hd : b d = d) : d ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hD.exists_pow_pow_eq_one d
  induction k generalizing d with
  | zero =>
    simp only [pow_zero, pow_one] at hk
    simp [hk]
  | succ k ih =>
    have hs : (d ^ 2) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hk
    have hf : b (d ^ 2) = d ^ 2 := by rw [map_pow, hd]
    have hh := ih (d ^ 2) hf hs
    exact hfour d (by simpa only [← pow_mul] using hh) hd

private theorem fixed_square_eq_one_of_nontrivial_four_action
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (hD : IsPGroup 2 D) (n : ℕ) (hn : 2 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a b : MulAut D) (ha : a ^ 3 = 1)
    (hfree : ∀ d : D, a d = d → d = 1) (hab : Commute b a)
    (hb : OmegaAction.omegaRestriction D 2 2 b ≠ 1)
    (d : D) (hd : b d = d) : d ^ 2 = 1 := by
  let O := omega D (p := 2) 2
  let r := OmegaAction.omegaRestriction D 2 2
  let eO : O ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    (e.omega 2 2).trans (OmegaAction.productOmegaEquiv n n 2 hn hn)
  have hane : r a ≠ 1 := by
    intro hh
    have hall (x : O) : x = 1 := by
      apply Subtype.ext
      apply hfree
      exact congrArg (fun f : MulAut O => (f x : D)) hh
    let : Subsingleton O := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hc : Nat.card O = 16 := by
      rw [Nat.card_congr eO.toEquiv]
      norm_num [Nat.card_prod, Nat.card_eq_fintype_card]
    have hc1 : Nat.card O = 1 := Nat.card_unique
    omega
  apply square_eq_one_of_four_torsion_fixed_bound hD b _ d hd
  intro x hx hfix
  let y : O := ⟨x, subset_closure hx⟩
  have hy : y ^ 2 = 1 :=
    c4_square_fixed_point_square_eq_one_of_commuting_three ⟨eO⟩
      (r a) (by rw [← map_pow, ha, map_one]) hane (r b) hb (hab.map r) y
      (Subtype.ext hfix)
  exact congrArg Subtype.val hy

/-- An outside involution fixes only square-one elements of an abelian
critical subgroup of index two with a fixed-point-free cubic action. -/
public theorem fixed_square_eq_one_of_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (C : Subgroup P) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hi : C.index = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (n : ℕ) (hn : 2 ≤ n)
    (e : C ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))))
    (a : MulAut P) (ha : orderOf a = 3)
    (hfree : ∀ c ∈ C, a c = c → c = 1) :
    ∀ t : P, orderOf t = 2 → t ∉ C →
      ∀ c ∈ C, Commute c t → c ^ 2 = 1 := by
  let : C.Characteristic := hC.characteristic
  let f : P →* MulAut C := MulAut.conjNormal
  let aC : MulAut C := MulAut.characteristic C a
  have hself : centralizer (C : Set P) ≤ C := by
    rw [hC.centralizer_eq]
    exact map_subtype_le _
  have htriv (g : P) (hg : g ∈ C) : f g = 1 := by
    ext d
    change g * (d : P) * g⁻¹ = d
    rw [(C.le_centralizer hg d d.property).symm, mul_inv_cancel_right]
  intro t ht hout c hc hct
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hat : a t ∉ C := by
    intro hh
    exact hout ((characteristic_iff_comap_eq.mp hC.characteristic a) ▸ hh)
  have hdiff : a t * t⁻¹ ∈ C := by
    rw [mul_mem_iff_of_index_two hi]
    simp only [inv_mem_iff, hat, hout]
  have hfeq : f (a t) = f t := by
    have hh := htriv _ hdiff
    rw [map_mul, map_inv, mul_inv_eq_one] at hh
    exact hh
  have hcomm : Commute (f t) aC := by
    apply MulEquiv.ext
    intro d
    have hh : f (a t) (aC d) = aC (f t d) := by
      apply Subtype.ext
      change a t * a (d : P) * (a t)⁻¹ = a (t * (d : P) * t⁻¹)
      simp only [map_mul, map_inv]
    simpa only [hfeq, MulAut.mul_apply] using hh
  have hb : OmegaAction.omegaRestriction C 2 2 (f t) ≠ 1 := by
    intro hzero
    have hfour : ∀ d : C, d ^ 4 = 1 → f t d = d :=
      (OmegaAction.mem_ker_restriction_iff f 2 2 t).mp hzero
    by_cases hn2 : n = 2
    · have hall (d : C) : f t d = d := by
        apply hfour
        apply e.injective
        rw [map_pow, map_one]
        have hp (x : Multiplicative (ZMod (2 ^ n))) : x ^ 4 = 1 := by
          subst n
          simpa [Nat.card_eq_fintype_card] using pow_card_eq_one' (x := x)
        exact Prod.ext (hp (e d).1) (hp (e d).2)
      apply hout
      apply hself
      intro d hd
      have hh := congrArg Subtype.val (hall ⟨d, hd⟩)
      change t * d * t⁻¹ = d at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · have hdeep := IsPGroup.deep_involution_of_homocyclic_fixing_four_torsion
        n (by omega) e (f t) (by rw [← map_pow, ht2, map_one]) hfour
      apply hout
      apply IsPGroup.involution_mem_normal_abelian_of_central_action_of_no_normal_eight
        hno hZ C hself t ht2
      · intro g
        apply hdeep.1 (f g)
        exact IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight hno hZ C hself g
      · intro d hd hdi
        exact congrArg Subtype.val (hdeep.2 ⟨d, hd⟩ (Subtype.ext hdi))
  have hres : (⟨c, hc⟩ : C) ^ 2 = 1 :=
    fixed_square_eq_one_of_nontrivial_four_action (hP.to_subgroup C) n hn e aC (f t)
      (by dsimp [aC]; rw [← map_pow, show a ^ 3 = 1 from ha ▸ pow_orderOf_eq_one a, map_one])
      (fun d hd => Subtype.ext (hfree d d.property (congrArg Subtype.val hd)))
      hcomm hb ⟨c, hc⟩ (by
        apply Subtype.ext
        change t * c * t⁻¹ = c
        rw [hct.symm.eq, mul_inv_cancel_right])
  exact congrArg Subtype.val hres

end IsCriticalPSubgroup
