module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.BinarySquares

/-!
# Exponent-four groups with transitive central involutions

In a nonabelian finite two-group of exponent four, suppose all involutions
are central and automorphisms are transitive on them. Then the center,
derived subgroup, Frattini subgroup and first omega subgroup coincide.

If a central element had nontrivial square, transitivity would give a
central square root of the square of any noncentral element. Their quotient
would be an involution, a contradiction. Thus the center is elementary.
Squares, hence commutators and the Frattini subgroup, lie in the center.
The nontrivial characteristic derived subgroup contains all involutions by
transitivity and therefore equals the center.

This elementary reduction isolates the intrinsic structural calculation in
Janko–Thompson, Math. Z. 113 (1970), Lemma 5.1, p.393, from the order and
exponent bounds supplied by the MacWilliams classification.
-/

namespace IsPGroup

open Subgroup

/-- If automorphisms are transitive on the elements of prime order, every
nontrivial characteristic subgroup contains first omega. -/
public theorem omega_one_le_characteristic_of_transitive_prime_order
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P)
    (htrans : ∀ x y : P, orderOf x = p → orderOf y = p →
      ∃ a : MulAut P, a x = y)
    (K : Subgroup P) [K.Characteristic] (hK : K ≠ ⊥) :
    omega₁ P (p := p) ≤ K := by
  have hdiv : p ∣ Nat.card K :=
    (hP.to_subgroup K).card_eq_or_dvd.resolve_left (fun h => hK (card_eq_one.mp h))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) p hdiv
  apply (closure_le K).mpr
  intro x hx
  change x ∈ K
  have hxp : x ^ p = 1 := by simpa using hx
  by_cases hx1 : x = 1
  · simpa only [hx1] using K.one_mem
  obtain ⟨a, ha⟩ := htrans z x ((orderOf_coe z).trans hz)
    (orderOf_eq_prime hxp hx1)
  have hm : a z ∈ K := characteristic_iff_le_comap.mp inferInstance a z.property
  rwa [ha] at hm

/-- Transitive central involutions and exponent four force a nonabelian
finite two-group to be special, with elementary center equal to first omega. -/
public theorem special_of_exponent_four_of_transitive_involutions
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hexp : ∀ x : P, x ^ 4 = 1) :
    center P = commutator P ∧ center P = frattini P ∧
      IsElementaryAbelian 2 (center P) ∧ center P = omega₁ P (p := 2) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq (x : P) : (x ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using hexp x
  have hcenterPow (z : P) (hz : z ∈ center P) : z ^ 2 = 1 := by
    by_contra hz2
    have hnZ : center P ≠ ⊤ := fun he => hnonab (center_eq_top_iff.mp he)
    obtain ⟨x, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hnZ)
    have hx2 : x ^ 2 ≠ 1 := fun he => hx.2 (hcentral x he)
    obtain ⟨a, ha⟩ := htrans (z ^ 2) (x ^ 2)
      (orderOf_eq_prime (hsq z) hz2) (orderOf_eq_prime (hsq x) hx2)
    have haz : a z ∈ center P := characteristic_iff_le_comap.mp inferInstance a hz
    have ha2 : (a z) ^ 2 = x ^ 2 := by simpa only [map_pow] using ha
    have hcomm : Commute x (a z)⁻¹ :=
      (show Commute x (a z) from mem_center_iff.mp haz x).inv_right
    have hquot : (x * (a z)⁻¹) ^ 2 = 1 := by
      rw [hcomm.mul_pow, inv_pow, ha2, mul_inv_cancel]
    have hc := (center P).mul_mem (hcentral _ hquot) haz
    exact hx.2 (by simpa only [inv_mul_cancel_right] using hc)
  let hE : IsElementaryAbelian 2 (center P) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
        (fun z => Subtype.ext (hcenterPow z z.property)) }
  have hOmega : omega₁ P (p := 2) = center P := by
    apply le_antisymm ?_ elementaryAbelian_le_omega₁
    apply (closure_le _).mpr
    intro x hx
    exact hcentral x (by simpa using hx)
  have hSquares : closure (Set.range fun x : P => x ^ 2) ≤ center P := by
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact hcentral _ (hsq x)
  have hD : commutator P ≤ center P := commutator_le_closure_squares.trans hSquares
  have hDne : commutator P ≠ ⊥ := fun he => hnonab ((commutator_eq_bot_iff P).mp he)
  obtain ⟨d, hd⟩ := ne_bot_iff_exists_ne_one.mp hDne
  have hd1 : (d : P) ≠ 1 := fun he => hd (Subtype.ext he)
  have hdord : orderOf (d : P) = 2 :=
    orderOf_eq_prime (hcenterPow d (hD d.property)) hd1
  have hZD : center P ≤ commutator P := by
    intro z hz
    by_cases hz1 : z = 1
    · simpa only [hz1] using (commutator P).one_mem
    obtain ⟨a, ha⟩ := htrans d z hdord (orderOf_eq_prime (hcenterPow z hz) hz1)
    have hamem : a d ∈ commutator P :=
      characteristic_iff_le_comap.mp inferInstance a d.property
    rwa [ha] at hamem
  have hF : frattini P ≤ center P := by
    rw [hP.frattini_eq_closure_squares]
    exact hSquares
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  exact ⟨le_antisymm hZD hD,
    le_antisymm (hZD.trans (commutator_le_frattini_of_isPGroup (p := 2))) hF,
    hE, hOmega.symm⟩

end IsPGroup
