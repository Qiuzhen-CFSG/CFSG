module

public import Theory.GroupTheory.CenterFreeOddCoreCentralizer
public import Theory.GroupAction.C4SquareCThreeCentralizer
public import Mathlib.Tactic

/-!
# Primitive-point centralizers in a C4-square residual

Let E and Q be normal subgroups of a finite center-free group P, with
E supplementing a supplied Sylow two-subgroup, Q a two-group, E∩Q a
C4-square group, and the E image modulo Q of order three. If r∈E∩Q has
nontrivial square, its centralizer in Q is precisely E∩Q.

The center-free residual theorem identifies the full residual centralizer
in Q with R=E∩Q. Actual conjugation on R has a nontrivial E image of order
three, and the Q image commutes with it. A nonidentity automorphism of R
commuting with this cubic action fixes only square-one points. Therefore
every Q-element fixing the chosen primitive point lies in the full kernel.

This supplies the primitive-point centralizer calculation preceding (8)
in Stellmacher (10.1)(a3), printed p.61 of
`refs/files/stellmacher-n-group.pdf`. The native geometric adapter is separate.
-/

open Subgroup
open scoped IsMulCommutative

private theorem conjugation_kernel
    {P : Type*} [Group P] (R : Subgroup P) [R.Normal] :
    (MulAut.conjNormal (H := R)).ker = centralizer (R : Set P) := by
  ext g
  rw [MonoidHom.mem_ker, mem_centralizer_iff]
  constructor
  · intro h r hr
    have hh := congrArg (fun f : MulAut R => (f ⟨r, hr⟩ : P)) h
    change g * r * g⁻¹ = r at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro h
    ext r
    change g * (r : P) * g⁻¹ = (r : P)
    rw [← h r r.property, mul_inv_cancel_right]

public theorem inf_centralizer_singleton_eq_of_centerfree_c4_square_primitive
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q : Subgroup P) [E.Normal] [Q.Normal]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hQ : IsPGroup 2 Q)
    (hcenter : center P = ⊥)
    (model : Nonempty ((E ⊓ Q : Subgroup P) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (himage : Nat.card (E.map (QuotientGroup.mk' Q)) = 3)
    (r : (E ⊓ Q : Subgroup P)) (hr : r^2 ≠ 1) :
    Q ⊓ centralizer ({(r:P)} : Set P) = E ⊓ Q := by
  classical
  let R := E ⊓ Q
  have hRp : IsPGroup 2 R := hQ.to_le inf_le_right
  obtain ⟨equiv⟩ := model
  let _ : IsMulCommutative R := IsMulCommutative.of_comm fun x y =>
    equiv.injective (by simp only [map_mul]; exact mul_comm _ _)
  have hRcard : Nat.card R = 16 := by
    rw [Nat.card_congr equiv.toEquiv]
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card]
  let K := Q ⊓ centralizer (R : Set P)
  have hK : K = R := inf_centralizer_inf_eq_of_centerfree_odd_image
    S E Q hcover hQ hcenter (by rw [himage]; decide)
  have hindex : R.relIndex E = 3 := by
    dsimp [R]
    rw [inf_relIndex_left, ← QuotientGroup.ker_mk' Q, relIndex_ker]
    exact himage
  let action : P →* MulAut R := MulAut.conjNormal
  have hker : action.ker = centralizer (R : Set P) := conjugation_kernel R
  have hRker : R ≤ action.ker := hker ▸ le_centralizer R
  have hRcentralE : R ⊓ centralizer (E : Set P) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S E R hcover hRp hcenter
  have himageNe : E.map action ≠ ⊥ := by
    intro hz
    have hEk : E ≤ action.ker := (Subgroup.map_eq_bot_iff _).mp hz
    have hRC : R ≤ centralizer (E : Set P) :=
      le_centralizer_iff.mp (hker ▸ hEk)
    have hbot : R = ⊥ := by simpa only [inf_eq_left.mpr hRC] using hRcentralE
    rw [hbot, card_bot] at hRcard
    omega
  have himageDvd : Nat.card (E.map action) ∣ 3 := by
    rw [← relIndex_ker, ← hindex]
    exact relIndex_dvd_of_le_left E hRker
  have himageThree : Nat.card (E.map action) = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp himageDvd with hone | hthree
    · exact False.elim (himageNe (card_eq_one.mp hone))
    · exact hthree
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := E.map action) 3
    (by rw [himageThree])
  have ha3 : (a : MulAut R) ^ 3 = 1 := by
    exact congrArg Subtype.val (ha ▸ pow_orderOf_eq_one a)
  have hane : (a : MulAut R) ≠ 1 := by
    intro heq
    have haa : a = 1 := Subtype.ext heq
    rw [haa, orderOf_one] at ha
    omega
  have hcentral : Q.map action ≤ centralizer (E.map action : Set (MulAut R)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (commutator_le_inf Q E).trans ((inf_comm Q E).le.trans hRker)
  apply le_antisymm
  · intro q hq
    have hfix : action q r = r := by
      apply Subtype.ext
      change q*(r:P)*q⁻¹=(r:P)
      have hc := mem_centralizer_iff.mp hq.2 (r:P) (Set.mem_singleton _)
      rw [← hc,mul_inv_cancel_right]
    have hone : action q = 1 := by
      by_contra hne
      exact hr (c4_square_fixed_point_square_eq_one_of_commuting_three
        ⟨equiv⟩ a ha3 hane (action q) hne
          (mem_centralizer_iff.mp (hcentral (mem_map_of_mem action hq.1)) a a.property).symm
            r hfix)
    have hqK : q ∈ K := ⟨hq.1,hker ▸ MonoidHom.mem_ker.mpr hone⟩
    exact hK.le hqK
  · intro q hq
    refine ⟨hq.2,?_⟩
    change q ∈ centralizer ({(r:P)} : Set P)
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : x=(r:P) := Set.mem_singleton_iff.mp hx
    subst x
    exact setLike_mul_comm (s:=R) r.property hq
