module

public import Theory.GroupTheory.CenterFreeOddCoreCentralizer
public import Theory.GroupAction.C4SquareCThreeCentralizer
public import Mathlib.Tactic

/-!
# A center-free group with a C4-square residual intersection

Let a normal subgroup E supplement a supplied Sylow two-subgroup in a finite
center-free group P. Suppose Q is a normal two-subgroup, E has image of order
three in P/Q, and R=E∩Q is isomorphic to C4×C4. Then |Q|≤64. The theorem
retains the supplied normality instances, quotient image, and model of the
actual intersection; no faithful action is included among its hypotheses.

The normal subgroup K=Q∩C_P(R) contains R and satisfies E∩K=R. Its E quotient
image therefore still has order three, and [K,E]≤R centralizes K. The proved
center-free odd-image collapse gives K=R. Conjugation on R now has kernel R
inside Q. Its E image divides three and cannot be trivial, since C_R(E)=1.
The Q image centralizes that order-three action because [Q,E]≤R. The
C4-square automorphism-centralizer bound makes this two-group image have at
most four elements. Kernel times image gives |Q|≤16·4.

This source-neutral group calculation supplies the upper Sylow estimate in
Stellmacher (10.1)(a1), printed pp.60–61,
`refs/files/stellmacher-n-group.pdf`. The native graph adapter is separate.
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

public theorem card_le_sixtyfour_of_centerfree_c4_square_residual
    {P : Type*} [Group P] [Finite P]
    (S : Sylow 2 P) (E Q : Subgroup P) [E.Normal] [Q.Normal]
    (hcover : E ⊔ (S : Subgroup P) = ⊤) (hQ : IsPGroup 2 Q)
    (hcenter : center P = ⊥)
    (model : Nonempty ((E ⊓ Q : Subgroup P) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (himage : Nat.card (E.map (QuotientGroup.mk' Q)) = 3) :
    Nat.card Q ≤ 64 := by
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
  have hbound : Nat.card (Q.map action) ≤ 4 :=
    two_group_c4_square_automorphism_centralizer_card_le_four ⟨equiv⟩ a ha3 hane
      (Q.map action) (hQ.map action) (by
        intro c hc
        exact (mem_centralizer_iff.mp (hcentral hc) a a.property).symm)
  have hQindex : R.relIndex Q = Nat.card (Q.map action) := by
    calc
      R.relIndex Q = K.relIndex Q := congrArg (fun J : Subgroup P => J.relIndex Q) hK.symm
      _ = (action.ker ⊓ Q).relIndex Q := by
        congr 1
        dsimp [K]
        rw [hker, inf_comm]
      _ = Nat.card (Q.map action) := by rw [inf_relIndex_right, relIndex_ker]
  have hcount := (R.subgroupOf Q).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show R ≤ Q from inf_le_right)).toEquiv] at hcount
  change Nat.card R * R.relIndex Q = Nat.card Q at hcount
  rw [hRcard, hQindex] at hcount
  omega
