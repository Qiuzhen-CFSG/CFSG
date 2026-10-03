module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Group

/-!
# Fixed-point-free automorphisms of order three

A finite group with a fixed-point-free automorphism of order three has
nilpotency class at most two. The norm identity first shows that every
individual element commutes with its image. Polarizing this identity and
using surjectivity of the automorphism commutator map makes every group
commutator central.

Source: B. H. Neumann's theorem, as used in G. Higman, *Suzuki 2-groups*,
Illinois J. Math. 7 (1963), Lemma 6. The checked group-word proof is extracted
from `BenderSuzuki/External/Higman/lemma_6.lean`, with only Mathlib dependencies.
-/

namespace MulAut

open scoped commutatorElement

universe u

private def neumannKappa {Q : Type u} [Group Q] (x y : Q) : Q :=
  x⁻¹ * y⁻¹ * x * y

private theorem neumannKappa_mul_left
    {Q : Type u} [Group Q] (x y z : Q) :
    neumannKappa (x * y) z =
      y⁻¹ * neumannKappa x z * y * neumannKappa y z := by
  simp [neumannKappa]
  group

private theorem neumannKappa_balanced_of_commutes
    {Q : Type u} [Group Q] (phi : MulAut Q)
    (hcomm : ∀ q : Q, Commute q (phi q)) (x y : Q) :
    neumannKappa (phi x) y = neumannKappa x (phi y) := by
  have hp := (hcomm (x * y⁻¹)).eq
  simp only [map_mul, map_inv] at hp
  have hp' := congrArg
    (fun t : Q => (phi x)⁻¹ * x⁻¹ * t * y * phi y) hp
  group at hp'
  have hba_inv : Commute (phi x) x⁻¹ :=
    Commute.inv_right_iff.mpr (hcomm x).symm
  have hp'' :
      (phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y =
        x⁻¹ * (phi y)⁻¹ * x := by
    simpa [hba_inv.inv_mul_cancel] using hp'
  calc
    neumannKappa (phi x) y =
        ((phi x)⁻¹ * y⁻¹ * phi x * (phi y)⁻¹ * y) * phi y := by
      simp [neumannKappa, mul_assoc, (hcomm y).symm.inv_mul_cancel]
    _ = (x⁻¹ * (phi y)⁻¹ * x) * phi y :=
      congrArg (fun t : Q => t * phi y) hp''
    _ = neumannKappa x (phi y) := by
      simp [neumannKappa, mul_assoc]

private theorem neumannKappa_conj_eq_of_balanced
    {Q : Type u} [Group Q] (phi : MulAut Q)
    (hbal : ∀ x y : Q,
      neumannKappa (phi x) y = neumannKappa x (phi y))
    (x z y : Q) :
    (phi y)⁻¹ * neumannKappa x (phi z) * phi y =
      y⁻¹ * neumannKappa x (phi z) * y := by
  have h := hbal (x * y) z
  simp only [map_mul, neumannKappa_mul_left] at h
  rw [hbal x z, hbal y z] at h
  exact mul_right_cancel h

private theorem neumannKappa_delta_commute_of_conj_eq
    {Q : Type u} [Group Q] (phi : MulAut Q)
    (hconj : ∀ x z y : Q,
      (phi y)⁻¹ * neumannKappa x (phi z) * phi y =
        y⁻¹ * neumannKappa x (phi z) * y)
    (x z y : Q) :
    Commute (neumannKappa x (phi z)) (phi y * y⁻¹) := by
  rw [commute_iff_eq]
  have h := congrArg (fun t : Q => phi y * t * y⁻¹) (hconj x z y)
  group at h
  simpa [mul_assoc] using h

/-- The irreducible Neumann order-three core, retaining the exact-order and
fixed-point-free hypotheses while exposing the derived period-three norm
identity used by the group-word argument. -/
private theorem neumann_order_three_product_identity_class_le_two_core
    {Q : Type u} [Group Q] [Finite Q]
    (phi : MulAut Q)
    (_hphi_order : orderOf phi = 3)
    (hphi_fixedPointFree : ∀ x : Q, phi x = x → x = 1)
    (hphi_period : (fun q : Q => phi q)^[3] = id)
    (hphi_product : ∀ q : Q, q * phi q * phi (phi q) = 1) :
    (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥ := by
  have hthird (q : Q) : phi (phi (phi q)) = q := by
    have h := congrFun hphi_period q
    simpa [Function.iterate_succ_apply] using h
  have hcomm (q : Q) : Commute q (phi q) := by
    have hq := hphi_product q
    have hqq := hphi_product (q * phi q)
    simp only [map_mul] at hqq
    rw [hthird] at hqq
    have hc : phi (phi q) = (q * phi q)⁻¹ :=
      eq_inv_of_mul_eq_one_right hq
    rw [hc] at hqq
    group at hqq
    rw [commute_iff_eq]
    have hconj : q * phi q * q⁻¹ = phi q := by
      apply mul_inv_eq_one.mp
      simpa [mul_assoc] using hqq
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hbal : ∀ x y : Q,
      neumannKappa (phi x) y = neumannKappa x (phi y) :=
    neumannKappa_balanced_of_commutes phi hcomm
  have hconj : ∀ x z y : Q,
      (phi y)⁻¹ * neumannKappa x (phi z) * phi y =
        y⁻¹ * neumannKappa x (phi z) * y :=
    neumannKappa_conj_eq_of_balanced phi hbal
  have hdelta : ∀ x z y : Q,
      Commute (neumannKappa x (phi z)) (phi y * y⁻¹) :=
    neumannKappa_delta_commute_of_conj_eq phi hconj
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => phi q) := by
    intro q hq
    exact hphi_fixedPointFree q hq
  have hsurj :
      Function.Surjective
        (MonoidHom.commutatorMap (fun q : Q => phi q)) :=
    MonoidHom.FixedPointFree.commutatorMap_surjective hFPF
  have hkappa_central (x w g : Q) :
      Commute (neumannKappa x w) g := by
    obtain ⟨y, hy⟩ := hsurj g⁻¹
    have hy' : phi y * y⁻¹ = g := by
      have hi := congrArg (fun t : Q => t⁻¹) hy
      simpa [MonoidHom.commutatorMap_apply, div_eq_mul_inv] using hi
    have h := hdelta x (phi.symm w) y
    simpa [hy'] using h
  have hcommutator_central (x y g : Q) : Commute ⁅x, y⁆ g := by
    have h := hkappa_central x⁻¹ y⁻¹ g
    simpa [neumannKappa, commutatorElement_def] using h
  change (⊤ : Subgroup Q).lowerCentralSeries (1 + 1) = ⊥
  rw [Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [commutator_eq_closure, Subgroup.closure_le]
  rintro c ⟨x, y, rfl⟩
  change ∀ g : Q, g ∈ (⊤ : Subgroup Q) →
    g * ⁅x, y⁆ = ⁅x, y⁆ * g
  intro g hg
  exact (hcommutator_central x y g).symm.eq
/-- The theorem of B. H. Neumann used in Higman Lemma 6: a finite group with
a fixed-point-free automorphism of order three has nilpotency class at most
two. -/
public theorem lowerCentralSeries_two_eq_bot_of_orderOf_eq_three_of_fixedPointFree
    {Q : Type u} [Group Q] [Finite Q]
    (phi : MulAut Q)
    (hphi_order : orderOf phi = 3)
    (hphi_fixedPointFree : ∀ x : Q, phi x = x → x = 1) :
    (⊤ : Subgroup Q).lowerCentralSeries 2 = ⊥ := by
  classical
  have hFPF : MonoidHom.FixedPointFree (fun q : Q => phi q) := by
    intro q hq
    exact hphi_fixedPointFree q hq
  have hpow_apply : ∀ k q, (phi ^ k) q = (fun q : Q => phi q)^[k] q := by
    intro k
    induction k with
    | zero => intro q; simp
    | succ k ih =>
        intro q
        simp [pow_succ, Function.iterate_succ, ih]
  have hphi_period : (fun q : Q => phi q)^[3] = id := by
    ext q
    have hpow : (phi ^ 3 : MulAut Q) = 1 := by
      rw [← hphi_order]
      exact pow_orderOf_eq_one phi
    have hq := congrArg (fun g : MulAut Q => g q) hpow
    change (phi ^ 3) q = q at hq
    rw [hpow_apply] at hq
    simpa using hq
  have hphi_product (q : Q) : q * phi q * phi (phi q) = 1 := by
    have hnorm := MonoidHom.FixedPointFree.prod_pow_eq_one hFPF hphi_period q
    simpa [Function.iterate_succ_apply, mul_assoc] using hnorm
  exact neumann_order_three_product_identity_class_le_two_core
    phi hphi_order hphi_fixedPointFree hphi_period hphi_product

/-- Every commutator is central when an order-three automorphism is fixed-point-free. -/
public theorem commutator_le_center_of_orderOf_eq_three_of_fixedPointFree
    {Q : Type*} [Group Q] [Finite Q] (phi : MulAut Q)
    (hphi_order : orderOf phi = 3)
    (hphi_fixedPointFree : MonoidHom.FixedPointFree phi) :
    commutator Q ≤ Subgroup.center Q := by
  have h := phi.lowerCentralSeries_two_eq_bot_of_orderOf_eq_three_of_fixedPointFree
    hphi_order hphi_fixedPointFree
  rw [show 2 = 1 + 1 from rfl, Subgroup.lowerCentralSeries_succ,
    Subgroup.top_lowerCentralSeries_one,
    Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  simpa only [Subgroup.coe_top, Subgroup.centralizer_univ] using h

end MulAut
