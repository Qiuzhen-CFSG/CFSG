module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Extracting an odd-prime obstruction from an inverted cyclic torus

If a cyclic torus has order p+1 with p > 1 and p ≡ 1 modulo four, choose an
odd prime r dividing (p+1)/2. The kernel of its r-th power map has order r
and is preserved by every normalizer of the torus. An actor containing an
inverter z has a commutator outside C(z): otherwise an element of order r
would have fourth power one. Transport retains the literal ambient action
on a normal subgroup; it does not discard outer elements.

This is the elementary extraction step for the unitary branch of
Aschbacher--Smith E.1.14(7), printed p.214. The torus and its normalization
remain explicit geometric premises, supplied separately by the matrix model.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {G : Type*} [Group G] [Finite G]

private theorem odd_prime_dvd_succ {p : ℕ} (hp : 1 < p) (hm : p % 4 = 1) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ p + 1 := by
  have hhalf : 1 < (p + 1) / 2 := by omega
  obtain ⟨r, hr, hd⟩ := Nat.exists_prime_and_dvd (by omega : (p + 1) / 2 ≠ 1)
  have ho : Odd ((p + 1) / 2) := ⟨p / 4, by omega⟩
  refine ⟨r, hr, Odd.of_dvd_nat ho hd, hd.trans ?_⟩
  exact Nat.div_dvd_of_dvd (by omega : 2 ∣ p + 1)

/-- An inverted cyclic torus supplies an odd-prime subgroup normalized by the same actor. -/
theorem escape_of_inverted_cyclic (D A R : Subgroup G) [IsCyclic D]
    {p : ℕ} (hp : 1 < p) (hm : p % 4 = 1) (hc : Nat.card D = p + 1)
    (z : G) (hz : z ∈ A)
    (hinv : ∀ x ∈ D, z * x * z⁻¹ = x⁻¹)
    (hn : R ≤ normalizer (D : Set G)) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧ R ≤ normalizer (X : Set G) ∧
        ¬ ⁅X, A⁆ ≤ centralizer ({z} : Set G) := by
  obtain ⟨r, hr, ho, hd⟩ := odd_prime_dvd_succ hp hm
  let : Fact r.Prime := ⟨hr⟩
  let := IsCyclic.commGroup (α := D)
  let K : Subgroup D := (powMonoidHom r : D →* D).ker
  have hK : Nat.card K = r := by
    rw [IsCyclic.card_powMonoidHom_ker, hc, Nat.gcd_eq_right hd]
  let X := K.map D.subtype
  have hXcard : Nat.card X = r := (Nat.card_congr
    (K.equivMapOfInjective D.subtype D.subtype_injective).toEquiv).symm.trans hK
  have hX : IsPGroup r X := IsPGroup.of_card (n := 1) (by simpa using hXcard)
  have hXD : X ≤ D := map_subtype_le K
  have hnorm : R ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hym : g * (y : G) * g⁻¹ ∈ D := (mem_normalizer_iff.mp (hn hg) y).mp y.property
    refine ⟨⟨g * (y : G) * g⁻¹, hym⟩, ?_, rfl⟩
    change (⟨g * (y : G) * g⁻¹, hym⟩ : D) ^ r = 1
    apply Subtype.ext
    change (g * (y : G) * g⁻¹) ^ r = 1
    have hy' : (y : G) ^ r = 1 := congrArg Subtype.val (show y ^ r = 1 from hy)
    simpa only [map_pow, map_one, MulAut.conj_apply] using
      congrArg (MulAut.conj g) hy'
  refine ⟨r, hr, ho, X, hX, hnorm, ?_⟩
  intro hcentral
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) r (hXcard ▸ dvd_rfl)
  have hxinv := hinv (x : G) (hXD x.property)
  have hxinv' : z * (x : G)⁻¹ * z⁻¹ = (x : G) := by
    have h := congrArg Inv.inv hxinv
    simpa [mul_assoc] using h
  have he : ⁅(x : G), z⁆ = (x : G) ^ 2 := by
    calc
      ⁅(x : G), z⁆ = (x : G) * (z * (x : G)⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def, mul_assoc]
      _ = (x : G) ^ 2 := by rw [hxinv', pow_two]
  have hcomm := mem_centralizer_singleton_iff.mp
    (hcentral (commutator_mem_commutator x.property hz))
  rw [he] at hcomm
  have hi2 : z * (x : G) ^ 2 * z⁻¹ = ((x : G) ^ 2)⁻¹ := by
    exact hinv _ (D.pow_mem (hXD x.property) 2)
  have hfour : (x : G) ^ 4 = 1 := by
    rw [← hcomm, mul_inv_cancel_right] at hi2
    calc
      (x : G) ^ 4 = (x : G) ^ 2 * (x : G) ^ 2 := by rw [← pow_add]
      _ = 1 := (congrArg (fun y : G => y * (x : G) ^ 2) hi2).trans (inv_mul_cancel _)
  have hd4 : r ∣ 4 := by
    rw [← hx, ← Subgroup.orderOf_coe]
    exact orderOf_dvd_of_pow_eq_one hfour
  have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow (show r ∣ 2 ^ 2 by norm_num; exact hd4)
  have heq : r = 2 := le_antisymm (Nat.le_of_dvd (by decide) hr2) hr.two_le
  exact ho.not_two_dvd_nat (heq ▸ dvd_rfl)

/-- Transport the torus and its full normalizing action through a normal subgroup model. -/
theorem escape_of_model_torus {M : Type*} [Group M]
    (L : Subgroup G) [L.Normal] (e : L ≃* M) (A R : Subgroup G)
    (D : Subgroup M) [IsCyclic D] {p : ℕ} (hp : 1 < p) (hm : p % 4 = 1)
    (hc : Nat.card D = p + 1) (z : L) (hz : (z : G) ∈ A)
    (hinv : ∀ x ∈ D, e z * x * (e z)⁻¹ = x⁻¹)
    (hpres : ∀ g ∈ R, ∀ x ∈ D, e (MulAut.conjNormal g (e.symm x)) ∈ D) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup G,
      IsPGroup r X ∧ R ≤ normalizer (X : Set G) ∧
        ¬ ⁅X, A⁆ ≤ centralizer ({(z : G)} : Set G) := by
  let f : M →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  let H := D.map f
  let ed : D ≃* H := D.equivMapOfInjective f hf
  let : IsCyclic H := ed.isCyclic.mp inferInstance
  have hHcard : Nat.card H = p + 1 := (Nat.card_congr ed.toEquiv).symm.trans hc
  have hez : f (e z) = (z : G) := by simp [f]
  have hHinv : ∀ x ∈ H, (z : G) * x * (z : G)⁻¹ = x⁻¹ := by
    rintro x ⟨y, hy, rfl⟩
    simpa only [map_mul, map_inv, hez] using congrArg f (hinv y hy)
  have hnorm : R ≤ normalizer (H : Set G) := by
    apply le_normalizer_iff.mpr
    rintro g hg x ⟨y, hy, rfl⟩
    refine ⟨e (MulAut.conjNormal g (e.symm y)), hpres g hg y hy, ?_⟩
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, Subgroup.subtype_apply, MulAut.conjNormal_apply]
  exact escape_of_inverted_cyclic H A R hp hm hHcard z hz hHinv hnorm
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
