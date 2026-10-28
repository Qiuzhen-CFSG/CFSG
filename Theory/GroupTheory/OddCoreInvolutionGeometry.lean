module
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Odd-core involutions

If the odd core is a three-group, excluding cubic subgroups from an
involution centralizer makes conjugation fixed-point-free on the odd core.
Surjectivity of its commutator map gives the full commutator identity.
For an abelian odd core in a solvable group with trivial two-core, two
involutions with full commutator both invert the core. Their product lies
in its centralizer; Fitting self-centralization and coprime orders force
that product to be trivial.

Application: Aschbacher--Smith 15.2.13, printed pp.1111--1112,
combined manuscript (1 March 2004), refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory
variable {D : Type*} [Group D] [Finite D]

/-- Absence of a cubic centralizer makes an involution move a cubic odd core. -/
theorem oddCore_commutator_of_three_centralizer
    (hO : IsPGroup 3 (pPrimeCore 2 D)) (t : D)
    (hC : ∀ C : Subgroup D, IsPGroup 3 C → C ≤ centralizer {t} → C = ⊥) :
    pPrimeCore 2 D = ⁅pPrimeCore 2 D, zpowers t⁆ := by
  let O := pPrimeCore 2 D
  have hz : O ⊓ centralizer {t} = ⊥ :=
    hC _ (hO.to_le inf_le_left) inf_le_right
  have hf : MonoidHom.FixedPointFree (MulAut.conjNormal t : MulAut O) := by
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hz]
    refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hx)).symm
  apply le_antisymm _ (commutator_le_left _ _)
  intro x hx
  obtain ⟨y,hy⟩ := hf.commutatorMap_surjective (⟨x,hx⟩ : O)
  have he : (y : D) / (t * (y : D) * t⁻¹) = x := congrArg Subtype.val hy
  rw [←he]
  have hh := commutator_mem_commutator y.property (mem_zpowers t)
  simpa only [commutatorElement_def,div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc] using hh

/-- In a solvable group with trivial two-core and abelian odd core, at most
one order-two subgroup of a two-subgroup moves the entire odd core. -/
theorem oddCore_involution_subgroup_unique
    (hs : Group.IsSolvable D) (hcore : pCore 2 D = ⊥)
    [IsMulCommutative (pPrimeCore 2 D)]
    (P A B : Subgroup D) (hp : IsPGroup 2 P)
    (hAP : A ≤ P) (hBP : B ≤ P) (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (ha : pPrimeCore 2 D = ⁅pPrimeCore 2 D,A⁆)
    (hb : pPrimeCore 2 D = ⁅pPrimeCore 2 D,B⁆) : A = B := by
  let O := pPrimeCore 2 D
  let : IsCyclic A := isCyclic_of_prime_card hA
  let : IsCyclic B := isCyclic_of_prime_card hB
  obtain ⟨a,hea⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  obtain ⟨b,heb⟩ := B.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hao : orderOf a = 2 := by rw [←Nat.card_zpowers,hea]; exact hA
  have hbo : orderOf b = 2 := by rw [←Nat.card_zpowers,heb]; exact hB
  have hai := inverts_abelian_of_full_commutator O a
    ⟨fun he => by simp [he] at hao, hao ▸ pow_orderOf_eq_one a⟩ (hea ▸ ha.symm)
  have hbi := inverts_abelian_of_full_commutator O b
    ⟨fun he => by simp [he] at hbo, hbo ▸ pow_orderOf_eq_one b⟩ (heb ▸ hb.symm)
  have hab : a*b ∈ centralizer (O : Set D) := by
    intro r hr
    have hh : (a*b)*r*(a*b)⁻¹ = r := by
      calc
        (a*b)*r*(a*b)⁻¹ = a*(b*r*b⁻¹)*a⁻¹ := by group
        _ = a*r⁻¹*a⁻¹ := by rw [hbi ⟨r,hr⟩]
        _ = r := by simpa using hai (⟨r,hr⟩ : O)⁻¹
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hO := centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs hcore hab
  have hP : a*b ∈ P := P.mul_mem (hAP (hea ▸ mem_zpowers a))
    (hBP (heb ▸ mem_zpowers b))
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : Disjoint P O := disjoint_of_coprime_natCard (by
    rw [hn]; exact (pPrimeCore_coprime_card (p := 2) (G := D)).pow_left n)
  have he : a*b = 1 := disjoint_def.mp hd hP hO
  have heab : a = b := by
    calc
      a = b⁻¹ := eq_inv_of_mul_eq_one_left he
      _ = b := inv_eq_of_mul_eq_one_left (by simpa only [←pow_two,←hbo] using pow_orderOf_eq_one b)
  rw [←hea,←heb,heab]
end Theory.GroupTheory
