module
public import Theory.GroupTheory.ZStar.OddCore

/-!
# Central elements in odd-kernel images

A central image under a homomorphism with odd kernel is central modulo the
actual odd core. An involution remains nonidentity there. Inversion on a
group, when it is an automorphism, commutes with every automorphism.

These elementary observations supply the final quotient step in
Aschbacher–Smith, Lemma A.1.28, printed p.26.
-/

open Subgroup
namespace Theory.GroupTheory
variable {G B : Type*} [Group G] [Finite G] [Group B]

omit [Finite G] in
/-- A central image under an action with odd kernel is central modulo the
odd core. -/
public theorem mem_center_oddCore_of_mem_center_image
    (f : G →* B) (hker : Odd (Nat.card f.ker)) (t : G)
    (ht : f t ∈ center B) :
    QuotientGroup.mk' (pPrimeCore 2 G) t ∈ center (G ⧸ pPrimeCore 2 G) := by
  have hk : f.ker ≤ pPrimeCore 2 G := le_sSup ⟨inferInstance, hker.coprime_two_left⟩
  apply Glauberman.ZStar.mem_center_quotient_of_commutators_mem
  intro g
  apply hk
  change f (g * t * g⁻¹ * t⁻¹) = 1
  simp only [map_mul, map_inv]
  rw [mem_center_iff.mp ht (f g), mul_inv_cancel_right, mul_inv_cancel]

/-- An involution central in an odd-kernel image supplies a nontrivial element
of the center of the actual odd-core quotient. -/
public theorem center_oddCore_ne_bot_of_involution_central_image
    (f : G →* B) (hker : Odd (Nat.card f.ker)) (t : G)
    (ht : orderOf t = 2) (hcentral : f t ∈ center B) :
    center (G ⧸ pPrimeCore 2 G) ≠ ⊥ := by
  intro hb
  have he := mem_center_oddCore_of_mem_center_image f hker t hcentral
  rw [hb, mem_bot] at he
  have hm := (QuotientGroup.eq_one_iff t).mp he
  have hdvd : 2 ∣ Nat.card (pPrimeCore 2 G) :=
    ht ▸ (pPrimeCore 2 G).orderOf_dvd_natCard hm
  exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) hdvd

/-- Inversion commutes with every automorphism whenever it is itself an
automorphism. This formulation does not require a separate commutativity
instance on the underlying group. -/
public theorem mem_center_mulAut_of_inverts {V : Type*} [Group V]
    (a : MulAut V) (ha : ∀ v : V, a v = v⁻¹) : a ∈ center (MulAut V) := by
  rw [mem_center_iff]
  intro b
  ext v
  change b (a v) = a (b v)
  rw [ha, map_inv, ha]
end Theory.GroupTheory
