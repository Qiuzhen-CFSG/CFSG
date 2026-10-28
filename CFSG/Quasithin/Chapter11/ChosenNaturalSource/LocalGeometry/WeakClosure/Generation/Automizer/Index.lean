module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer.Cartan
public import Theory.NumberTheory.BinarySemilinearTorusPowers

/-!
# Bounding Cartan parameters by the index of the actual layer

A Cartan element normalizes the layer Sylow by solvable Sylow control.
Its index-th power belongs to the normal layer, so the inner Borel exponent
bounds its order after multiplication by that index. Primitive divisors
then bound the Cartan parameter even when the index contributes additional
split-torus factors. All intersections and normalizers are relative to the
original group; the layer may have a nontrivial center.

Source: Aschbacher--Smith A.3.15 and 11.2.1, pp.50--51,766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
variable {X : Type*} [Group X] [Finite X]

/-- The layer index and inner Borel exponent annihilate each odd normalizer element. -/
theorem normalizer_pow_eq_one_of_layer_index (K : Subgroup X) [K.Normal]
    {r : ℕ}
    (hexp : ∀ (Q : Sylow 2 K) (b : K), b ∈ normalizer (Q : Set K) →
      Odd (orderOf b) → b ^ r = 1)
    (P : Sylow 2 X) (a : X)
    (ha : a ∈ normalizer ((P : Subgroup X) ⊓ K : Set X))
    (ho : Odd (orderOf a)) : a ^ (K.index * r) = 1 := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal K
  let b : K := ⟨a ^ K.index, K.pow_index_mem a⟩
  have hb : b ∈ normalizer (Q : Set K) := by
    have hn := (normalizer ((P : Subgroup X) ⊓ K : Set X)).pow_mem ha K.index
    have hsub : ((P : Subgroup X) ⊓ K).subgroupOf K = (Q : Subgroup K) := by
      rw [hQ]
      ext x
      exact and_iff_left x.property
    change b ∈ normalizer ((Q : Subgroup K) : Set K)
    rw [← hsub, ← subgroupOf_normalizer_eq (show (P : Subgroup X) ⊓ K ≤ K from inf_le_right)]
    exact hn
  have hob : Odd (orderOf b) := by
    rw [Subgroup.orderOf_mk]
    exact ho.of_dvd_nat (orderOf_pow_dvd _)
  have he := congrArg Subtype.val (hexp Q b hb hob)
  simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_mul] using he

/-- A split-torus index bound suffices for the full ambient Cartan parameter. -/
theorem nPrime_le_of_even_layer_index (K : Subgroup X) [K.Normal]
    (hK : SolvableSylowControl 2 K) {n k : ℕ} (hn : 0 < n)
    (hindex : K.index ∣ 2 * (n * (2 ^ n - 1) ^ k))
    (hexp : ∀ (Q : Sylow 2 K) (b : K), b ∈ normalizer (Q : Set K) →
      Odd (orderOf b) → b ^ (2 ^ n - 1) = 1) : nPrime X ≤ n := by
  apply nPrime_le_iff.mpr
  intro c w
  let := w.cyclic
  obtain ⟨a,ha⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic w.cyclicGroup)
  have ho : Odd (orderOf (a : X)) := by
    rw [Subgroup.orderOf_coe, ha]
    exact w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  have hmem : (a : X) ∈ normalizer ((w.sylow : Subgroup X) ⊓ K : Set X) :=
    witness_normalizes_layer_sylow K hK w (mem_sup_left (w.cyclic_le a.property))
  have hd := orderOf_dvd_of_pow_eq_one
    (normalizer_pow_eq_one_of_layer_index K hexp w.sylow a hmem ho)
  rw [Subgroup.orderOf_coe, ha, w.card] at hd
  apply Theory.NumberTheory.binary_mersenne_exponent_le_of_torus_power_dvd hn
    (k := k + 1)
  have h := hd.trans (Nat.mul_dvd_mul hindex (dvd_refl (2 ^ n - 1)))
  have ho' : Odd (2 ^ c - 1) := by
    rwa [Subgroup.orderOf_coe, ha, w.card] at ho
  apply ho'.coprime_two_right.dvd_of_dvd_mul_left
  simpa only [pow_succ, mul_assoc] using h

/-- The odd-index version omits the harmless factor two. -/
theorem nPrime_le_of_layer_index (K : Subgroup X) [K.Normal]
    (hK : SolvableSylowControl 2 K) {n k : ℕ} (hn : 0 < n)
    (hindex : K.index ∣ n * (2 ^ n - 1) ^ k)
    (hexp : ∀ (Q : Sylow 2 K) (b : K), b ∈ normalizer (Q : Set K) →
      Odd (orderOf b) → b ^ (2 ^ n - 1) = 1) : nPrime X ≤ n :=
  nPrime_le_of_even_layer_index K hK hn
    (hindex.trans (dvd_mul_left _ 2)) hexp

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Automizer
