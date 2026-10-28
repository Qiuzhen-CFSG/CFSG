module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer
public import Theory.GroupTheory.SylowKernelCore

/-!
# Inverters of the ordinary natural-line residual

The normalizer of the four-letter A₄ preserves its two fixed letters.
An even element of that normalizer outside A₄ inverts A₄/O₂(A₄): a
kernel-checked calculation on the twelve permutations in the other coset
shows that each inversion displacement has square one. The quotient has
order three, so these displacements lie in its two-core.

An even normalizing subgroup whose order is divisible by eight cannot lie
in A₄, of order twelve. It therefore supplies such an inverter. Conjugation
transports the result to the actual natural-line residual. The fixed-letter
argument follows `OrdinaryNormalizer`; the finite enumeration uses the
four-letter permutation API of `BinaryFlags`.

Source: Aschbacher–Smith, 13.8.20, printed p.954/PDF p.971, and the
ordinary natural-action setup of Notation 13.2.1, printed pp.876–877.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryInverter
open NaturalGeometry NaturalPairing BinaryPermutation Representation.BinaryOffender
private theorem common_fixed (i : Fin 6) (ha : cycle012 i = i) (hb : cycle013 i = i) :
    i = 4 ∨ i = 5 := by
  exact (by decide : ∀ j : Fin 6, cycle012 j = j → cycle013 j = j → j = 4 ∨ j = 5) i ha hb

private theorem normalizer_K_le : normalizer (K : Set S) ≤ H1 := by
  intro g hg
  have hfix (i : Fin 6) (hi : i = 4 ∨ i = 5) (k : S) (hk : k ∈ K) : k (g i) = g i := by
    have hh := le_normalizer_iff.mp (le_refl (normalizer (K : Set S)))
      g⁻¹ ((normalizer (K : Set S)).inv_mem hg) k hk
    have hh' := (mem_K.mp hh).1
    have he : (g⁻¹ * k * (g⁻¹)⁻¹) i = i := by rcases hi with rfl | rfl; exact hh'.1; exact hh'.2
    have hf := congrArg g he
    change g (g.symm (k (g i))) = g i at hf
    simpa only [g.apply_symm_apply] using hf
  have h4 := common_fixed (g 4) (hfix 4 (Or.inl rfl) cycle012 (by decide))
    (hfix 4 (Or.inl rfl) cycle013 (by decide))
  have h5 := common_fixed (g 5) (hfix 5 (Or.inr rfl) cycle012 (by decide))
    (hfix 5 (Or.inr rfl) cycle013 (by decide))
  have hn : g 4 ≠ g 5 := g.injective.ne (by decide)
  change (pair 4 5).image g = pair 4 5
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
    simp_all [pair, Finset.pair_comm]


private def words : List S := (permsOfList [0, 1, 2, 3]).filter (fun g => decide (g ∈ K))
private theorem mem_words (g : S) : g ∈ words ↔ g ∈ K := by
  rw [words, List.mem_filter, decide_eq_true_eq]
  refine ⟨And.right, fun hg => ⟨?_, hg⟩⟩
  apply mem_permsOfList_of_mem
  intro x hx
  fin_cases x <;> simp_all [mem_K]
private instance : Fintype K := Fintype.ofFinset words.toFinset (by
  intro g
  simp only [List.mem_toFinset]
  exact mem_words g)
private theorem card_K : Nat.card K = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def oddWords : List S :=
  ((permsOfList [0, 1, 2, 3]).map (fun g => swap45 * g)).filter (fun g => decide (g ∈ L1))
private theorem mem_oddWords (g : S) (hg : g ∈ L1) (hn : g ∉ K) : g ∈ oddWords := by
  rw [oddWords, List.mem_filter, decide_eq_true_eq]
  refine ⟨?_, hg⟩
  rcases mem_H1_cases hg.1 with h | h
  · exact (hn ⟨h, hg.2⟩).elim
  · apply List.mem_map.mpr
    refine ⟨swap45 * g, ?_, ?_⟩
    · apply mem_permsOfList_of_mem
      intro i hi
      fin_cases i <;> simp_all [swap45, Equiv.Perm.mul_apply]
    · simp [swap45, ← mul_assoc]

set_option maxRecDepth 4096 in
private theorem inverter_cert : oddWords.all (fun g =>
    decide (∀ x : K, (g * x.val * g⁻¹ * x.val) ^ 2 = 1)) = true := by decide +kernel

private theorem canonical_square (g : S) (hg : g ∈ L1) (hn : g ∉ K)
    (x : S) (hx : x ∈ K) : (g * x * g⁻¹ * x) ^ 2 = 1 := by
  have hc : ∀ g ∈ oddWords, ∀ x : K, (g * x.val * g⁻¹ * x.val) ^ 2 = 1 := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using inverter_cert
  exact hc g (mem_oddWords g hg hn) ⟨x, hx⟩

/-- An even subgroup with eight dividing its order, normalizing an embedded
four-letter A₄, contains an element inducing inversion modulo its two-core. -/
theorem exists_inverter_of_conjugate (R Q : Subgroup S)
    (hQ : Q ≤ alternatingGroup (Fin 6)) (hc : 8 ∣ Nat.card Q)
    (hn : Q ≤ normalizer (R : Set S))
    (hR : ∃ g : S, R.map (MulAut.conj g).toMonoidHom = K) :
    ∃ t ∈ Q, ∀ x ∈ R, t * x * t⁻¹ * x ∈ R.pCoreIn 2 := by
  obtain ⟨g, hg⟩ := hR
  let e := MulAut.conj g
  let Q' := Q.map e.toMonoidHom
  have hn' : Q' ≤ normalizer (K : Set S) := by
    rw [← hg]
    exact (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  have hQ' : Q' ≤ L1 := by
    refine le_inf (hn'.trans normalizer_K_le) ?_
    rintro _ ⟨q, hq, rfl⟩
    change Equiv.Perm.sign (g * q * g⁻¹) = 1
    simp only [map_mul, map_inv, show Equiv.Perm.sign q = 1 from hQ hq,
      mul_one, mul_inv_cancel]
  have hnK : ¬ Q' ≤ K := by
    intro h
    have hd := (card_dvd_of_le h)
    rw [card_map_of_injective e.injective, card_K] at hd
    exact (by decide : ¬ 8 ∣ 12) (hc.trans hd)
  obtain ⟨t', ht', htK⟩ := SetLike.not_le_iff_exists.mp hnK
  obtain ⟨t, ht, rfl⟩ := ht'
  refine ⟨t, ht, ?_⟩
  intro x hx
  have hyK : e x ∈ K := hg ▸ mem_map_of_mem e.toMonoidHom hx
  have hs := canonical_square (e t) (hQ' (mem_map_of_mem _ ht)) htK (e x) hyK
  have hyn : e (t * x * t⁻¹ * x) ∈ K := by
    rw [map_mul, map_mul, map_mul, map_inv]
    exact K.mul_mem (le_normalizer_iff.mp hn' _ (mem_map_of_mem _ ht) _ hyK) hyK
  let y : K := ⟨e (t * x * t⁻¹ * x), hyn⟩
  have hy2 : y ^ 2 = 1 := by
    apply Subtype.ext
    simpa only [y, coe_pow, coe_one, map_mul, map_inv] using hs
  have hycore : y ∈ pCore 2 K := by
    apply (QuotientGroup.eq_one_iff (N := pCore 2 K) y).mp
    let z := QuotientGroup.mk' (pCore 2 K) y
    have hz2 : z ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    have hz3 : z ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := z)
      rwa [NaturalCubicOrder.quotient_K_card] at hh
    have : z ^ 3 = z := by rw [pow_succ, hz2, one_mul]
    exact this.symm.trans hz3
  have hmem : e (t * x * t⁻¹ * x) ∈ K.pCoreIn 2 := ⟨y, hycore, rfl⟩
  rw [← hg, ← map_pCoreIn_of_injective 2 R e.toMonoidHom e.injective] at hmem
  exact (mem_map_iff_mem e.injective).mp hmem
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryInverter
