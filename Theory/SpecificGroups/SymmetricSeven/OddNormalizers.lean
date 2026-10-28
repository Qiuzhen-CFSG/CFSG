module
public import Theory.SpecificGroups.SymmetricSeven.EightNormalizers
public import Theory.ElementaryAbelian.Injective

/-!
# Odd two-subgroup normalizers in S₇

Every two-subgroup containing an element of order four is covered by the
unique-square normalizer bound. An elementary eight is covered by the two
Sylow representatives. A remaining subgroup has order two or four; either
it has order two itself or its even kernel does. The normalizer fixes that
unique involution, whose centralizer has order 48 or 240.

The oddness hypothesis excludes the regular even four-group, whose
normalizer has three-rank two. Source application: Aschbacher–Smith C.2.7
and original15.3.21, printed pp.145–147 and1127.
-/

@[expose] public section
open Subgroup Equiv
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
namespace Theory.SpecificGroups.SymmetricSeven.OddNormalizers

private theorem rank_three_le_one_of_card {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 48 ∨ Nat.card H = 240) : primeRank 3 H ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd := E.card_subgroup_dvd_card
  rcases hc with hc | hc
  · have hd : Nat.card E ∣ 3 * 16 := by simpa only [hc] using hd
    have hp : Nat.Coprime (Nat.card E) 16 := by
      rw [hn]; exact (by decide : Nat.Coprime 3 16).pow_left n
    exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)
  · have hd : Nat.card E ∣ 3 * 80 := by simpa only [hc] using hd
    have hp : Nat.Coprime (Nat.card E) 80 := by
      rw [hn]; exact (by decide : Nat.Coprime 3 80).pow_left n
    exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

private theorem involution_centralizer_rank (z : S7) (hz : z ^ 2 = 1) (hne : z ≠ 1) :
    primeRank 3 (centralizer ({z} : Set S7)) ≤ 1 := by
  have ht := Perm.cycleType_of_pow_prime_eq_one hz
  have hs := z.support.card_le_univ
  have hs' := z.sum_cycleType
  rw [ht,Multiset.sum_replicate] at hs'
  have hp : 0 < z.cycleType.card := by
    apply Nat.pos_of_ne_zero
    intro h
    have he : z.cycleType = 0 := Multiset.card_eq_zero.mp h
    exact hne (Perm.cycleType_eq_zero.mp he)
  have hb : z.cycleType.card ≤ 3 := by
    simp only [Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs hs'
    omega
  have hcases : z.cycleType.card = 1 ∨ z.cycleType.card = 2 ∨ z.cycleType.card = 3 := by omega
  apply rank_three_le_one_of_card
  rw [Perm.nat_card_centralizer,ht]
  rcases hcases with h | h | h <;> rw [h] <;> norm_num [Nat.factorial]

private theorem normalized_two (N A : Subgroup S7) (hn : N ≤ normalizer (A : Set S7))
    (hc : Nat.card A = 2) (hA : IsElementaryAbelian 2 A) : primeRank 3 N ≤ 1 := by
  let := hA
  obtain ⟨z,hz,hu⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hc
  have hzne : (z : S7) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hNC : N ≤ centralizer ({(z : S7)} : Set S7) := by
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    let w : A := ⟨g * (z : S7) * g⁻¹,(mem_normalizer_iff.mp (hn hg) z).mp z.property⟩
    have hw : w ≠ 1 := by
      intro hw
      apply hzne
      apply (MulAut.conj g).injective
      change g * (z : S7) * g⁻¹ = (MulAut.conj g) 1
      rw [map_one]
      exact congrArg Subtype.val hw
    exact congrArg Subtype.val (hu w hw)
  exact (primeRank_mono 3 hNC).trans (involution_centralizer_rank z
    (elemPow_eq_one_of_isElementaryAbelian _ z.property) hzne)

private theorem elementary_of_square (E : Subgroup S7)
    (h : ∀ x ∈ E, x ^ 2 = 1) : IsElementaryAbelian 2 E := by
  have hi (x : E) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change (x : S7) * (x : S7) = 1
    simpa only [pow_two] using h x x.property
  exact {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x*y = (x*y)⁻¹ := (hi _).symm
           _ = y⁻¹*x⁻¹ := mul_inv_rev _ _
           _ = y*x := by rw [hi,hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Subtype.ext (h x x.property)) }

/-- A two-subgroup of S7 containing an odd permutation has three-rank at most one
in its normalizer. The regular even four-group is deliberately excluded. -/
theorem normalizer_rank (A : Subgroup S7) (hA : IsPGroup 2 A)
    (hodd : ¬ A ≤ alternatingGroup (Fin 7)) :
    primeRank 3 (normalizer (A : Set S7)) ≤ 1 := by
  by_cases hx : ∃ x ∈ A, x ^ 2 ≠ 1
  · exact EightNormalizers.noninvolution_normalizer_rank A hA hx
  have he : IsElementaryAbelian 2 A := elementary_of_square A (by intro x hxA; by_contra hn; exact hx ⟨x,hxA,hn⟩)
  let := he
  have hbound := elementary_card_le he
  by_cases h8 : Nat.card A = 8
  · exact EightNormalizers.elementary_normalizer_rank A he h8
  have hne : A ≠ ⊥ := fun h => hodd (h ▸ bot_le)
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  have hp : 0 < n := by
    by_contra hh
    have : Nat.card A = 1 := by rw [hn,show n=0 by omega,pow_zero]
    exact hne (Subgroup.card_eq_one.mp this)
  have hnle : n ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [hn] using hbound
  have hcases : Nat.card A = 2 ∨ Nat.card A = 4 := by
    have : n=1 ∨ n=2 := by
      have hn3 : n ≠ 3 := fun hh => h8 (by rw [hn,hh]; decide)
      omega
    rcases this with rfl | rfl <;> norm_num [hn]
  rcases hcases with h2 | h4
  · exact normalized_two _ A le_rfl h2 he
  let f : A →* ℤˣ := Perm.sign.comp A.subtype
  have hf : Function.Surjective f := by
    obtain ⟨a,ha,hna⟩ : ∃ a ∈ A, a ∉ alternatingGroup (Fin 7) := by
      simpa only [SetLike.le_def,not_forall,exists_prop] using hodd
    have hsign : Perm.sign a = -1 := (Int.units_eq_one_or _).resolve_left hna
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1,map_one f⟩
    · exact ⟨⟨a,ha⟩,hsign⟩
  have hi : f.ker.index = 2 := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hf,
      Nat.card_congr (Subgroup.topEquiv (G := ℤˣ)).toEquiv,Nat.card_eq_fintype_card]
    decide
  have hc := f.ker.card_mul_index
  rw [hi,h4] at hc
  let B := A ⊓ alternatingGroup (Fin 7)
  let e : B ≃ f.ker := {
    toFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
    invFun x := ⟨x.val.val,x.val.property,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hB : Nat.card B = 2 := by rw [Nat.card_congr e]; omega
  have hBN : normalizer (A : Set S7) ≤ normalizer (B : Set S7) :=
    (le_inf le_rfl le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  exact normalized_two _ B hBN hB (IsElementaryAbelian.of_injective
    (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _))
end Theory.SpecificGroups.SymmetricSeven.OddNormalizers
