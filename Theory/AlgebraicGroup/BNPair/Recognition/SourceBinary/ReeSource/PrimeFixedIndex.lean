module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.BinaryCentralizers
public import Theory.Representation.Suzuki.BinaryDegree

/-!
# Fixed-index bounds for the source Suzuki action

Orbit counting for a prime-order automorphism of a finite two-group makes
its fixed index a power of two congruent to one modulo that prime. The
multiplicative order of two therefore bounds this index. A primitive prime
in the Suzuki order supplies an index of at least q⁴; at q=2 use five.

DerivedProduct applies this bound to the actual radical Frattini quotient,
where the perpendicular root supplies q fixed points. This completes the
order argument for Fong--Seitz I (1973), (6H)(f), printed p.55.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

/-- Orbit counting bounds the fixed index of an odd-prime automorphism. -/
theorem prime_fixed_index_ge {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : MulAut V) (ha : orderOf a = p) :
    2 ^ orderOf (2 : ZMod p) ≤ a.fixedSubgroup.index := by
  let : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup p (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ha,pow_one])
  have he : FixedPoints.subgroup (zpowers a) V = a.fixedSubgroup := by
    ext x
    exact (MulAut.mem_fixed_zpowers_iff a x).trans (MulAut.mem_fixedSubgroup a x).symm
  have hc := hA.card_modEq_card_fixedPoints V
  change Nat.card V % p = Nat.card (FixedPoints.subgroup (zpowers a) V) % p at hc
  rw [he,←a.fixedSubgroup.index_mul_card] at hc
  obtain ⟨m,hm⟩ := (hV.to_subgroup a.fixedSubgroup).exists_card_eq
  have hcop : Nat.Coprime p (Nat.card a.fixedSubgroup) := by
    rw [hm]
    exact (hp.coprime_iff_not_dvd.mpr (fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))).pow_right m
  have hi : a.fixedSubgroup.index ≡ 1 [MOD p] := by
    apply Nat.ModEq.cancel_right_of_coprime hcop
    simpa only [Nat.ModEq,one_mul] using hc
  obtain ⟨n,hn⟩ := hV.index a.fixedSubgroup
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have ht : a.fixedSubgroup = ⊤ := index_eq_one.mp (by simpa only [hn0,pow_zero] using hn)
    have ha1 : a = 1 := by
      ext x
      exact (MulAut.mem_fixedSubgroup a x).mp (ht ▸ mem_top x)
    rw [ha1,orderOf_one] at ha
    exact hp.ne_one ha.symm
  have hpow : (2 : ZMod p)^n = 1 := by
    have hz := (ZMod.natCast_eq_natCast_iff (2^n) 1 p).mpr (hn ▸ hi)
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hz
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) (orderOf_le_of_pow_eq_one hnpos hpow)

/-- Every faithful Suzuki action on a finite two-group has a prime actor
with fixed index at least q⁴; the binary group is included. -/
theorem suzuki_exists_large_fixed_index {V : Type*} [Group V] [Finite V]
    (hV : IsPGroup 2 V) (m : ℕ)
    (f : SuzukiMatrixGroup m →* MulAut V) (hf : Function.Injective f) :
    ∃ g : SuzukiMatrixGroup m, (2^(2*m+1))^4 ≤ (f g).fixedSubgroup.index := by
  have hpick : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      orderOf (2 : ZMod p) = 4*(2*m+1) ∧ p ∣ Nat.card (SuzukiMatrixGroup m) := by
    by_cases hm : m = 0
    · subst m
      refine ⟨5,by decide,by decide,?_,?_⟩
      · simpa using Representation.BinaryPrimeDegree.orderOf_two_mod_five
      · rw [suzukiZero_card]; decide
    · obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul_odd
        (n := 2*m+1) ⟨m,rfl⟩ (by omega)
      refine ⟨p,hp,?_,ho,Representation.Suzuki.prime_dvd_card_of_orderOf_two (by omega) hp ho⟩
      intro he
      subst p
      rw [show (2 : ZMod 2) = 0 by decide,orderOf_zero] at ho
      omega
  obtain ⟨p,hp,hp2,ho,hdiv⟩ := hpick
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' p hdiv
  refine ⟨g,?_⟩
  have hh := prime_fixed_index_ge hV hp hp2 (f g) ((orderOf_injective f hf g).trans hg)
  simpa only [ho,pow_mul,Nat.mul_comm 4 (2*m+1)] using hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
