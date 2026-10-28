module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.PrimeFixedIndex

/-!
# The fixed layer in a small faithful Suzuki action

Let a Suzuki group with parameter q act faithfully on a two-group W of
order q⁵, with a fixed subgroup Z of order q. Any proper invariant
subgroup containing Z equals Z. A primitive-prime actor would otherwise
force an index of q⁴ inside that proper subgroup. The actor consequently
fixes it, and the same index bound on W limits its order to q.

ThirdCommutator applies this to the actual derived radical and its third
commutator. The argument includes q=2 via the prime five.
Source: Fong--Seitz I (1973), proof of (6H)(g), printed p.55.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource

/-- A q-sized fixed subgroup contains every proper invariant subgroup above
it in a faithful Suzuki two-group of order q⁵. -/
theorem suzuki_proper_invariant_eq_fixed_layer {W : Type*} [Group W] [Finite W]
    (hW : IsPGroup 2 W) (m : ℕ)
    (f : SuzukiMatrixGroup m →* MulAut W) (hf : Function.Injective f)
    (Z K : Subgroup W) (hZK : Z ≤ K) (hKt : K ≠ ⊤)
    (hZ : ∀ g, Z ≤ (f g).fixedSubgroup)
    (hK : ∀ g, K.map (f g).toMonoidHom = K)
    (hWcard : Nat.card W = (2^(2*m+1))^5)
    (hZcard : Nat.card Z = 2^(2*m+1)) : K = Z := by
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
  let a := f g
  let b : MulAut K := (a.subgroupMap K).trans (MulEquiv.subgroupCongr (hK g))
  have hbpow (k : ℕ) (x : K) : ((b^k) x : W) = (a^k) (x : W) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',pow_succ',MulAut.mul_apply,MulAut.mul_apply]
      change a ((b^k) x : W) = a ((a^k) (x : W))
      rw [ih]
  have hap : a^p = 1 := by rw [←map_pow,←hg,pow_orderOf_eq_one,map_one]
  have hbp : b^p = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hbpow,hap]
    rfl
  have hZb : Z.subgroupOf K ≤ b.fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply Subtype.ext
    exact (MulAut.mem_fixedSubgroup _ _).mp (hZ g hx)
  have hZbcard : 2^(2*m+1) ≤ Nat.card b.fixedSubgroup := by
    rw [←hZcard,←Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv]
    exact Nat.card_le_card_of_injective (inclusion hZb) (inclusion_injective _)
  have hb : b = 1 := by
    by_contra hne
    have hi := prime_fixed_index_ge (hW.to_subgroup K) hp hp2 b (orderOf_eq_prime hbp hne)
    have hq : (2^(2*m+1))^4 ≤ b.fixedSubgroup.index := by
      simpa only [ho,pow_mul,Nat.mul_comm 4 (2*m+1)] using hi
    have he := b.fixedSubgroup.index_mul_card
    have hge := Nat.mul_le_mul hq hZbcard
    rw [he,←pow_succ] at hge
    apply hKt
    apply eq_of_le_of_card_ge le_top
    rw [Nat.card_congr (topEquiv (G := W)).toEquiv,hWcard]
    exact hge
  have hKa : K ≤ a.fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    exact congrArg (fun t : MulAut K => (t ⟨x,hx⟩ : W)) hb
  have hi := prime_fixed_index_ge hW hp hp2 a ((orderOf_injective f hf g).trans hg)
  have hq : (2^(2*m+1))^4 ≤ a.fixedSubgroup.index := by
    simpa only [ho,pow_mul,Nat.mul_comm 4 (2*m+1)] using hi
  have he := a.fixedSubgroup.index_mul_card
  rw [hWcard] at he
  have hfixed : Nat.card a.fixedSubgroup ≤ 2^(2*m+1) := by
    have hmul : (2^(2*m+1))^4 * Nat.card a.fixedSubgroup ≤
        (2^(2*m+1))^4 * 2^(2*m+1) := by
      calc
        _ ≤ a.fixedSubgroup.index * Nat.card a.fixedSubgroup := Nat.mul_le_mul_right _ hq
        _ = (2^(2*m+1))^5 := he
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  apply Eq.symm
  apply eq_of_le_of_card_ge hZK
  rw [hZcard]
  exact (Nat.card_le_card_of_injective (inclusion hKa) (inclusion_injective _)).trans hfixed

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
