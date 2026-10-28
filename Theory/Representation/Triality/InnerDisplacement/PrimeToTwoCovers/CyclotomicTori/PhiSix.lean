module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.Order
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.Descent
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.Lang
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.TwistedCoordinates

/-!
# Sixth-cyclotomic Sylow pairs in binary triality

A marked primary plane in the twisted split torus over GF(q⁶), together
with a Lang witness for its specified folded Weyl word, descends to a
faithful plane in the genuine carrier. Its order is the full p-primary
part of the carrier order, not merely a subgroup of the correct exponent.
The descended fourth power of the Weyl word acts by q² and 1 on the two
generators. Since p > 3 divides q² − q + 1, determinant minus one is
coprime to their primary exponent. This constructs the literal TorusPair
and applies it to arbitrary finite perfect central covers and R → R/Z(R).

The coroot-coordinate construction and the finite Lang solution supply
both descent inputs. The unconditional `exists_sylow_pair` therefore
discharges the exact hsix premise of
`CyclotomicTori.geometry_of_remaining_tori` for n > 1. The conditional
descent interfaces remain available separately.

Source: GLS3 §§2.1–2.4 and the nondefining-characteristic calculation
summarized in §6.1, Theorem 6.1.4. No multiplier table is a proof input.
-/

public section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
open PerfectCentralCovering PerfectCentralCovering.OddSylow

private theorem plane_decomposition {d : ℕ} [NeZero d] (z : Plane d) :
    z = first d ^ z.toAdd.1.val * second d ^ z.toAdd.2.val := by
  apply Multiplicative.toAdd.injective
  apply Prod.ext <;> simp [first, second, nsmul_eq_mul]

private theorem generates_range {G : Type*} [Group G] {d : ℕ} [NeZero d]
    (f : Plane d →* G) : Subgroup.closure ({f (first d), f (second d)} : Set G) = f.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | h
    · exact ⟨_, rfl⟩
    · rcases Set.mem_singleton_iff.mp h with rfl
      exact ⟨_, rfl⟩
  · rintro g ⟨z, rfl⟩
    rw [plane_decomposition z, map_mul, map_pow, map_pow]
    have hl : f (first d) ∈ Subgroup.closure ({f (first d), f (second d)} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hr : f (second d) ∈ Subgroup.closure ({f (first d), f (second d)} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hl _) (Subgroup.pow_mem _ hr _)

private theorem first_pow (d : ℕ) : first d ^ d = 1 := by
  apply Multiplicative.toAdd.injective
  apply Prod.ext <;> simp [first, nsmul_eq_mul]

private theorem card_range {G : Type*} [Group G] {d : ℕ} [NeZero d]
    (f : Plane d →* G) (hf : Function.Injective f) : Nat.card f.range = d ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  change Nat.card (ZMod d × ZMod d) = _
  rw [Nat.card_prod, Nat.card_zmod, pow_two]

/-- Conditional on the two independent geometric constructions, this is the
exact full Sylow TorusPair consumed by the cyclotomic assembly. -/
theorem exists_sylow_pair_of_descent {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n))
    (D : TwistedPlane n hn (p ^ (modulus (2 ^ n)).factorization p))
    (x : LangWitness n hn) :
    ∃ Q : Sylow p (Standard.BinaryCarrier n hn),
      Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))) := by
  let d := p ^ (modulus (2 ^ n)).factorization p
  let : NeZero d := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let f := D.carrierEmbedding x
  let Q := sylowOfCard hn hp hd f.range (card_range f (D.carrierEmbedding_injective x))
  refine ⟨Q, ⟨{
    left := f (first d)
    right := f (second d)
    actor := TwistedPlane.carrierActor x
    generates := generates_range f
    commute := (Commute.all _ _).map f
    exponent := d
    leftPower := (2 ^ n) ^ 2
    rightPower := 1
    positive := by positivity
    coprime := by simpa only [mul_one] using
      primary_coprime (one_le_pow₀ (by decide)) hp hd ((modulus (2 ^ n)).factorization p)
    pow_eq_one := by rw [← map_pow, first_pow, map_one]
    conjugate_left := D.carrier_conjugate_first x
    conjugate_right := by simpa only [pow_one] using D.carrier_conjugate_second x
  }⟩⟩

/-- Actual local geometry obtained from the twisted plane and finite Lang solution. -/
theorem geometry_of_descent {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n))
    (D : TwistedPlane n hn (p ^ (modulus (2 ^ n)).factorization p))
    (x : LangWitness n hn) : Geometry p (Standard.BinaryCarrier n hn) := by
  obtain ⟨Q, ⟨pair⟩⟩ := exists_sylow_pair_of_descent hn hp hd D x
  exact .torus Q pair

/-- The resulting finite perfect-central-cover application has no extra
cover-specific hypothesis. Only the two base-group constructions remain. -/
theorem not_dvd_card_kernel_of_descent {E : Type*} [Group E] [Finite E]
    {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n))
    (D : TwistedPlane n hn (p ^ (modulus (2 ^ n)).factorization p))
    (x : LangWitness n hn) (f : Cover E (Standard.BinaryCarrier n hn)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  (geometry_of_descent hn hp hd D x).not_dvd_card_kernel (by omega) f

/-- Application to the literal central projection of the source perfect group. -/
theorem not_dvd_card_center_of_descent {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] {n p : ℕ} (hn : 0 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ modulus (2 ^ n))
    (D : TwistedPlane n hn (p ^ (modulus (2 ^ n)).factorization p))
    (x : LangWitness n hn)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R)) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel_of_descent hn hp hd D x (centralQuotientCover e)

/-- The full sixth-cyclotomic Sylow pair in the genuine binary triality carrier.
This supplies the exact hsix premise of `geometry_of_remaining_tori`, with
both the twisted torus and its finite Lang conjugator constructed internally. -/
theorem exists_sylow_pair {n p : ℕ} (hn : 0 < n) (hlarge : 1 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) :
    ∃ Q : Sylow p (Standard.BinaryCarrier n hn),
      Nonempty (TorusPair (Q : Subgroup (Standard.BinaryCarrier n hn))) := by
  obtain ⟨D⟩ := twistedPlane_nonempty n hn hlarge p hp hd
  obtain ⟨x⟩ := langWitness_nonempty n hn hlarge
  exact exists_sylow_pair_of_descent hn hp hd D x

/-- Sixth-cyclotomic primes have the local geometry required for central transfer. -/
theorem geometry {n p : ℕ} (hn : 0 < n) (hlarge : 1 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1) :
    Geometry p (Standard.BinaryCarrier n hn) := by
  obtain ⟨Q, ⟨pair⟩⟩ := exists_sylow_pair hn hlarge hp hd
  exact .torus Q pair

/-- No sixth-cyclotomic prime greater than three divides the kernel of a
finite perfect central cover of the actual binary triality group. -/
theorem not_dvd_card_kernel {E : Type*} [Group E] [Finite E]
    {n p : ℕ} (hn : 0 < n) (hlarge : 1 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (f : Cover E (Standard.BinaryCarrier n hn)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  (geometry hn hlarge hp hd).not_dvd_card_kernel (by omega) f

/-- The same prime exclusion for the literal projection R → R/Z(R), using
the source model isomorphism and no additional geometric premises. -/
theorem not_dvd_card_center {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] {n p : ℕ} (hn : 0 < n) (hlarge : 1 < n) [Fact p.Prime]
    (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R)) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel hn hlarge hp hd (centralQuotientCover e)

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
