module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.Data
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.Lang
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree.SplitTorus
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedDescent

/-!
# Descent and Sylow placement for the third cyclotomic torus

Conjugating a twisted primary plane by a solution of σ(x) = xw gives a
faithful plane in the genuine graph-field fixed group. The same conjugation
carries w to an actual ambient element acting by powers q² and 1. The
proved carrier order places the full plane in a Sylow subgroup, and
coprimality of q²−1 with its exponent annihilates the lifted alternating
pairing in every central extension.

The split-coroot construction supplies `TwistedPlane`, and the concrete Spin
Lang theorem with finite-field descent supplies the Lang equation for the
specified word. Combining them proves the third-cyclotomic branch for every
n > 1, including repeated prime powers. `exists_sylow_pair` discharges the
exact `hthree` premise of the remaining-tori assembly, and the final theorems
apply it to perfect central covers and the literal map R → R/Z(R). Neither
a multiplier table nor an auxiliary group model is used.

Source: GLS3 §2.2 (graph-field and quotient conventions) and §6.1
(Theorem 6.1.4). This is the general-parameter form of the concrete descent
used in `CyclotomicTori.SevenAtTwo`.
-/

public section
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
open Triality.Standard Triality.Standard.ConcreteBruhat.FixedDescent
open PerfectCentralCovering PerfectCentralCovering.OddSylow
noncomputable section

private theorem plane_generated (n p : ℕ) (z : Plane n p) :
    z = leftVector n p ^ z.toAdd.1.val * rightVector n p ^ z.toAdd.2.val := by
  apply Multiplicative.toAdd.injective
  ext <;> simp [leftVector, rightVector]

private theorem plane_generates {G : Type*} [Group G] (n p : ℕ) (f : Plane n p →* G) :
    Subgroup.closure ({f (leftVector n p), f (rightVector n p)} : Set G) = f.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | h
    · exact ⟨_, rfl⟩
    · rcases Set.mem_singleton_iff.mp h with rfl
      exact ⟨_, rfl⟩
  · rintro g ⟨z, rfl⟩
    rw [plane_generated n p z, map_mul, map_pow, map_pow]
    have hl : f (leftVector n p) ∈
        Subgroup.closure ({f (leftVector n p), f (rightVector n p)} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hr : f (rightVector n p) ∈
        Subgroup.closure ({f (leftVector n p), f (rightVector n p)} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hl _) (Subgroup.pow_mem _ hr _)

/-- A faithful primary plane with the specified ambient action is the full
Sylow subgroup and supplies the exact torus-pair consumer. -/
theorem exists_sylow_pair_of_embedding (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1)
    (f : Plane n p →* BinaryCarrier n hn) (hf : Function.Injective f)
    (s : BinaryCarrier n hn)
    (hsleft : s * f (leftVector n p) * s⁻¹ = f (leftVector n p) ^ (2 ^ n) ^ 2)
    (hsright : s * f (rightVector n p) * s⁻¹ = f (rightVector n p)) :
    ∃ Q : Sylow p (BinaryCarrier n hn),
      Nonempty (TorusPair (Q : Subgroup (BinaryCarrier n hn))) := by
  have hcard : Nat.card f.range = p ^ (Nat.card (BinaryCarrier n hn)).factorization p := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    change Nat.card (ZMod (primaryOrder n p) × ZMod (primaryOrder n p)) = _
    rw [Nat.card_prod, Nat.card_zmod, ← pow_two]
    exact primaryOrder_sq n hn hp hthree
  let Q := Sylow.ofCard f.range hcard
  refine ⟨Q, ⟨{
    left := f (leftVector n p)
    right := f (rightVector n p)
    actor := s
    generates := plane_generates n p f
    commute := (Commute.all _ _).map f
    exponent := primaryOrder n p
    leftPower := (2 ^ n) ^ 2
    rightPower := 1
    positive := by positivity
    coprime := by simpa only [mul_one] using primaryOrder_coprime hp hthree
    pow_eq_one := ?_
    conjugate_left := hsleft
    conjugate_right := by simpa only [pow_one] using hsright
  }⟩⟩
  rw [← map_pow]
  have h : leftVector n p ^ primaryOrder n p = 1 := by
    apply Multiplicative.toAdd.injective
    ext <;> simp [leftVector]
  rw [h, map_one]

variable {n : ℕ} {hn : 0 < n} {p : ℕ}

/-- The exact orientation of the Lang identity turns twisted fixedness into
membership in the genuine fixed subgroup. -/
theorem conjugate_mem_fixed (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn)
    (y : SplitGroup (binaryParameters n hn))
    (hy : twistWord n hn * graphFieldAutomorphism (binaryParameters n hn) y =
      y * twistWord n hn) :
    x * y * x⁻¹ ∈ fixedSubgroup (binaryParameters n hn) := by
  change graphFieldAutomorphism (binaryParameters n hn) (x * y * x⁻¹) = x * y * x⁻¹
  calc
    _ = x * (twistWord n hn * graphFieldAutomorphism (binaryParameters n hn) y) *
        (twistWord n hn)⁻¹ * x⁻¹ := by
      simp only [map_mul, map_inv, hx]
      group
    _ = _ := by rw [hy]; group

private def fixedEmbedding (d : TwistedPlane n hn p)
    (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    Plane n p →* fixedSubgroup (binaryParameters n hn) :=
  (((MulAut.conj x).toMonoidHom).comp d.embedding).codRestrict
    (fixedSubgroup (binaryParameters n hn))
    (fun z => conjugate_mem_fixed x hx _ (d.twisted_fixed z))

private def fixedActor (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    fixedSubgroup (binaryParameters n hn) :=
  ⟨x * twistWord n hn * x⁻¹,
    conjugate_mem_fixed x hx _ (by rw [graphField_twistWord])⟩

private def embedding (d : TwistedPlane n hn p)
    (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    Plane n p →* BinaryCarrier n hn :=
  (carrierFixedEquiv (binaryParameters n hn) rfl).symm.toMonoidHom.comp (fixedEmbedding d x hx)

private theorem embedding_injective (d : TwistedPlane n hn p)
    (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    Function.Injective (embedding d x hx) := by
  apply (carrierFixedEquiv (binaryParameters n hn) rfl).symm.injective.comp
  intro a b h
  exact d.injective ((MulAut.conj x).injective (congrArg Subtype.val h))

private def actor (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    BinaryCarrier n hn := (carrierFixedEquiv (binaryParameters n hn) rfl).symm (fixedActor x hx)

private theorem conjugates (d : TwistedPlane n hn p)
    (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn)
    (z : Plane n p) (k : ℕ)
    (h : twistWord n hn * d.embedding z * (twistWord n hn)⁻¹ = d.embedding z ^ k) :
    actor x hx * embedding d x hx z * (actor x hx)⁻¹ = embedding d x hx z ^ k := by
  have hf : fixedActor x hx * fixedEmbedding d x hx z * (fixedActor x hx)⁻¹ =
      fixedEmbedding d x hx z ^ k := by
    apply Subtype.ext
    change (MulAut.conj x) (twistWord n hn) *
      (MulAut.conj x) (d.embedding z) * ((MulAut.conj x) (twistWord n hn))⁻¹ =
      (MulAut.conj x) (d.embedding z) ^ k
    simpa only [map_mul, map_inv, map_pow] using congrArg (MulAut.conj x) h
  simpa only [actor, embedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv, map_pow] using congrArg (carrierFixedEquiv (binaryParameters n hn) rfl).symm hf

/-- Conditional assembly of the literal `hthree` premise. Both geometric
inputs must be constructed before claiming the source branch. -/
theorem exists_sylow_pair_of_twistedPlane [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) (d : TwistedPlane n hn p)
    (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    ∃ Q : Sylow p (BinaryCarrier n hn),
      Nonempty (TorusPair (Q : Subgroup (BinaryCarrier n hn))) :=
  exists_sylow_pair_of_embedding n hn hp hthree (embedding d x hx)
    (embedding_injective d x hx) (actor x hx)
    (conjugates d x hx _ _ d.conjugate_left)
    (by
      simpa only [pow_one] using conjugates d x hx (rightVector n p) 1
        (by simpa only [pow_one] using d.conjugate_right))

/-- Application to the local-geometry interface, retaining the two inputs. -/
theorem geometry_of_twistedPlane [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) (d : TwistedPlane n hn p)
    (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    Geometry p (BinaryCarrier n hn) := by
  obtain ⟨Q, ⟨t⟩⟩ := exists_sylow_pair_of_twistedPlane hp hthree d x hx
  exact .torus Q t

/-- The same descended plane excludes p from every finite perfect central kernel. -/
theorem not_dvd_card_kernel_of_twistedPlane {E : Type*} [Group E] [Finite E]
    [Fact p.Prime] (hp : 3 < p) (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1)
    (d : TwistedPlane n hn p) (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn)
    (f : Cover E (BinaryCarrier n hn)) : ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  (geometry_of_twistedPlane hp hthree d x hx).not_dvd_card_kernel (by omega) f

/-- Consumer on the literal map R → R/Z(R), using the genuine carrier equivalence. -/
theorem not_dvd_card_center_of_twistedPlane {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] [Fact p.Prime]
    (hmodel : IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    (hp : 3 < p) (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1)
    (d : TwistedPlane n hn p) (x : SplitGroup (binaryParameters n hn))
    (hx : graphFieldAutomorphism (binaryParameters n hn) x = x * twistWord n hn) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel_of_twistedPlane hp hthree d x hx (centralQuotientCover e)

/-- The full third-cyclotomic Sylow torus pair in the genuine binary carrier.
This supplies `hthree` in `CyclotomicTori.geometry_of_remaining_tori`, with
both the split plane and its Lang conjugator constructed. -/
theorem exists_sylow_pair (n : ℕ) (hn : 0 < n) (hlarge : 1 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    ∃ Q : Sylow p (BinaryCarrier n hn),
      Nonempty (TorusPair (Q : Subgroup (BinaryCarrier n hn))) := by
  obtain ⟨d⟩ := exists_twistedPlane n hn hlarge p hp hthree
  obtain ⟨x, hx⟩ := exists_langWitness n hn hlarge
  exact exists_sylow_pair_of_twistedPlane hp hthree d x hx

/-- Third-cyclotomic primes have the local geometry needed for central covers. -/
theorem geometry (n : ℕ) (hn : 0 < n) (hlarge : 1 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    Geometry p (BinaryCarrier n hn) := by
  obtain ⟨Q, ⟨t⟩⟩ := exists_sylow_pair n hn hlarge hp hthree
  exact .torus Q t

/-- No third-cyclotomic prime greater than three divides the kernel of a
finite perfect central cover of the genuine binary triality carrier. -/
theorem not_dvd_card_kernel {E : Type*} [Group E] [Finite E]
    (n : ℕ) (hn : 0 < n) (hlarge : 1 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1)
    (f : Cover E (BinaryCarrier n hn)) : ¬ p ∣ Nat.card f.toMonoidHom.ker :=
  (geometry n hn hlarge hp hthree).not_dvd_card_kernel (by omega) f

/-- The third-cyclotomic exclusion on the literal central projection R → R/Z(R),
transported through the given isomorphism with the genuine triality model. -/
theorem not_dvd_card_center {R : Type*} [Group R] [Finite R] [Group.IsPerfect R]
    (n : ℕ) (hn : 0 < n) (hlarge : 1 < n)
    (hmodel : IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hthree : p ∣ (2 ^ n) ^ 2 + 2 ^ n + 1) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel n hn hlarge hp hthree (centralQuotientCover e)

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
