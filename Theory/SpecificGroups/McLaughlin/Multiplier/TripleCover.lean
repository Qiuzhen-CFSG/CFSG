module

public import Theory.SpecificGroups.McLaughlin.Multiplier.Basic
public import Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover.LiftRelations
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Constructing a perfect McLaughlin triple cover from marked word identities

The group is the image of the paired word map into the degree-275 permutation
carrier and a finite matrix-unit group. Its projection is surjective. A complete
presentation of the base bounds its kernel by the cyclic scalar subgroup;
the eleventh-power product word supplies every scalar in that subgroup.
The generator relations of exponents 2, 5 and 33 kill the abelianization,
so this paired group is perfect. Its literal kernel is isomorphic to C3.

This module proves the construction conditional on two independent inputs:
`base.ker = normalClosure relators` and the finite matrix identities
`LiftRelations A B`. Neither input is asserted to be proved for the candidate
ATLAS matrices. A concrete finite triple cover remains to be assembled after
those certifications. The comparison with the Leech triangle stabilizer is
retained explicitly, as permitted by the independent model-comparison task.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (the multiplier lower bound).
The candidate matrices and presentation are the ATLAS files
`3McLG1-f25r45aB0` and `McLG1-P1.M`; see `TripleCover/source/README.md`.
This construction does not use universality or an assumed multiplier value.
-/

public section

open PerfectCentralCovering

namespace Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover

variable {H : Type*} [Group H]

/-- Evaluate each word simultaneously on the base and the proposed lifts. -/
@[expose] def wordPair (A B : H) : Word →* Sporadic.LeechRelated.McL.Carrier × H :=
  base.prod (evaluate A B)

/-- The actual generated subgroup of permutation/matrix pairs. If the ambient
group `H` is finite, its inherited `Group` and `Finite` instances apply. -/
abbrev PairedGroup (A B : H) := (wordPair A B).range

/-- The surjective word map onto the paired subgroup. -/
@[expose] def liftWord (A B : H) : Word →* PairedGroup A B := (wordPair A B).rangeRestrict

/-- Projection to the original permutation-generated carrier. -/
@[expose] def projection (A B : H) : PairedGroup A B →* Sporadic.LeechRelated.McL.Carrier :=
  (MonoidHom.fst _ _).comp (wordPair A B).range.subtype

/-- Surjectivity uses the defining generators of the literal base carrier. -/
theorem projection_surjective (A B : H) : Function.Surjective (projection A B) := by
  intro x
  obtain ⟨w, rfl⟩ := base_surjective x
  exact ⟨liftWord A B w, rfl⟩

private theorem base_relation
    (hp : base.ker = Subgroup.normalClosure relators) {w : Word} (hw : w ∈ relators) :
    base w = 1 := by
  exact show w ∈ base.ker from hp ▸ Subgroup.subset_normalClosure hw

private theorem abelian_pair_trivial {C : Type*} [CommGroup C] (x y : C)
    (hx : x ^ 2 = 1) (hy : y ^ 5 = 1) (hxy : (x * y) ^ 33 = 1) :
    x = 1 ∧ y = 1 := by
  have h10 : (x * y) ^ 10 = 1 := by
    rw [mul_pow]
    calc
      x ^ 10 * y ^ 10 = (x ^ 2) ^ 5 * (y ^ 5) ^ 2 := by simp only [← pow_mul]
      _ = 1 := by simp [hx, hy]
  have hxy1 : x * y = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 10 33)
      (orderOf_dvd_of_pow_eq_one h10) (orderOf_dvd_of_pow_eq_one hxy))
  have hx5 : x ^ 5 = 1 := by
    rw [eq_inv_of_mul_eq_one_left hxy1, inv_pow, hy, inv_one]
  have hx1 : x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 5)
      (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_of_pow_eq_one hx5))
  exact ⟨hx1, by simpa [hx1] using hxy1⟩

/-- The exponents 2, 5 and 33 force every abelian image to be trivial. -/
theorem perfect (A B : H) (hp : base.ker = Subgroup.normalClosure relators)
    (h : LiftRelations A B) : Group.IsPerfect (PairedGroup A B) := by
  have ha : liftWord A B a ^ 2 = 1 := by
    rw [← map_pow]
    apply Subtype.ext
    apply Prod.ext
    · exact base_relation hp (show a ^ 2 ∈ relators by simp [relators, relatorList])
    · change evaluate A B (a ^ 2) = 1
      simpa only [map_pow, evaluate_a] using h.a_sq
  have hb : liftWord A B b ^ 5 = 1 := by
    rw [← map_pow]
    apply Subtype.ext
    apply Prod.ext
    · exact base_relation hp (show b ^ 5 ∈ relators by simp [relators, relatorList])
    · change evaluate A B (b ^ 5) = 1
      simpa only [map_pow, evaluate_b] using h.b_fifth
  have hab : (liftWord A B a * liftWord A B b) ^ 33 = 1 := by
    rw [← map_mul, ← map_pow]
    apply Subtype.ext
    apply Prod.ext
    · have h11 : base ((a * b) ^ 11) = 1 :=
        base_relation hp (show (a * b) ^ 11 ∈ relators by simp [relators, relatorList])
      change base ((a * b) ^ 33) = 1
      calc
        base ((a * b) ^ 33) = base ((a * b) ^ 11) ^ 3 := by rw [← map_pow, ← pow_mul]
        _ = 1 := by rw [h11, one_pow]
    · change evaluate A B ((a * b) ^ 33) = 1
      simpa only [map_pow, map_mul, evaluate_a, evaluate_b] using h.ab_pow
  obtain ⟨ha1, hb1⟩ := abelian_pair_trivial
    (Abelianization.of (liftWord A B a)) (Abelianization.of (liftWord A B b))
    (by simpa only [map_pow, map_one] using congrArg Abelianization.of ha)
    (by simpa only [map_pow, map_mul, map_one] using congrArg Abelianization.of hb)
    (by simpa only [map_pow, map_mul, map_one] using congrArg Abelianization.of hab)
  have hkill : Abelianization.of.comp (liftWord A B) = 1 := by
    apply FreeGroup.ext_hom
    intro i
    cases i
    · exact ha1
    · exact hb1
  constructor
  apply (Subgroup.eq_top_iff' _).mpr
  intro x
  obtain ⟨w, rfl⟩ := (wordPair A B).rangeRestrict_surjective x
  rw [← Abelianization.ker_of]
  exact DFunLike.congr_fun hkill w

private theorem kernel_coordinate (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B)
    {x : PairedGroup A B} (hx : projection A B x = 1) : x.val.2 ∈ Subgroup.zpowers (scalar A B) := by
  have hcentral : Subgroup.zpowers (scalar A B) ≤ Subgroup.center H :=
    Subgroup.zpowers_le.mpr h.scalar_central
  let : (Subgroup.zpowers (scalar A B)).Normal := ⟨by
    intro g hg k
    rw [Subgroup.mem_center_iff.mp (hcentral hg) k, mul_inv_cancel_right]
    exact hg⟩
  have hle : base.ker ≤ (Subgroup.zpowers (scalar A B)).comap (evaluate A B) := by
    rw [hp]
    exact Subgroup.normalClosure_le_normal h.relators_cyclic
  obtain ⟨w, hw⟩ := x.property
  have hwbase : base w = 1 := (congrArg Prod.fst hw).trans hx
  have hwH : evaluate A B w = x.val.2 := congrArg Prod.snd hw
  exact hwH ▸ hle hwbase

/-- Completeness of the marked presentation makes every kernel coordinate central. -/
theorem kernel_le_center (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B) :
    (projection A B).ker ≤ Subgroup.center (PairedGroup A B) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply Prod.ext
  · change y.val.1 * x.val.1 = x.val.1 * y.val.1
    have hx1 : x.val.1 = 1 := hx
    simp [hx1]
  · exact Subgroup.mem_center_iff.mp
      ((Subgroup.zpowers_le.mpr h.scalar_central) (kernel_coordinate A B hp h hx)) y.val.2

/-- The second coordinate identifies the whole kernel with the scalar subgroup. -/
noncomputable def kernelEquiv (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B) :
    (projection A B).ker ≃* Subgroup.zpowers (scalar A B) := by
  let k : (projection A B).ker →* Subgroup.zpowers (scalar A B) :=
    { toFun := fun x => ⟨x.val.val.2, kernel_coordinate A B hp h x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  apply MulEquiv.ofBijective k
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show x.val.val.1 = 1 from x.property).trans
        (show y.val.val.1 = 1 from y.property).symm
    · exact congrArg Subtype.val hxy
  · intro z
    obtain ⟨n, hn⟩ := z.property
    have hw : base ((a * b) ^ 11) = 1 :=
      base_relation hp (by simp [relators, relatorList])
    let x : (projection A B).ker := ⟨liftWord A B (((a * b) ^ 11) ^ n), by
      change base (((a * b) ^ 11) ^ n) = 1
      rw [map_zpow, hw, one_zpow]⟩
    refine ⟨x, Subtype.ext ?_⟩
    change evaluate A B (((a * b) ^ 11) ^ n) = z.val
    simpa [scalar] using hn

/-- The distinguished scalar has order exactly three. -/
theorem scalar_order (A B : H) (h : LiftRelations A B) : orderOf (scalar A B) = 3 := by
  apply orderOf_eq_prime _ h.scalar_ne_one
  simpa only [scalar, ← pow_mul] using h.ab_pow

/-- The kernel has order exactly three, with the presentation premise explicit. -/
theorem kernel_card (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B) :
    Nat.card (projection A B).ker = 3 := by
  rw [Nat.card_congr (kernelEquiv A B hp h).toEquiv, Nat.card_zpowers, scalar_order A B h]

/-- The constructed perfect central cover, with its precise Leech-model codomain. -/
@[expose] def cover (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B)
    (comparison : Sporadic.LeechRelated.McL.Carrier ≃* Atlas.Sporadic.McLaughlin.Model) :
    Cover (PairedGroup A B) Atlas.Sporadic.McLaughlin.Model where
  toMonoidHom := comparison.toMonoidHom.comp (projection A B)
  surjective := comparison.surjective.comp (projection_surjective A B)
  isPerfect := perfect A B hp h
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ comparison.injective]
    exact kernel_le_center A B hp h

/-- Model transport preserves the literal order-three kernel. -/
theorem cover_kernel_card (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B)
    (comparison : Sporadic.LeechRelated.McL.Carrier ≃* Atlas.Sporadic.McLaughlin.Model) :
    Nat.card (cover A B hp h comparison).toMonoidHom.ker = 3 := by
  change Nat.card (comparison.toMonoidHom.comp (projection A B)).ker = 3
  rw [MonoidHom.ker_comp_of_injective _ _ comparison.injective]
  exact kernel_card A B hp h

/-- The actual transported kernel is cyclic of order three as a group. -/
noncomputable def coverKernelEquiv (A B : H)
    (hp : base.ker = Subgroup.normalClosure relators) (h : LiftRelations A B)
    (comparison : Sporadic.LeechRelated.McL.Carrier ≃* Atlas.Sporadic.McLaughlin.Model) :
    (cover A B hp h comparison).toMonoidHom.ker ≃* Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (cover_kernel_card A B hp h comparison) (by simp)

end Theory.SpecificGroups.McLaughlin.Multiplier.TripleCover
