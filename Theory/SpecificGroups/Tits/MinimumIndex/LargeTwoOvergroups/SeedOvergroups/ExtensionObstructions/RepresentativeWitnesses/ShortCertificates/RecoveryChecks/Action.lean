module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.Contracts
public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.SylowFactorizations.Basic

/-!
# Seed recovery from generator transitions

A transition carries an actual seed factor. Composing transitions through the
mixed-radix normal form keeps that factor in the seed. Normal-form surjectivity
and injectivity then recover the exact numeric certificate, without any order
assumption or any assertion that the representatives are distinct cosets.
Source: Parrott (1972), section 5, p.683, and the parent source READMEs.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction

open SylowFactorizationCertificate (generator recoveryQ recovery_mem rowEquation rowMember
  rowTarget rowTest recoveryTest transitionTest transition_eq transitionT transitionG
  transitionQ transitionU)

/-- The five-bit target of a right generator transition. -/
def move (d : Nat) (j : Fin 8) (b : Fin 32) : Fin 32 :=
  ⟨(d >>> (5 * (32 * j.val + b.val))) % 32, Nat.mod_lt _ (by decide)⟩

def movePow (d : Nat) (j : Fin 8) (b : Fin 32) : Nat → Fin 32
  | 0 => b
  | k + 1 => move d j (movePow d j b k)

/-- Apply the eight literal normal-form factors, in their original order. -/
def walk (d : Nat) (b : Fin 32) (n : Fin 2048) : Fin 32 :=
  movePow d 7 (movePow d 6 (movePow d 5 (movePow d 4
    (movePow d 3 (movePow d 2 (movePow d 1 (movePow d 0 b
    (n.val % 2)) (n.val / 2 % 2)) (n.val / 4 % 4)) (n.val / 16 % 2))
    (n.val / 32 % 4)) (n.val / 128 % 2)) (n.val / 256 % 4)) (n.val / 1024 % 2)

/-- A left seed factor for one specified pair of representatives. -/
def Factors (i : Fin 122) (b a : Fin 32) (x : Atlas1600Group) : Prop :=
  ∃ q : seed i, transversal i b * x = q.val * transversal i a

/-- Soundness of the 256 entries of one generator-transition table. -/
def MoveSound (i : Fin 122) (d : Nat) : Prop :=
  ∀ (b : Fin 32) (j : Fin 8), Factors i b (move d j b) (generator j)

theorem factors_one (i : Fin 122) (b : Fin 32) : Factors i b b 1 := by
  exact ⟨1, by simp⟩

theorem factors_mul {i : Fin 122} {b a t : Fin 32} {x y : Atlas1600Group}
    (hx : Factors i b a x) (hy : Factors i a t y) : Factors i b t (x * y) := by
  obtain ⟨q, hq⟩ := hx
  obtain ⟨r, hr⟩ := hy
  refine ⟨q * r, ?_⟩
  change transversal i b * (x * y) = (q.val * r.val) * transversal i t
  rw [← mul_assoc, hq, mul_assoc, hr, ← mul_assoc]

theorem movePow_sound (i : Fin 122) (d : Nat) (h : MoveSound i d)
    (b : Fin 32) (j : Fin 8) (e : Nat) :
    Factors i b (movePow d j b e) (generator j ^ e) := by
  induction e with
  | zero => simpa only [movePow, pow_zero] using factors_one i b
  | succ e ih =>
    simpa only [movePow, pow_succ] using factors_mul ih (h (movePow d j b e) j)

theorem walk_sound (i : Fin 122) (d : Nat) (h : MoveSound i d)
    (b : Fin 32) (n : Fin 2048) :
    Factors i b (walk d b n) (atlas1600SylowTwoNormalForm n) := by
  have hp := movePow_sound i d h
  have hh := factors_mul (factors_mul (factors_mul (factors_mul (factors_mul
    (factors_mul (factors_mul (hp b 0 (n.val % 2)) (hp _ 1 (n.val / 2 % 2)))
    (hp _ 2 (n.val / 4 % 4))) (hp _ 3 (n.val / 16 % 2)))
    (hp _ 4 (n.val / 32 % 4))) (hp _ 5 (n.val / 128 % 2)))
    (hp _ 6 (n.val / 256 % 4))) (hp _ 7 (n.val / 1024 % 2))
  simpa [walk, generator, atlas1600SylowTwoNormalForm_eq] using hh

/-- Reuse the certified shared generator equations and positive recovery trees. -/
theorem moveSound_of_checks (i : Fin 122) (d r t : Nat)
    (codes : Fin 5940 → Nat)
    (hc : ∀ k, transitionTest (codes k) = true)
    (hr : ∀ k, SylowFactorizationCertificate.recoveryTest i r k = true)
    (ht : ∀ b j, rowTest codes i r t b j = true)
    (hd : ∀ b j, move d j b = rowTarget t b j) : MoveSound i d := by
  intro b j
  have hh := ht b j
  simp only [rowTest, Bool.and_eq_true, beq_iff_eq] at hh
  have he := transition_eq _ (hc (rowEquation t b j))
  rw [hh.1.1.1, hh.1.1.2, hh.1.2, hh.2] at he
  refine ⟨⟨_, recovery_mem i r hr (rowMember t b j)⟩, ?_⟩
  rw [hd]
  exact he

/-- The finite coverage check is entirely independent of membership and order. -/
def Coverage (i : Fin 122) (d : Nat) : Prop :=
  ∀ (a b : Fin 32) (c : Fin 15), witnessCase i a b c = .short →
    ∃ n : Fin 2048, inCatalogue n c = true ∧ walk d b n = a

/-- One proposed normal-form index for each pair of representatives. -/
def choice (d : Nat) (a b : Fin 32) : Fin 2048 :=
  ⟨(d >>> (11 * (32 * a.val + b.val))) % 2048, Nat.mod_lt _ (by decide)⟩

/-- Combined place/product exclusion, retaining the original selector. -/
def excluded (i : Fin 122) (c : Fin 15) : Nat :=
  (productMasks (productSelector i) ||| placeMasks (placeSelector i)) >>> (1024 * c.val)

/-- A small arithmetic check, after the seed and catalogue selectors reduce. -/
def coverageTest (d cat bad choices : Nat) (a b : Fin 32) : Bool :=
  bad.testBit (32 * a.val + b.val) ||
    ((walk d b (choice choices a b) == a) && cat.testBit (choice choices a b).val)

theorem excluded_false_of_short (i : Fin 122) (a b : Fin 32) (c : Fin 15)
    (h : witnessCase i a b c = .short) :
    (excluded i c).testBit (32 * a.val + b.val) = false := by
  have hp : (productMasks (productSelector i)).testBit (candidateIndex a b c) = false := by
    cases hp : (productMasks (productSelector i)).testBit (candidateIndex a b c)
    · rfl
    · simp [witnessCase, hp] at h
  have hl : (placeMasks (placeSelector i)).testBit (candidateIndex a b c) = false := by
    cases hl : (placeMasks (placeSelector i)).testBit (candidateIndex a b c)
    · rfl
    · simp [witnessCase, hp, hl] at h
  have he : 1024 * c.val + (32 * a.val + b.val) = candidateIndex a b c := by
    simp only [candidateIndex]
    omega
  simp only [excluded, Nat.testBit_shiftRight, he, Nat.testBit_or, hp, hl]
  rfl

/-- Consumer of each fixed seed/catalogue coverage batch. -/
theorem coverage_of_tests (i : Fin 122) (d : Nat) (choices : Fin 15 → Nat)
    (h : ∀ c a b, coverageTest d (catalogueMask c) (excluded i c) (choices c) a b = true) :
    Coverage i d := by
  intro a b c hs
  have ht := h c a b
  simp only [coverageTest, excluded_false_of_short i a b c hs, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at ht
  exact ⟨choice (choices c) a b, ht.2, ht.1⟩

/-- A certified walk recovers exactly the original left-product equation. -/
theorem recovery_of_walk (i : Fin 122) (d : Nat) (h : MoveSound i d)
    (a b : Fin 32) (c : Fin 15) (n : Fin 2048)
    (hn : inCatalogue n c = true) (hw : walk d b n = a) :
    ∃ q : Fin 2048, RecoveryCertificate i a b c q n := by
  obtain ⟨q, hq⟩ := walk_sound i d h b n
  rw [hw] at hq
  obtain ⟨k, hk⟩ := atlas1600SylowTwoNormalForm_surjective (seed_le_sylow i q.property)
  refine ⟨k, ?_, hn, ?_⟩
  · rw [hk]
    exact q.property
  · apply atlas1600SylowTwoNormalForm_injective
    rw [normalMul_sound, normalMul_sound, hk]
    exact hq.symm

theorem recoveryCertificates_of_coverage (data : Fin 122 → Nat)
    (hmove : ∀ i, MoveSound i (data i)) (hcover : ∀ i, Coverage i (data i)) :
    RecoveryCertificates := by
  intro i a b c hs
  obtain ⟨n, hn, hw⟩ := hcover i a b c hs
  obtain ⟨q, hq⟩ := recovery_of_walk i (data i) (hmove i) a b c n hn hw
  exact ⟨q, n, hq⟩

/-- Actual extension application; the independent order producer supplies ho. -/
theorem representativeWitness_of_walk (i : Fin 122) (d : Nat) (h : MoveSound i d)
    (a b : Fin 32) (c : Fin 15) (n : Fin 2048)
    (hn : inCatalogue n c = true) (hw : walk d b n = a)
    (ho : orderOf (shortElement n (shortIndex c)) = 13) :
    RepresentativeWitness i a b (shortIndex c) := by
  obtain ⟨q, hq⟩ := recovery_of_walk i d h a b c n hn hw
  exact representativeWitness_of_certificate i a b c q n hq ho

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates.RecoveryAction
