module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.CarrierMap
public import Theory.GroupTheory.CosetWordCertificate
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Literal source subgroup and signed words for the M24 presentation bound

The subgroup generators are the outputs of ATLAS M24G1-max8W1, reversed
for native composition. The inverse-based source words are derived from the
seven defining positive words. In the abstract presentation, the first local
generator squares to one and the second has fourth power one; these proofs
use the original square, cube and commutator relations only.

The remaining order-bound obligations are a bound of 6072 on this actual
subgroup and a cover by 40320 cosets. Neither follows from the permutation
image or from the ATLAS subgroup label. See `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
open Subgroup.CosetWordCertificate

/-- The original two marked generators in the abstract group. -/
def generator (i : Fin 2) : UniversalGroup := PresentedGroup.of i

theorem generator_relations : Relations (generator 0) (generator 1) := by
  intro i
  change relatorValues (PresentedGroup.mk relators (FreeGroup.of 0))
    (PresentedGroup.mk relators (FreeGroup.of 1)) i = 1
  rw [← map_relatorValues]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- The inverse-based source words after reversal for native composition. -/
def signedRelatorValues {G : Type*} [Group G] (a b : G) : Fin 7 → G :=
  ![a ^ 2, b ^ 3, (b * a) ^ 23,
    (b * a * b⁻¹ * a⁻¹) ^ 12,
    ((b * a * b) * a * (b * a * b)⁻¹ * a⁻¹) ^ 5,
    (b⁻¹ * a * b⁻¹ * a * b * a) ^ 3 * (b⁻¹ * a * b * a * b * a) ^ 3,
    ((b⁻¹ * a * b * a) ^ 3 * b * a) ^ 4]

theorem signedRelatorValues_eq_reverse {G : Type*} [Group G]
    (a b : G) (i : Fin 7) :
    signedRelatorValues a b i =
      MulOpposite.unop (atlasRelatorValues (MulOpposite.op a) (MulOpposite.op b) i) := by
  fin_cases i <;> simp [signedRelatorValues, atlasRelatorValues, mul_assoc]

theorem signed_generator_relations (i : Fin 7) :
    signedRelatorValues (generator 0) (generator 1) i = 1 := by
  rw [signedRelatorValues_eq_reverse, ← rowRelatorValues_eq_atlas,
    ← relatorValues_eq_reverse]
  · exact generator_relations i
  · change MulOpposite.op (generator 0 ^ 2) = 1
    have h : generator 0 ^ 2 = 1 := generator_relations 0
    rw [h]; rfl
  · change MulOpposite.op (generator 1 ^ 3) = 1
    have h : generator 1 ^ 3 = 1 := generator_relations 1
    rw [h]; rfl

/-- Literal output of M24G1-max8W1, reversed as an entire group word. -/
def subgroupWord {G : Type*} [Group G] (a b : G) : Fin 2 → G :=
  let c := b * a
  let d := b * c
  let e := d * c
  let t := e ^ 11 * c ^ 7
  ![a, t * e ^ 3 * t⁻¹]

/-- The original row-action program, before reversing its words. -/
def rowSubgroupWord {G : Type*} [Group G] (a b : G) : Fin 2 → G :=
  let c := a * b
  let d := c * b
  let e := c * d
  let t := c ^ 7 * e ^ 11
  ![a, t⁻¹ * e ^ 3 * t]

theorem subgroupWord_eq_reverse {G : Type*} [Group G] (a b : G) (s : Fin 2) :
    subgroupWord a b s =
      MulOpposite.unop (rowSubgroupWord (MulOpposite.op a) (MulOpposite.op b) s) := by
  fin_cases s <;> simp [subgroupWord, rowSubgroupWord, mul_assoc]

theorem map_subgroupWord {G K : Type*} [Group G] [Group K] (f : G →* K)
    (a b : G) (s : Fin 2) :
    f (subgroupWord a b s) = subgroupWord (f a) (f b) s := by
  fin_cases s <;> simp [subgroupWord]

/-- Actual words in the seven-relator group, without any model recognition. -/
def boundGenerator : Fin 2 → UniversalGroup := subgroupWord (generator 0) (generator 1)

def boundSubgroup : Subgroup UniversalGroup := Subgroup.closure (Set.range boundGenerator)

theorem boundGenerator_mem (s : Fin 2) : boundGenerator s ∈ boundSubgroup :=
  Subgroup.subset_closure ⟨s, rfl⟩

theorem boundGenerator_zero_sq : boundGenerator 0 ^ 2 = 1 := generator_relations 0

theorem boundGenerator_one_pow_four : boundGenerator 1 ^ 4 = 1 := by
  let a := generator 0
  let b := generator 1
  have ha : a ^ 2 = 1 := generator_relations 0
  have hb : b ^ 3 = 1 := generator_relations 1
  have hai : a⁻¹ = a := by
    apply mul_left_cancel (a := a)
    simp [← pow_two, ha]
  have hbi : b⁻¹ = b ^ 2 := by
    apply mul_left_cancel (a := b)
    rw [mul_inv_cancel, ← pow_succ', hb]
  have hr : (b * a * b⁻¹ * a⁻¹) ^ 12 = 1 := signed_generator_relations 3
  have he : ((b * (b * a)) * (b * a)) ^ 12 = 1 := by
    have hx : b⁻¹ * (b * a * b⁻¹ * a⁻¹)⁻¹ * b = (b * (b * a)) * (b * a) := by
      simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one, hai]
      rw [hbi]
      simp only [pow_two, mul_assoc]
    rw [← hx]
    have hp := conj_pow (a := b⁻¹) (b := (b * a * b⁻¹ * a⁻¹)⁻¹) (i := 12)
    simpa only [inv_inv, inv_pow, hr, inv_one, mul_one, inv_mul_cancel] using hp
  change ((_) * (((b * (b * a)) * (b * a)) ^ 3) * (_)⁻¹) ^ 4 = 1
  rw [conj_pow, ← pow_mul]
  change _ * ((b * (b * a)) * (b * a)) ^ 12 * _ = 1
  rw [he]
  simp

/-- Concatenate a signed word a specified number of times. -/
def powerLetters (w : Word (Fin 2)) : ℕ → Word (Fin 2)
  | 0 => []
  | n + 1 => w ++ powerLetters w n

@[simp] theorem eval_powerLetters {G : Type*} [Group G] (g : Fin 2 → G)
    (w : Word (Fin 2)) (n : ℕ) : eval g (powerLetters w n) = eval g w ^ n := by
  induction n with
  | zero => simp [powerLetters]
  | succ n ih => rw [powerLetters, eval_append, ih, pow_succ']

/-- All seven source relators, in the native signed-letter convention. -/
def sourceLetters : Fin 7 → Word (Fin 2) :=
  let a : Word (Fin 2) := [(0, true)]
  let b : Word (Fin 2) := [(1, true)]
  let ai := FreeGroup.invRev a
  let bi := FreeGroup.invRev b
  ![powerLetters a 2, powerLetters b 3, powerLetters (b ++ a) 23,
    powerLetters (b ++ a ++ bi ++ ai) 12,
    powerLetters ((b ++ a ++ b) ++ a ++ FreeGroup.invRev (b ++ a ++ b) ++ ai) 5,
    powerLetters (bi ++ a ++ bi ++ a ++ b ++ a) 3 ++
      powerLetters (bi ++ a ++ b ++ a ++ b ++ a) 3,
    powerLetters (powerLetters (bi ++ a ++ b ++ a) 3 ++ b ++ a) 4]

theorem eval_sourceLetters {G : Type*} [Group G] (g : Fin 2 → G) (i : Fin 7) :
    eval g (sourceLetters i) = signedRelatorValues (g 0) (g 1) i := by
  fin_cases i <;> simp [sourceLetters, signedRelatorValues, eval_append, eval_invRev,
    eval_cons, mul_assoc]

theorem sourceLetters_eq_one (i : Fin 7) : eval generator (sourceLetters i) = 1 := by
  rw [eval_sourceLetters, signed_generator_relations]

/-- Signed letters of the literal reversed subgroup program. -/
def boundLetters (s : Fin 2) : Word (Fin 2) :=
  let a : Word (Fin 2) := [(0, true)]
  let b : Word (Fin 2) := [(1, true)]
  let c := b ++ a
  let d := b ++ c
  let e := d ++ c
  let t := powerLetters e 11 ++ powerLetters c 7
  if s = 0 then a else t ++ powerLetters e 3 ++ FreeGroup.invRev t

theorem eval_boundLetters {G : Type*} [Group G] (g : Fin 2 → G) (s : Fin 2) :
    eval g (boundLetters s) = subgroupWord (g 0) (g 1) s := by
  fin_cases s <;> simp [boundLetters, eval_append, eval_invRev, eval_cons,
    subgroupWord, mul_assoc]

theorem boundLetters_mem (s : Fin 2) : eval generator (boundLetters s) ∈ boundSubgroup := by
  rw [eval_boundLetters]
  exact boundGenerator_mem s

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound
