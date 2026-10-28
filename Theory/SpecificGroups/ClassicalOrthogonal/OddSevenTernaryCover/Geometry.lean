module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Residual.OmegaInvariants
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.IsometryQuotients.Standard
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.BlockMaps
public import Mathlib.Algebra.Field.ZMod

/-!
# The minus-six block in the ternary odd-seven group

The chosen anisotropic-plane parameter is one over a field of order three.
The identity x²+xy−y²−c²=(x−y)²+(y+c)(y−c) therefore identifies the
minus-six space plus a negative line with the standard odd-seven space.
Elementary block extension embeds the literal minus-six commutator group;
fixing the extra line proves injectivity after projectivization. The proved
spinor criterion places negation of the six-space in that commutator group,
giving a nontrivial involution centralizing the entire block.

Source: the Ω₇(3) branch of Aschbacher–Smith I.2.1 and A.2.17; GLS3 §2.7.
-/

open Theory.AlgebraicGroup
open ClassicalOrthogonal ClassicalOrthogonal.Minus
open ClassicalOrthogonal.Fundamental.SplitOddBlocks
@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddSevenTernaryCover
variable {F : Type} [Field F] [Finite F] [CharP F 3]

omit [CharP F 3] in
theorem parameter_eq_one (hcard : Nat.card F = 3) : parameter F = 1 := by
  let := Fintype.ofFinite F
  let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨a, ha⟩ := e.surjective (parameter F)
  fin_cases a
  · change e 0 = parameter F at ha
    have hh := parameter_spec F 0
    simp only [map_zero] at ha
    simp [← ha] at hh
  · change e 1 = parameter F at ha
    simpa only [map_one] using ha.symm
  · change e 2 = parameter F at ha
    have hh := parameter_spec F 1
    rw [map_ofNat] at ha
    norm_num [← ha] at hh

def coordinates : (Space F 2 × F) ≃ₗ[F] VectorB 3 F where
  toFun v := ((fun i => Sum.elim ![(v.1.1 0).1, (v.1.1 1).1, v.1.2.2 + v.2]
    ![(v.1.1 0).2, (v.1.1 1).2, v.1.2.2 - v.2] i), v.1.2.1 - v.1.2.2)
  invFun v := (((fun i => (v.1 (.inl i.castSucc), v.1 (.inr i.castSucc))),
    (v.2 + (v.1 (.inl 2) + v.1 (.inr 2)) / 2,
      (v.1 (.inl 2) + v.1 (.inr 2)) / 2)),
        (v.1 (.inl 2) - v.1 (.inr 2)) / 2)
  left_inv v := by
    have h2 : (2 : F) ≠ 0 := by
      intro hz
      exact (by decide : ¬ 3 ∣ 2) ((CharP.cast_eq_zero_iff F 3 2).mp hz)
    apply Prod.ext
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · apply Prod.ext <;> dsimp <;> field_simp <;> ring
    · dsimp; field_simp; ring
  right_inv v := by
    have h2 : (2 : F) ≠ 0 := by
      intro hz
      exact (by decide : ¬ 3 ∣ 2) ((CharP.cast_eq_zero_iff F 3 2).mp hz)
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> dsimp <;> try rfl
      all_goals field_simp; ring
    · dsimp; ring
  map_add' v w := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> simp <;> ring
    · simp; ring
  map_smul' c v := by
    apply Prod.ext
    · funext i
      rcases i with i | i <;> fin_cases i <;> simp <;> ring
    · simp [mul_sub]

def negativeLine : QuadraticForm F F := -QuadraticMap.sq

def spaceIsometry (hcard : Nat.card F = 3) :
    ((quadraticForm F 3).prod (negativeLine (F := F))).IsometryEquiv (formB 3 F) where
  __ := coordinates (F := F)
  map_app' v := by
    have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
    change formB 3 F (coordinates v) = (quadraticForm F 3).prod negativeLine v
    simp [coordinates, quadraticForm, form_apply, plane_apply, parameter_eq_one hcard,
      formB_apply, formD_apply, Fin.sum_univ_succ, negativeLine]
    linear_combination (v.1.2.2 ^ 2 - v.1.2.1 * v.1.2.2) * h3

open Fundamental.MinusCentralizer

abbrev MinusSix := Minus.Omega F (Space F 2) (quadraticForm F 3)

omit [Finite F] in
theorem ternary_two_ne_zero : (2 : F) ≠ 0 := by
  intro hz
  exact (by decide : ¬ 3 ∣ 2) ((CharP.cast_eq_zero_iff F 3 2).mp hz)

def block (hcard : Nat.card F = 3) : MinusSix (F := F) →* OmegaOdd 3 F :=
  (elementaryConjugate (spaceIsometry hcard)).comp
    (((elementaryProd (quadraticForm F 3) negativeLine).comp
      (MonoidHom.inl _ _)).comp
        (MulEquiv.subgroupCongr
          (complement_elementary_eq_omega (F := F) 2 (by omega) ternary_two_ne_zero).symm).toMonoidHom)

theorem block_apply (hcard : Nat.card F = 3) (g : MinusSix (F := F))
    (v : Space F 2) (c : F) :
    (block hcard g).val.val (spaceIsometry hcard (v, c)) =
      spaceIsometry hcard (g.val.val v, c) := by
  change spaceIsometry hcard
    (g.val.val ((spaceIsometry hcard).symm (spaceIsometry hcard (v,c))).1,
      ((spaceIsometry hcard).symm (spaceIsometry hcard (v,c))).2) = _
  rw [QuadraticMap.IsometryEquiv.symm_apply_apply]

def projectiveBlock (hcard : Nat.card F = 3) : MinusSix (F := F) →* POmegaOdd 3 F :=
  (projectiveElementaryMap (formB 3 F)).comp (block hcard)

theorem projectiveBlock_injective (hcard : Nat.card F = 3) :
    Function.Injective (projectiveBlock hcard) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨a, ha⟩ := (projectiveOdd_scalar_kernel (block hcard g)).mp hg
  have ht := ha (spaceIsometry hcard (0,1))
  rw [block_apply, ← map_smul] at ht
  have he := congrArg Prod.snd ((spaceIsometry hcard).injective ht)
  have ha1 : a = 1 := by simpa using he.symm
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have ht := ha (spaceIsometry hcard (v,0))
  rw [block_apply, ha1, one_smul] at ht
  exact congrArg Prod.fst ((spaceIsometry hcard).injective ht)

def negativeSix (hcard : Nat.card F = 3) : MinusSix (F := F) :=
  ⟨negativeComplement 2, (negativeComplement_mem_omega_iff 2 (by omega) ternary_two_ne_zero).mpr
    ⟨by decide, by rw [hcard]⟩⟩

theorem negativeSix_square (hcard : Nat.card F = 3) : negativeSix hcard ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change -(-v) = v
  exact neg_neg v

theorem negativeSix_ne_one (hcard : Nat.card F = 3) : negativeSix hcard ≠ 1 := by
  intro hh
  have ht := congrArg (fun g : MinusSix (F := F) => (g.val.val (0,(1,0))).2.1) hh
  change -(1 : F) = 1 at ht
  exact ternary_two_ne_zero (by linear_combination -ht)

theorem negativeSix_commute (hcard : Nat.card F = 3) (g : MinusSix (F := F)) :
    Commute g (negativeSix hcard) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change g.val.val (-v) = -(g.val.val v)
  exact map_neg _ _

end ClassicalOrthogonal.OddSevenTernaryCover
