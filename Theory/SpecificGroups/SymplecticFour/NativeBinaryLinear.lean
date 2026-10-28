module
public import Theory.SpecificGroups.SymplecticFour.NativeAlternating
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.BinaryLinear.EvenLieLevi

/-!
# Binary linear exclusions in symplectic degree four

The actual PSL₄(2) carrier is A₈. The actual PSL₅(2) parabolic contains
PSL₃(2) through its block Levi embedding. In each case the order-seven
normalizer contradicts the characteristic-two symplectic spectrum. Field
transport retains the given carrier for every binary field model.

Source: Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour.NativeBinaryLinear
variable {F : Type*} [Field F] [CharP F 2]

/-- The actual exceptional A₈ comparison excludes PSL₄(2). -/
theorem four_not_injective (j : PSL(4,ZMod 2) →* Sp F) : ¬Function.Injective j := by
  intro hj
  let e := Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
  exact NativeAlternating.alternatingEight_not_injective (j.comp e.symm.toMonoidHom)
    (hj.comp e.symm.injective)

/-- The actual block Levi subgroup excludes PSL₅(2). -/
theorem five_not_injective (j : PSL(5,ZMod 2) →* Sp F) : ¬Function.Injective j := by
  intro hj
  let inc : Matrix.PSL3Two.PSL →* PSL(2,ZMod 2) × Matrix.PSL3Two.PSL :=
    (1 : Matrix.PSL3Two.PSL →* PSL(2,ZMod 2)).prod (MonoidHom.id _)
  have hi : Function.Injective inc := by intro a b h; exact congrArg Prod.snd h
  let l : Matrix.PSL3Two.PSL →* PSL(5,ZMod 2) :=
    (BinaryLinear.EvenLieLevi.projectiveParabolic 3).subtype.comp
      ((BinaryLinear.EvenLieLevi.projectiveLevi 3 (by decide)).comp inc)
  have hl : Function.Injective l := Subtype.val_injective.comp
    ((BinaryLinear.EvenLieLevi.projectiveLevi_injective 3 (by decide)).comp hi)
  let f := j.comp l
  have hf : Function.Injective f := hj.comp hl
  obtain ⟨a,b,ha,han,hab⟩ := Matrix.PSL3Two.exists_seven_conjugate_square
  apply SevenNormalizer.seven_not_conjugate_square (f a) (f b)
  · rw [←map_pow,ha,map_one]
  · exact fun h => han (hf (h.trans f.map_one.symm))
  · simpa only [map_mul,map_inv,map_pow] using congrArg f hab

/-- The binary linear rows of Theorem C admit no faithful Sp₄ action. -/
theorem small_binary_not_injective {n : ℕ} (hn : n=4 ∨ n=5)
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K=2)
    (j : PSL(n,K) →* Sp F) : ¬Function.Injective j := by
  intro hj
  letI := Fintype.ofFinite K
  let eK : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card, Nat.card_zmod] using hK)
  let e := Atlas.fieldEquivPSL n eK
  rcases hn with rfl|rfl
  · exact four_not_injective (j.comp e.symm.toMonoidHom) (hj.comp e.symm.injective)
  · exact five_not_injective (j.comp e.symm.toMonoidHom) (hj.comp e.symm.injective)
end Theory.SpecificGroups.SymplecticFour.NativeBinaryLinear
