module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.TwoKernel.ThreeAction
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Finite

/-!
# An elementary abelian rank-three witness in the Suz centralizer

This supplies the direct-embedding alternative to bounding the kernel of the
27-pair action. The words `d⁴` and its conjugates by `c⁻¹ d c d c²` and
`c d³ c⁻¹` have cube one and commute, as checked on all 1782 letters.
Their 27 products are distinguished by their images of letters 0 and 1.
Thus they embed `(C₃)³` in the actual numerator `⟨c,d⟩`, already proved to
centralize the specified involution. No splitting or kernel bound is assumed.

The chapter consumer uses this local rank obstruction to exclude Suz from
strong quasithinness. The precise existing orthogonal quotient is preserved.
Source: ATLAS SuzG1-p1782B0; GLS3 Table 5.3o; Aschbacher--Smith A.2.19 and I.1.3.
-/

public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection
namespace ThreeWitness

/-- Three independent cyclic groups of order three. -/
abbrev Parameters := Multiplicative (ZMod 3) ×
  Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

private def cycle (g : numerator) (hg : g ^ 3 = 1) : Multiplicative (ZMod 3) →* numerator where
  toFun a := g ^ a.toAdd.val
  map_one' := pow_zero _
  map_mul' a b := by
    change g ^ (a.toAdd + b.toAdd).val = _
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

/-- The actual elementary abelian subgroup is parametrized by the three checked words. -/
def embedding : Parameters →* numerator :=
  (cycle x x_cube).noncommCoprod
    ((cycle y y_cube).noncommCoprod (cycle t t_cube)
      (fun a b => y_commute_t.pow_pow a.toAdd.val b.toAdd.val))
    (fun a b => (x_commute_y.pow_pow a.toAdd.val b.1.toAdd.val).mul_right
      (x_commute_t.pow_pow a.toAdd.val b.2.toAdd.val))

private def parameterMap (a : Parameters) (b : Fin 1782) : Fin 1782 :=
  (xMap^[a.1.toAdd.val]) ((yMap^[a.2.1.toAdd.val]) ((tMap^[a.2.2.toAdd.val]) b))

private theorem embedding_apply (a : Parameters) (b : Fin 1782) :
    representation (embedding a) b = parameterMap a b := by
  change representation (x ^ a.1.toAdd.val *
    (y ^ a.2.1.toAdd.val * t ^ a.2.2.toAdd.val)) b = _
  have hx : (representation x : Fin 1782 → Fin 1782) = xMap := funext x_apply
  have hy : (representation y : Fin 1782 → Fin 1782) = yMap := funext y_apply
  have ht : (representation t : Fin 1782 → Fin 1782) = tMap := funext t_apply
  simp only [map_mul, Equiv.Perm.mul_apply, map_pow, Equiv.Perm.coe_pow, hx, hy, ht,
    parameterMap]

private theorem coordinates_injective :
    Function.Injective (fun a : Parameters => (parameterMap a 0, parameterMap a 1)) := by
  decide +kernel

/-- Evaluation at two original letters distinguishes all 27 products. -/
theorem embedding_injective : Function.Injective embedding := by
  intro a b hab
  apply coordinates_injective
  apply Prod.ext
  · simpa only [embedding_apply] using
      congrArg (fun g : numerator => representation g 0) hab
  · simpa only [embedding_apply] using
      congrArg (fun g : numerator => representation g 1) hab

end ThreeWitness

/-- The actual centralizing numerator contains an elementary abelian three-group of rank three. -/
theorem numerator_primeRank_three_ge : 3 ≤ primeRank 3 numerator := by
  have hp : ∀ a : ThreeWitness.Parameters, a ^ 3 = 1 := by decide +kernel
  have hc : Nat.card ThreeWitness.Parameters = 3 ^ 3 := by
    simp [Nat.card_eq_fintype_card]
  exact primeRank_ge_of_elementary_embedding hp hc ThreeWitness.embedding
    ThreeWitness.embedding_injective

end Sporadic.LeechRelated.Suz.CentralizerSection
