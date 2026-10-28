module
public import Theory.GroupTheory.NormalizerActionFixer
/-!
# Embedding centralizing supplements into automorphism fixers

A subgroup normalizing K and centralizing U acts on K through the pointwise
fixer of U intersect K. A faithful normalizer action makes this homomorphism
injective. This retains the literal ambient conjugation action.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Conjugation by a subgroup which normalizes K and centralizes U fixes U in K. -/
def normalizerCentralizerHom (K D U : Subgroup G)
    (hDN : D ≤ normalizer (K : Set G))
    (hDC : D ≤ centralizer (U : Set G)) :
    D →* fixingSubgroup (MulAut K) (U.subgroupOf K : Set K) :=
  (K.normalizerMonoidHom.comp (inclusion hDN)).codRestrict _ (by
    intro d
    rw [mem_fixingSubgroup_iff]
    intro u hu
    apply Subtype.ext
    change (d : G) * (u : G) * (d : G)⁻¹ = (u : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hDC d.property u hu).symm)

theorem normalizerCentralizerHom_injective (K D U : Subgroup G)
    (hDN : D ≤ normalizer (K : Set G))
    (hDC : D ≤ centralizer (U : Set G))
    (hf : Function.Injective K.normalizerMonoidHom) :
    Function.Injective (normalizerCentralizerHom K D U hDN hDC) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : normalizer (K : Set G) => (z : G))
    (hf (congrArg Subtype.val h))

@[simp] theorem normalizerCentralizerHom_apply (K D U : Subgroup G)
    (hDN : D ≤ normalizer (K : Set G))
    (hDC : D ≤ centralizer (U : Set G)) (d : D) (k : K) :
    ((normalizerCentralizerHom K D U hDN hDC d : MulAut K) k : G) =
      (d : G) * (k : G) * (d : G)⁻¹ := by rfl

end Subgroup
