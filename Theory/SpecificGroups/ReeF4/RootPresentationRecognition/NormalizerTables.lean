module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NormalizerPresentation
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order.TorusCardinality

/-!
# Finite Weyl tables on the full Ree torus

The native torus equivalence transports the literal Weyl action to the two
field-unit coordinates. The two resulting tables satisfy their native
conjugation equations, involution laws, and mixed eighth-power relation.
The proved normalizer equivalence also gives its exact order; at m = 0 this
is sixteen, retaining the full binary model's Weyl group.

Source: GLS3 2.3.2--4, `refs/KGroup/GLS3/chapter2.tex`. These are the torus
part of the finite presentation tables, not signed-root conjugation tables.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.NormalizerTables
open Subgroup Parabolics CentralCovers.OddPrimary.Order WeylPresentation NormalizerPresentation

/-- Transport of the literal native Weyl action through both field-unit parameters. -/
def fieldAction (m : ℕ) : Weyl →* MulAut ((CoefficientField m)ˣ × (CoefficientField m)ˣ) where
  toFun w := (fixedTorusEquiv m).trans ((action m w).trans (fixedTorusEquiv m).symm)
  map_one' := by
    apply MulEquiv.ext
    intro t
    simp only [map_one, MulEquiv.trans_apply, MulAut.one_apply, MulEquiv.symm_apply_apply]
  map_mul' w v := by
    apply MulEquiv.ext
    intro t
    simp only [map_mul, MulEquiv.trans_apply, MulAut.mul_apply, MulEquiv.apply_symm_apply]

@[simp] theorem fieldAction_apply (m : ℕ) (w : Weyl)
    (t : (CoefficientField m)ˣ × (CoefficientField m)ˣ) :
    fieldAction m w t = (fixedTorusEquiv m).symm (action m w (fixedTorusEquiv m t)) := rfl

/-- The two fixed finite torus tables S_i in the source equation contract. -/
def table (m : ℕ) (s : Bool) : MulAut ((CoefficientField m)ˣ × (CoefficientField m)ˣ) :=
  fieldAction m (simple s)

/-- Native verification uses the actual fixed torus and literal orbit word. -/
theorem native_equation (m : ℕ) (s : Bool)
    (t : (CoefficientField m)ˣ × (CoefficientField m)ˣ) :
    (fixedTorusEquiv m (table m s t) : Model m) =
      Parabolics.Binary.FixedGeometry.weylLift m (side s) * fixedTorusEquiv m t *
        (Parabolics.Binary.FixedGeometry.weylLift m (side s))⁻¹ := by
  change ((fixedTorusEquiv m) ((fixedTorusEquiv m).symm
    (action m (simple s) (fixedTorusEquiv m t))) : Model m) = _
  rw [MulEquiv.apply_symm_apply, action_apply, weyl_simple]

/-- Involutivity is retained on both unit parameters. -/
theorem table_sq (m : ℕ) (s : Bool) : table m s ^ 2 = 1 := by
  change fieldAction m (simple s) ^ 2 = 1
  rw [← map_pow]
  have hs : simple s ^ 2 = 1 := by cases s <;> decide
  rw [hs,map_one]

/-- The literal octagon relation is retained on the full torus action. -/
theorem table_product_eight (m : ℕ) : (table m false * table m true)^8 = 1 := by
  change (fieldAction m (simple false) * fieldAction m (simple true))^8 = 1
  rw [← map_mul,← map_pow]
  have hs : (simple false * simple true)^8 = 1 := by decide
  rw [hs,map_one]

/-- Exact full-normalizer size, derived from the proved evaluation equivalence. -/
theorem card_normalizer (m : ℕ) :
    Nat.card (SectionGeometry.BNPair.normalizerWords m) = (2^(2*m+1)-1)^2 * 16 := by
  rw [← Nat.card_congr (nativeEquiv m).toEquiv, SemidirectProduct.card,
    card_fixedTorus, DihedralGroup.nat_card]

/-- The binary endpoint retains all sixteen Weyl matrices; its torus is trivial. -/
theorem card_binary_normalizer : Nat.card (SectionGeometry.BNPair.normalizerWords 0) = 16 := by
  rw [card_normalizer]
  norm_num

end ReeF4.RootPresentationRecognition.NormalizerTables
