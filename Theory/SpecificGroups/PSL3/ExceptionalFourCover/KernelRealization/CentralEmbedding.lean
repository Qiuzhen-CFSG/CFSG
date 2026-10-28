module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.CentralEmbedding.Elements

/-!
# The full central C₄ × C₄ × C₃ subgroup of the explicit PSL₃(4) model

The three certified signed words give cyclic homomorphisms into the center.
Their product is injective: the first permutation coordinate detects the second
C₄ exponent, the second then detects the first, and the scalar matrix detects
the C₃ exponent. Thus all 48 products are distinct. The literal projective
projection kills them. No order bound or universal-kernel bound is used.

Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1. This supplies the
central-embedding input of `KernelRealization`; it does not assert that the
48-element subgroup exhausts that projection's kernel.
-/

public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel
open CentralWords

private def centralCyclic {n : ℕ} [NeZero n] (g : Group)
    (hp : g ^ n = 1) (hc : g ∈ Subgroup.center Group) :
    Multiplicative (ZMod n) →* Subgroup.center Group where
  toFun a := ⟨g ^ a.toAdd.val, (Subgroup.center Group).pow_mem hc _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change g ^ (a.toAdd + b.toAdd).val = g ^ a.toAdd.val * g ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hp, pow_add]

private def centralCoordinates : Multiplier →* Subgroup.center Group :=
  ((centralCyclic elementA elementA_fourth elementA_central).noncommCoprod
    (centralCyclic elementB elementB_fourth elementB_central)
    (fun _ _ => mul_comm' _ _)).noncommCoprod
    (centralCyclic elementC elementC_cube elementC_central) (fun _ _ => mul_comm' _ _)

/-- The two order-four source words, followed by the order-three source word. -/
def centralEmbedding : Multiplier →* Group :=
  (Subgroup.center Group).subtype.comp centralCoordinates

theorem centralEmbedding_apply (a : Multiplier) :
    centralEmbedding a =
      elementA ^ a.1.1.toAdd.val * elementB ^ a.1.2.toAdd.val *
        elementC ^ a.2.toAdd.val := by
  rfl

theorem centralEmbedding_central (a : Multiplier) :
    centralEmbedding a ∈ Subgroup.center Group :=
  (centralCoordinates a).property

theorem centralEmbedding_first (a : Multiplier) :
    (centralEmbedding a).val.1.1 = permA ^ a.1.2.toAdd.val := by
  rw [centralEmbedding_apply]
  change 1 ^ a.1.1.toAdd.val * permA ^ a.1.2.toAdd.val * 1 ^ a.2.toAdd.val = _
  simp only [one_pow, one_mul, mul_one]

theorem centralEmbedding_second (a : Multiplier) :
    (centralEmbedding a).val.1.2 = permB ^ a.1.1.toAdd.val * permB ^ a.1.2.toAdd.val := by
  rw [centralEmbedding_apply]
  change (permB ^ a.1.1.toAdd.val * permB ^ a.1.2.toAdd.val) * 1 ^ a.2.toAdd.val = _
  simp only [one_pow, mul_one]

theorem centralEmbedding_matrix (a : Multiplier) :
    (centralEmbedding a).val.2 = scalarZ ^ a.2.toAdd.val := by
  rw [centralEmbedding_apply]
  change 1 ^ a.1.1.toAdd.val * 1 ^ a.1.2.toAdd.val * scalarZ ^ a.2.toAdd.val = _
  simp only [one_pow, one_mul]

private theorem scalarZ_detect (a : ZMod 3) :
    ((scalarZ ^ a.val : SL) : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 → a = 0 := by
  revert a
  decide +kernel

/-- Independence of all 48 products, detected in the literal ambient coordinates. -/
theorem centralEmbedding_injective : Function.Injective centralEmbedding := by
  apply (injective_iff_map_eq_one centralEmbedding).mpr
  rintro ⟨⟨a, b⟩, c⟩ h
  have hb0 := congrArg (fun g : Group => g.val.1.1 0) h
  rw [centralEmbedding_first] at hb0
  have hb : b = 1 := by
    change b.toAdd = 0
    exact permA_detect _ hb0
  have ha0 := congrArg (fun g : Group => g.val.1.2 0) h
  rw [centralEmbedding_second] at ha0
  change (permB ^ a.toAdd.val * permB ^ b.toAdd.val) 0 = 0 at ha0
  have ha : a = 1 := by
    change a.toAdd = 0
    apply permB_detect
    simpa only [hb, toAdd_one, ZMod.val_zero, pow_zero, mul_one] using ha0
  have hc0 := congrArg (fun g : Group => (g.val.2 : Matrix (Fin 3) (Fin 3) F) 0 0) h
  rw [centralEmbedding_matrix] at hc0
  have hc : c = 1 := by
    change c.toAdd = 0
    exact scalarZ_detect _ hc0
  exact Prod.ext (Prod.ext ha hb) hc

/-- The scalar quotient used by the model kills the entire embedded multiplier. -/
theorem projection_comp_centralEmbedding : projection.comp centralEmbedding = 1 := by
  ext a
  change projection (centralEmbedding a) = 1
  rw [centralEmbedding_apply, map_mul, map_mul, map_pow, map_pow, map_pow,
    projection_elementA, projection_elementB, projection_elementC]
  simp only [one_pow, one_mul]

end Matrix.PSL3.ExceptionalFourCover.KernelModel
