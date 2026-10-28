module

public import Theory.Representation.OrthogonalNatural
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.Representation.BinaryOffender.Basic

/-!
# The actual binary orthogonal module in 13.8.16

The group is the existing scalar quotient of the Siegel-generated group of
`formD 2 F`, where F is the concrete field of four elements. Its action is
exactly the descended natural action, restricted to the binary field.
Faithfulness uses the proved triviality of scalar isometries in characteristic
two. Cardinality gives binary dimension eight.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953 (PDF pp.969–970).
The module identification from the ambient source group is a separate input.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight

abbrev F := Representation.SL2FourNatural.F
abbrev V := ClassicalOrthogonal.VectorD 2 F
abbrev G := ClassicalOrthogonal.POmegaPlus 2 F

/-- The natural four-dimensional representation over the field of four elements. -/
def fieldAction : Representation F G V :=
  ClassicalOrthogonal.projectiveElementaryNatural (ClassicalOrthogonal.formD 2 F)

/-- The actual natural action restricted to the binary field. -/
def action : Representation (ZMod 2) G V where
  toFun g := (fieldAction g).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Module.End F V => f v) fieldAction.map_one
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : Module.End F V => f v) (fieldAction.map_mul g h)

@[simp] theorem action_apply (g : G) (v : V) : action g v = fieldAction g v := rfl

/-- An explicit lift to the existing elementary orthogonal carrier. -/
@[simp] theorem action_projective (g : ClassicalOrthogonal.OmegaPlus 2 F) (v : V) :
    action (ClassicalOrthogonal.projectiveElementaryMap (ClassicalOrthogonal.formD 2 F) g) v =
      g.val.val v :=
  ClassicalOrthogonal.projectiveElementaryNatural_mk _ g v

/-- The binary action is faithful, as is the natural action before restriction. -/
theorem action_injective : Function.Injective action := by
  intro g h he
  apply (ClassicalOrthogonal.elementaryProjectiveEquiv
    (ClassicalOrthogonal.formD 2 F)).symm.injective
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) V => f v) he

/-- The same action with its invertibility retained. -/
def linearAction : G →* (V ≃ₗ[ZMod 2] V) where
  toFun g := LinearEquiv.ofBijective (action g) (action.apply_bijective g)
  map_one' := by apply LinearEquiv.ext; intro v; exact congrArg (fun f : Module.End (ZMod 2) V => f v) action.map_one
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul g h)

@[simp] theorem linearAction_apply (g : G) (v : V) : linearAction g v = action g v := rfl

/-- Scalar restriction preserves the full quadratic form. -/
theorem action_preserves (g : G) (v : V) :
    ClassicalOrthogonal.formD 2 F (action g v) = ClassicalOrthogonal.formD 2 F v :=
  ClassicalOrthogonal.projectiveElementaryNatural_preserves _ g v

/-- The scalar field is two-dimensional over the binary field. -/
theorem finrank_field : Module.finrank (ZMod 2) F = 2 :=
  ClassicalOrthogonal.FourPlusMatrix.Binary.finrank_field

/-- Four hyperbolic coordinates over F₄ have binary dimension eight. -/
theorem finrank_binary : Module.finrank (ZMod 2) V = 8 := by
  change Module.finrank (ZMod 2) (ClassicalOrthogonal.Index 2 → F) = 8
  rw [Module.finrank_pi_fintype]
  simp [ClassicalOrthogonal.Index, finrank_field]

/-- The same natural space has dimension four over its scalar field. -/
theorem finrank_natural : Module.finrank F V = 4 := by
  change Module.finrank F (ClassicalOrthogonal.Index 2 → F) = 4
  rw [Module.finrank_pi_fintype]
  simp [ClassicalOrthogonal.Index]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight
