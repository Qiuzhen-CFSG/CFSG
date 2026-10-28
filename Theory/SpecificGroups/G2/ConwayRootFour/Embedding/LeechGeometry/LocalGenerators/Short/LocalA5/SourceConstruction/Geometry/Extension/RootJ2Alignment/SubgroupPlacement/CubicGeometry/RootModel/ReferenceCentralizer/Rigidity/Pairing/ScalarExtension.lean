module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Rigidity.PairedAction

/-!
# Recovering the four-element-field pairing from binary coefficients

For a binary form B balanced under the literal Y, the two coefficients
`(B(v,w), B(Yv,w))` define a GoldenFour-valued bilinear form: Y² = Y + 1
is precisely the scalar multiplication rule. Transport through the published
`Long.scalarFieldEquiv` gives F-bilinearity for the existing scoped module.
The first coefficient detects nondegeneracy, and commutation with Y preserves
invariance for the actual reference centralizer action.

The final constructor consumes the binary lattice form in `Pairing`.
Source context: Aschbacher, *Sporadic Groups* (1994), 49.5, p.283, with the
scalar and Leech conventions of the attributed ATLAS imports.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel.PairingScalar
open scoped Long

private theorem y_square (v : fixedSpace) :
    Long.yEnd (Long.yEnd v) = v + Long.yEnd v := by
  have h := congrArg (fun f : Module.End Bit fixedSpace => f v) Long.yEnd_quadratic
  simpa only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    one_smul, Module.End.one_apply] using h

private theorem scalar_expand (a : F) (v : fixedSpace) :
    a • v = (Long.scalarFieldEquiv a).re • v +
      (Long.scalarFieldEquiv a).im • Long.yEnd v := by
  apply Subtype.ext
  exact Long.smul_val a v

def value (B : LinearMap.BilinForm Bit fixedSpace) (v w : fixedSpace) : GoldenFour :=
  ⟨B v w, B (Long.yEnd v) w⟩

private theorem value_add_left (B : LinearMap.BilinForm Bit fixedSpace)
    (v v' w : fixedSpace) : value B (v + v') w = value B v w + value B v' w := by
  ext <;> simp only [value, map_add, LinearMap.add_apply, QuadraticAlgebra.re_add,
    QuadraticAlgebra.im_add]

private theorem value_add_right (B : LinearMap.BilinForm Bit fixedSpace)
    (v w w' : fixedSpace) : value B v (w + w') = value B v w + value B v w' := by
  ext <;> simp only [value, map_add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]

private theorem value_smul_left (B : LinearMap.BilinForm Bit fixedSpace)
    (a : F) (v w : fixedSpace) :
    value B (a • v) w = Long.scalarFieldEquiv a * value B v w := by
  rw [scalar_expand]
  ext <;> simp only [value, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    y_square, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    smul_eq_mul] <;> ring

private theorem value_smul_right (B : LinearMap.BilinForm Bit fixedSpace)
    (hbalance : ∀ v w, B (Long.yEnd v) w = B v (Long.yEnd w))
    (a : F) (v w : fixedSpace) :
    value B v (a • w) = Long.scalarFieldEquiv a * value B v w := by
  rw [scalar_expand]
  ext <;> simp only [value, map_add, map_smul,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    ← hbalance, y_square, LinearMap.add_apply, smul_eq_mul] <;> ring

/-- Recover the F-valued form from its binary coefficient and its Y-translate. -/
def form (B : LinearMap.BilinForm Bit fixedSpace)
    (hbalance : ∀ v w, B (Long.yEnd v) w = B v (Long.yEnd w)) :
    LinearMap.BilinForm F fixedSpace :=
  LinearMap.mk₂ F (fun v w => Long.scalarFieldEquiv.symm (value B v w))
    (fun v v' w => by rw [value_add_left, map_add])
    (fun a v w => by rw [value_smul_left, map_mul, RingEquiv.symm_apply_apply]; rfl)
    (fun v w w' => by rw [value_add_right, map_add])
    (fun a v w => by rw [value_smul_right B hbalance, map_mul,
      RingEquiv.symm_apply_apply]; rfl)

/-- Nondegeneracy is already detected by the first binary coefficient. -/
theorem form_nondegenerate (B : LinearMap.BilinForm Bit fixedSpace)
    (hbalance : ∀ v w, B (Long.yEnd v) w = B v (Long.yEnd w))
    (hn : B.Nondegenerate) : (form B hbalance).Nondegenerate := by
  constructor
  · intro v hv
    apply hn.1 v
    intro w
    have h := congrArg (fun z : F => (Long.scalarFieldEquiv z).re) (hv w)
    simpa only [form, LinearMap.mk₂_apply, RingEquiv.apply_symm_apply,
      map_zero, QuadraticAlgebra.re_zero, value] using h
  · intro w hw
    apply hn.2 w
    intro v
    have h := congrArg (fun z : F => (Long.scalarFieldEquiv z).re) (hw v)
    simpa only [form, LinearMap.mk₂_apply, RingEquiv.apply_symm_apply,
      map_zero, QuadraticAlgebra.re_zero, value] using h

private theorem action_y (g : referenceCentralizer) (v : fixedSpace) :
    Long.yEnd (referenceFixedAction g v) = referenceFixedAction g (Long.yEnd v) := by
  apply Subtype.ext
  change quotientModTwoRepresentation y (quotientModTwoRepresentation g.val v.val) =
    quotientModTwoRepresentation g.val (quotientModTwoRepresentation y v.val)
  have h := g.property.1 y (show y ∈ I from ⟨threeCycle, rfl⟩)
  simpa only [map_mul, LinearEquiv.mul_apply] using
    congrArg (fun k => quotientModTwoRepresentation k v.val) h

/-- The reconstruction preserves invariance for the literal reference action. -/
def ofBinary (B : LinearMap.BilinForm Bit fixedSpace)
    (hn : B.Nondegenerate)
    (hbalance : ∀ v w, B (Long.yEnd v) w = B v (Long.yEnd w))
    (hinv : ∀ (g : referenceCentralizer) (v w : fixedSpace),
      B (referenceFixedAction g v) (referenceFixedAction g w) = B v w) :
    ReferenceInvariantPairing where
  form := form B hbalance
  nondegenerate := form_nondegenerate B hbalance hn
  invariant g v w := by
    change Long.scalarFieldEquiv.symm (value B (referenceFixedAction g v)
      (referenceFixedAction g w)) = Long.scalarFieldEquiv.symm (value B v w)
    congr 1
    ext
    · exact hinv g v w
    · change B (Long.yEnd (referenceFixedAction g v)) (referenceFixedAction g w) =
        B (Long.yEnd v) w
      rw [action_y, hinv]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel.PairingScalar
