module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SourceClass
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechFullIsometries
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.PolynomialSelection.KernelAction
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Character

/-!
# Rational representation on the complementary sixteen coordinates

The literal integral octad centralizer acts on the rational coordinates outside
the octad. Zero extension intertwines this action with the existing rational
extension of Leech isometries, and the restricted dot product is preserved.

The octad restriction kernel acts faithfully: for an integral vector x, its
octad part x - sign(x) is fixed by the definition of the kernel, while its
complementary part x + sign(x) is detected by this representation. The marked
complementary sign acts as minus identity. Under extraspeciality it is the
unique nonidentity central element of the kernel.

The polynomial on the WHOLE Leech lattice extends by a rational basis and then
restricts to this representation. Orthogonality equates the traces of an actor
and its inverse, so an actor of order three satisfying the polynomial has trace
-8. The induced action on endomorphisms therefore has trace 64. These results
supply the concrete representation for the remaining extraspecial projective
basis argument; no quaternion class selection is assumed or asserted here.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5 and Chapter 9,
Exercise 6, p.141. The rational Leech extension used here is the existing ATLAS
port credited in `LeechRationalExtension` and `LeechFullIsometries`; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section

open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace PolynomialSelection

abbrev ComplementCoordinate := {i : Omega // (golayBasis 0).val i = 0}
abbrev ComplementSpace := ComplementCoordinate → ℚ

theorem complementCoordinate_card : Fintype.card ComplementCoordinate = 16 := by
  classical
  have h := Fintype.card_subtype_compl (fun i : Omega => (golayBasis 0).val i ≠ 0)
  simp only [not_not] at h
  change Fintype.card ComplementCoordinate = Fintype.card Omega - Fintype.card Coordinate at h
  rw [coordinate_card] at h
  simpa [Omega, HexIndex] using h

theorem complementSpace_finrank : Module.finrank ℚ ComplementSpace = 16 := by
  rw [Module.finrank_fintype_fun_eq_card, complementCoordinate_card]

def complementEmbedding : ComplementSpace →ₗ[ℚ] RationalCoordinates where
  toFun x i := if hi : (golayBasis 0).val i = 0 then x ⟨i, hi⟩ else 0
  map_add' x y := by ext i; dsimp; split_ifs <;> simp
  map_smul' n x := by ext i; dsimp; split_ifs <;> simp

def complementProjection : RationalCoordinates →ₗ[ℚ] ComplementSpace where
  toFun x i := x i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complementProjection_embedding (x : ComplementSpace) :
    complementProjection (complementEmbedding x) = x := by
  funext i
  simp [complementProjection, complementEmbedding, i.prop]

theorem complementEmbedding_injective : Function.Injective complementEmbedding :=
  Function.LeftInverse.injective complementProjection_embedding

def rationalSign : RationalCoordinates →ₗ[ℚ] RationalCoordinates where
  toFun x i := if (golayBasis 0).val i = 0 then x i else -x i
  map_add' x y := by ext i; dsimp; split_ifs <;> simp [add_comm]
  map_smul' n x := by ext i; dsimp; split_ifs <;> simp

theorem rationalSign_eq : rationalSign = (rationalExtension sign.val).toLinearMap := by
  apply rationalExtension_unique
  intro x
  ext i
  change (if (golayBasis 0).val i = 0 then (x.val i : ℚ) else -(x.val i : ℚ)) =
    ((if (golayBasis 0).val i = 0 then x.val i else -x.val i : ℤ) : ℚ)
  split_ifs <;> simp

theorem rationalSign_embedding (x : ComplementSpace) :
    rationalSign (complementEmbedding x) = complementEmbedding x := by
  ext i
  simp only [rationalSign, complementEmbedding, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> simp

theorem embedding_projection_of_fixed {x : RationalCoordinates} (hx : rationalSign x = x) :
    complementEmbedding (complementProjection x) = x := by
  ext i
  by_cases hi : (golayBasis 0).val i = 0
  · simp [complementEmbedding, complementProjection, hi]
  · have h := congrFun hx i
    simp only [rationalSign, LinearMap.coe_mk, AddHom.coe_mk, if_neg hi] at h
    simp only [complementEmbedding, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hi]
    linarith

def ambientAction : centralizer →* (RationalCoordinates ≃ₗ[ℚ] RationalCoordinates) :=
  rationalLatticeIsometries.subtype.comp (fullIsometryExtension.comp centralizer.subtype)

theorem ambientAction_agrees (g : centralizer) (x : leech) :
    ambientAction g (rationalEmbedding x.val) = rationalEmbedding (g.val.val x).val :=
  rationalExtension_agrees g.val.val x

theorem ambientAction_commutes_sign (g : centralizer) (x : RationalCoordinates) :
    ambientAction g (rationalSign x) = rationalSign (ambientAction g x) := by
  have h := (mem_centralizer.mp g.prop).map
    (rationalLatticeIsometries.subtype.comp fullIsometryExtension)
  rw [rationalSign_eq]
  exact congrArg (fun f : RationalCoordinates ≃ₗ[ℚ] RationalCoordinates => f x) h.eq

theorem ambientAction_preserves (g : centralizer) (x : ComplementSpace) :
    rationalSign (ambientAction g (complementEmbedding x)) =
      ambientAction g (complementEmbedding x) := by
  rw [← ambientAction_commutes_sign, rationalSign_embedding]

def complementAction : centralizer →* (ComplementSpace ≃ₗ[ℚ] ComplementSpace) where
  toFun g :=
    { toFun := fun x => complementProjection (ambientAction g (complementEmbedding x))
      invFun := fun x => complementProjection (ambientAction g⁻¹ (complementEmbedding x))
      left_inv := by
        intro x
        dsimp only
        rw [embedding_projection_of_fixed (ambientAction_preserves g x), map_inv]
        simp only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, complementProjection_embedding]
      right_inv := by
        intro x
        dsimp only
        rw [embedding_projection_of_fixed (ambientAction_preserves g⁻¹ x), map_inv]
        simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, complementProjection_embedding]
      map_add' x y := by simp only [map_add]
      map_smul' n x := by simp only [map_smul, RingHom.id_apply] }
  map_one' := by ext x; simp [complementProjection_embedding]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change complementProjection (ambientAction (g * h) (complementEmbedding x)) =
      complementProjection (ambientAction g (complementEmbedding
        (complementProjection (ambientAction h (complementEmbedding x)))))
    rw [embedding_projection_of_fixed (ambientAction_preserves h x), map_mul]
    rfl

theorem complementAction_intertwines (g : centralizer) (x : ComplementSpace) :
    complementEmbedding (complementAction g x) = ambientAction g (complementEmbedding x) :=
  embedding_projection_of_fixed (ambientAction_preserves g x)

theorem ambient_polynomial {r : centralizer}
    (hr : ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0)
    (x : RationalCoordinates) : ambientAction r (ambientAction r x) + ambientAction r x + x = 0 := by
  have h : ((ambientAction r).toLinearMap * (ambientAction r).toLinearMap +
      (ambientAction r).toLinearMap + 1 : Module.End ℚ RationalCoordinates) = 0 := by
    apply rationalLeechBasis.ext
    intro i
    change ambientAction r (ambientAction r (rationalLeechBasis i)) +
      ambientAction r (rationalLeechBasis i) + rationalLeechBasis i = 0
    rw [rationalLeechBasis_apply, ambientAction_agrees, ambientAction_agrees]
    have hi := congrArg (fun y : leech => rationalEmbedding y.val) (hr (leechBasis i))
    simpa only [Submodule.coe_add, Submodule.coe_zero, map_add, map_zero] using hi
  exact LinearMap.congr_fun h x

theorem complement_polynomial {r : centralizer}
    (hr : ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0)
    (x : ComplementSpace) : complementAction r (complementAction r x) +
      complementAction r x + x = 0 := by
  apply complementEmbedding_injective
  simp only [map_add, map_zero, complementAction_intertwines]
  exact ambient_polynomial hr _

theorem complementEmbedding_form (x y : ComplementSpace) :
    rationalForm (complementEmbedding x) (complementEmbedding y) =
      (1 / 8 : ℚ) * ∑ i, x i * y i := by
  have hs : (∑ i : ComplementCoordinate, x i * y i) =
      ∑ i : Omega, complementEmbedding x i * complementEmbedding y i := by
    apply Fintype.sum_of_injective (fun i : ComplementCoordinate => i.val) Subtype.val_injective
    · intro i hi
      have hn : ¬(golayBasis 0).val i = 0 := fun h => hi ⟨⟨i, h⟩, rfl⟩
      simp [complementEmbedding, hn]
    · intro i
      simp [complementEmbedding, i.prop]
  rw [hs]
  rfl

theorem complementAction_dot (g : centralizer) (x y : ComplementSpace) :
    (∑ i, complementAction g x i * complementAction g y i) = ∑ i, x i * y i := by
  have h := rationalExtension_form g.val (complementEmbedding x) (complementEmbedding y)
  change rationalForm (ambientAction g (complementEmbedding x))
    (ambientAction g (complementEmbedding y)) = _ at h
  rw [← complementAction_intertwines, ← complementAction_intertwines,
    complementEmbedding_form, complementEmbedding_form] at h
  linarith

theorem complementAction_trace_inv (g : centralizer) :
    LinearMap.trace ℚ ComplementSpace (complementAction g⁻¹).toLinearMap =
      LinearMap.trace ℚ ComplementSpace (complementAction g).toLinearMap := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ ComplementCoordinate),
    LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ ComplementCoordinate)]
  apply Finset.sum_congr rfl
  intro i _
  change (complementAction g⁻¹ (Pi.single i 1)) i = (complementAction g (Pi.single i 1)) i
  have h := complementAction_dot g (complementAction g⁻¹ (Pi.single i 1)) (Pi.single i 1)
  rw [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
  change dotProduct (Pi.single i 1) (complementAction g (Pi.single i 1)) =
    dotProduct ((complementAction g).symm (Pi.single i 1)) (Pi.single i 1) at h
  simpa only [dotProduct_single_one, single_one_dotProduct, map_inv, LinearEquiv.coe_inv]
    using h.symm

theorem complementAction_trace_of_polynomial {r : centralizer} (ho : orderOf r = 3)
    (hr : ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0) :
    LinearMap.trace ℚ ComplementSpace (complementAction r).toLinearMap = -8 := by
  have hp : (complementAction (r ^ 2)).toLinearMap +
      (complementAction r).toLinearMap + (1 : Module.End ℚ ComplementSpace) = 0 := by
    apply LinearMap.ext
    intro x
    change complementAction (r ^ 2) x + complementAction r x + x = 0
    rw [map_pow]
    exact complement_polynomial hr x
  have hinv : r ^ 2 = r⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      r ^ 2 * r = r ^ 3 := (pow_succ r 2).symm
      _ = 1 := ho ▸ pow_orderOf_eq_one r
  rw [hinv] at hp
  have ht := congrArg (LinearMap.trace ℚ ComplementSpace) hp
  rw [map_add, map_add, map_zero, LinearMap.trace_one,
    complementAction_trace_inv, complementSpace_finrank] at ht
  norm_num at ht
  linarith

theorem kernel_complementAction_injective :
    Function.Injective (complementAction.comp action.ker.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro g hg
  change g = 1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hminus : x - sign.val x ∈ lattice := by
    rw [mem_lattice_iff_support]
    intro i hi
    change x.val i - (if (golayBasis 0).val i = 0 then x.val i else -x.val i) = 0
    simp [hi]
  have hv := (mem_action_ker g.val).mp g.prop ⟨x - sign.val x, hminus⟩
  have hplus : rationalSign (rationalEmbedding (x + sign.val x).val) =
      rationalEmbedding (x + sign.val x).val := by
    ext i
    change (if (golayBasis 0).val i = 0 then
      ((x.val i + (if (golayBasis 0).val i = 0 then x.val i else -x.val i) : ℤ) : ℚ)
      else -((x.val i + (if (golayBasis 0).val i = 0 then x.val i else -x.val i) : ℤ) : ℚ)) =
      ((x.val i + (if (golayBasis 0).val i = 0 then x.val i else -x.val i) : ℤ) : ℚ)
    split_ifs <;> simp
  have hu := congrArg (fun f : ComplementSpace ≃ₗ[ℚ] ComplementSpace =>
    complementEmbedding (f (complementProjection (rationalEmbedding (x + sign.val x).val)))) hg
  change complementEmbedding (complementAction g.val
    (complementProjection (rationalEmbedding (x + sign.val x).val))) =
      complementEmbedding (complementProjection (rationalEmbedding (x + sign.val x).val)) at hu
  rw [complementAction_intertwines, embedding_projection_of_fixed hplus,
    ambientAction_agrees] at hu
  have hu' : g.val.val.val (x + sign.val x) = x + sign.val x :=
    Subtype.ext (rationalEmbedding_injective hu)
  rw [map_add] at hu'
  rw [map_sub] at hv
  apply Subtype.ext
  funext i
  have hu'' := congrArg (fun y : leech => y.val i) hu'
  have hv' := congrArg (fun y : leech => y.val i) hv
  change (g.val.val.val x).val i + (g.val.val.val (sign.val x)).val i =
    x.val i + (sign.val x).val i at hu''
  change (g.val.val.val x).val i - (g.val.val.val (sign.val x)).val i =
    x.val i - (sign.val x).val i at hv'
  change (g.val.val.val x).val i = x.val i
  omega

theorem ambientAction_complementSign (x : RationalCoordinates) :
    ambientAction complementSign x = -rationalSign x := by
  have h : (ambientAction complementSign).toLinearMap = -rationalSign := by
    apply rationalLeechBasis.ext
    intro i
    rw [rationalLeechBasis_apply]
    change ambientAction complementSign (rationalEmbedding (leechBasis i).val) =
      -rationalSign (rationalEmbedding (leechBasis i).val)
    rw [ambientAction_agrees, complementSign_apply, Submodule.coe_neg, map_neg,
      rationalSign_eq]
    exact congrArg Neg.neg (rationalExtension_agrees sign.val (leechBasis i)).symm
  exact LinearMap.congr_fun h x

theorem complementAction_complementSign (x : ComplementSpace) :
    complementAction complementSign x = -x := by
  apply complementEmbedding_injective
  rw [complementAction_intertwines, ambientAction_complementSign,
    rationalSign_embedding, map_neg]

theorem kernel_center_negation (hQ : IsExtraspecial 2 action.ker)
    (z : Subgroup.center action.ker) (hz : z.val ≠ 1) (x : ComplementSpace) :
    complementAction z.val.val x = -x := by
  rw [(kernel_center_cases hQ z).resolve_left hz]
  exact complementAction_complementSign x

def complementRepresentation : centralizer →* Module.End ℚ ComplementSpace :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp complementAction

def kernelRepresentation : action.ker →* Module.End ℚ ComplementSpace :=
  complementRepresentation.comp action.ker.subtype

theorem kernelRepresentation_injective : Function.Injective kernelRepresentation := by
  intro q s h
  apply kernel_complementAction_injective
  exact LinearEquiv.toLinearMap_injective h

theorem kernelRepresentation_center (hQ : IsExtraspecial 2 action.ker)
    (z : Subgroup.center action.ker) (hz : z.val ≠ 1) :
    kernelRepresentation z.val = -1 := by
  apply LinearMap.ext
  intro x
  exact kernel_center_negation hQ z hz x

theorem kernelRepresentation_conjugation (r : centralizer) (q : action.ker) :
    kernelRepresentation (MulAut.conjNormal r q) =
      (complementAction r).conj (kernelRepresentation q) := by
  apply LinearMap.ext
  intro x
  change complementAction (r * q.val * r⁻¹) x =
    complementAction r (complementAction q.val ((complementAction r).symm x))
  simp only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv]

theorem complementAction_cube {r : centralizer} (hr : orderOf r = 3) :
    complementAction r ^ 3 = 1 := by
  rw [← map_pow, ← hr, pow_orderOf_eq_one, map_one]

theorem complementRepresentation_trace_of_polynomial {r : centralizer} (ho : orderOf r = 3)
    (hr : ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0) :
    LinearMap.trace ℚ ComplementSpace (complementRepresentation r) = -8 :=
  complementAction_trace_of_polynomial ho hr

theorem complementAction_conjugation_trace {r : centralizer} (ho : orderOf r = 3)
    (hr : ∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0) :
    LinearMap.trace ℚ (Module.End ℚ ComplementSpace) (complementAction r).conj.toLinearMap = 64 := by
  have h := Representation.char_linHom complementRepresentation complementRepresentation r
  have he : Representation.linHom complementRepresentation complementRepresentation r =
      (complementAction r).conj.toLinearMap := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    change complementAction r (f (complementAction r⁻¹ x)) =
      complementAction r (f ((complementAction r).symm x))
    rw [map_inv, LinearEquiv.coe_inv]
  simp only [Representation.character, he] at h
  change LinearMap.trace ℚ (Module.End ℚ ComplementSpace) (complementAction r).conj.toLinearMap =
    LinearMap.trace ℚ ComplementSpace (complementAction r⁻¹).toLinearMap *
      LinearMap.trace ℚ ComplementSpace (complementAction r).toLinearMap at h
  rw [complementAction_trace_inv, complementAction_trace_of_polynomial ho hr] at h
  norm_num at h
  exact h

end PolynomialSelection
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
