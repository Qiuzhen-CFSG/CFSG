module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Exterior
public import Theory.Representation.MathieuCodeRestriction.Duality.Absolute

/-!
# The native Golay exterior contraction

Coordinatewise multiplication of two Golay words lies in the even core by
self-orthogonality. Modulo Golay it is unchanged when either argument changes
by a constant word, and it vanishes on the diagonal. It therefore induces an
M24-equivariant map from the exterior square of the code to the cocode.
A triple intersection of native rows shows the map is nonzero; irreducibility
of the cocode makes it surjective. Its literal invariant kernel has dimension
44. No irreducibility of this kernel is asserted here.

This constructs a candidate for the degree-44 factors in James, The modular
characters of the Mathieu groups, J. Algebra 27 (1973), 57--111, used in the
M24 case of GM02, Proposition 5.1, manuscript p.17.
-/

@[expose] public section
open Sporadic.Mathieu MathieuCode Representation
open Representation.MathieuM24Degree44.FiveSpace
open scoped BigOperators
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour

/-- Coordinatewise intersection of two Golay words, in the even core. -/
def productCore (v w : golay) : Core :=
  ⟨fun i => v.val i * w.val i, golay_le_orthogonal w.property v.val v.property⟩

def rawProduct : golay →ₗ[ZMod 2] golay →ₗ[ZMod 2] Cocode :=
  LinearMap.mk₂ (ZMod 2) (fun v w => codeInCore.mkQ (productCore v w))
    (by intro v v' w; rw [← map_add]; congr 1; ext i; exact add_mul _ _ _)
    (by intro c v w; rw [← map_smul]; congr 1; ext i; exact mul_assoc _ _ _)
    (by intro v w w'; rw [← map_add]; congr 1; ext i; exact mul_add _ _ _)
    (by intro c v w; rw [← map_smul]; congr 1; ext i; exact mul_left_comm _ _ _)

theorem rawProduct_comm (v w : golay) : rawProduct v w = rawProduct w v := by
  change codeInCore.mkQ _ = codeInCore.mkQ _
  congr 1
  ext i
  exact mul_comm _ _

theorem rawProduct_line : codeLine ≤ rawProduct.ker := by
  intro v hv
  apply LinearMap.ext
  intro w
  apply (Submodule.Quotient.mk_eq_zero codeInCore).mpr
  change (fun i => v.val i * w.val i) ∈ golay
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have he : (fun i => v.val i * w.val i) = c • w.val := by
    funext i
    have hi := congrFun hc i
    change c * 1 = v.val i at hi
    simp only [mul_one] at hi
    simp only [← hi, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact golay.smul_mem c w.property

/-- Coordinatewise product on the two actual code quotients, modulo Golay. -/
def product : Code →ₗ[ZMod 2] Code →ₗ[ZMod 2] Cocode :=
  rawProduct.liftQ₂ codeLine codeLine rawProduct_line (by
    intro v hv
    ext w
    change rawProduct w v = 0
    rw [rawProduct_comm]
    exact LinearMap.congr_fun (rawProduct_line hv) w)

theorem product_self (v : Code) : product v v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    apply (Submodule.Quotient.mk_eq_zero codeInCore).mpr
    change (fun i => v.val i * v.val i) ∈ golay
    have he : (fun i => v.val i * v.val i) = v.val := by
      funext i
      have h : ∀ a : ZMod 2, a * a = a := by decide
      exact h _
    rw [he]
    exact v.property

def productAlternating : Code [⋀^Fin 2]→ₗ[ZMod 2] Cocode where
  toFun v := product (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [map_add]
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change product (v 0) (v 1) = 0
      change v 0 = v 1 at h
      rw [h]
      exact product_self _
    · change product (v 0) (v 1) = 0
      change v 1 = v 0 at h
      rw [h]
      exact product_self _
    · exact (hij rfl).elim

def contractionLinear : (⋀[ZMod 2]^2 Code) →ₗ[ZMod 2] Cocode :=
  exteriorPower.alternatingMapLinearEquiv productAlternating

theorem product_equivariant (g : M24) (v w : Code) :
    product (codeRepresentation g v) (codeRepresentation g w) =
      cocodeRepresentation g (product v w) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    induction w using Submodule.Quotient.induction_on with
    | _ w => rfl

/-- The native equivariant exterior contraction onto the cocode. -/
def contraction : codeExterior.IntertwiningMap cocodeRepresentation where
  toLinearMap := contractionLinear
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    change contractionLinear (exteriorPower.map 2 (codeRepresentation g)
      (exteriorPower.ιMulti (ZMod 2) 2 v)) =
      cocodeRepresentation g (contractionLinear (exteriorPower.ιMulti (ZMod 2) 2 v))
    simp only [contractionLinear, exteriorPower.map_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact product_equivariant g (v 0) (v 1)

theorem contraction_ne_zero : contraction ≠ 0 := by
  intro h
  have hz := congrArg (fun f : codeExterior.IntertwiningMap cocodeRepresentation =>
    f (exteriorPower.ιMulti (ZMod 2) 2
      ![codeLine.mkQ ⟨row 0, row_mem 0⟩, codeLine.mkQ ⟨row 1, row_mem 1⟩])) h
  change contractionLinear _ = 0 at hz
  rw [contractionLinear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at hz
  have hm := (Submodule.Quotient.mk_eq_zero codeInCore).mp hz
  have hp := golay_le_orthogonal hm _ (row_mem 3)
  have hn : dotForm (row 3) (fun i => row 0 i * row 1 i) ≠ 0 := by decide +kernel
  exact hn hp

theorem contraction_surjective : Function.Surjective contraction := by
  let : cocodeRepresentation.IsIrreducible := cocode_isIrreducible
  exact (IsIrreducible.surjective_or_eq_zero contraction).resolve_right contraction_ne_zero

/-- The literal 44-dimensional invariant subspace of the code exterior square. -/
def kernel : Subrepresentation codeExterior := contraction.ker

abbrev Kernel := kernel.toSubmodule

/-- The original M24 action restricted to the contraction kernel. -/
def kernelRepresentation : Representation (ZMod 2) M24 Kernel := kernel.toRepresentation

theorem finrank_kernel : Module.finrank (ZMod 2) Kernel = 44 := by
  have h := contractionLinear.finrank_range_add_finrank_ker
  have hs : Function.Surjective contractionLinear := contraction_surjective
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_cocode,
    finrank_codeExterior] at h
  change 11 + Module.finrank (ZMod 2) Kernel = 55 at h
  omega

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
