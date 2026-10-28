module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Actions
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action

/-!
# The native quintet displacement duality

The actual displacement pairing identifies V6/V1 with the dual of Additive K.
Conjugating the acting transvection transports its displacement form by the
inverse action. This proves equivariance for conjugation inside Q; K is not
assumed normal in the whole pair stabilizer. The pairing never replaces K by
a permutation module on the basis of its dimension.

Source: Aschbacher--Smith H.15.4(1--2), printed p.400, using H.15.3(2).
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace MathieuCode.M22Quintet.CocodeTransfer
open DualAction BinaryTransvectionGroups.LineAction

/-- The literal Q action on Additive K is conjugation in the pair stabilizer. -/
def kernelConjugation [IsElementaryAbelian 2 K] :
    Representation (ZMod 2) Q (Additive K) :=
  Representation.BinaryInternalFixedSpaceCodimension.representation K Q Q_le_normalizer_K

@[simp] theorem kernelConjugation_apply [IsElementaryAbelian 2 K] (g : Q) (k : Additive K) :
    ((kernelConjugation g k).toMul : m22PairStabilizer) =
      g.val * k.toMul.val * g.val⁻¹ := rfl

/-- The intrinsic center, with the actual induced Q action. -/
def centerSubrepresentation (D : SextetTransvectionInputs) :
    Subrepresentation V6Subrepresentation.toRepresentation where
  toSubmodule := V1.comap V6.subtype
  apply_mem_toSubmodule g v hv := by
    have hw := (middle_fixed_eq_geometricCenter D).le hv
    apply (middle_fixed_eq_geometricCenter D).ge
    change m22OuterCocodeRepresentation g.val v.val ∈ W1
    rw [W1_fixed g v.val hw]
    exact hw

def centerCoordinate (D : SextetTransvectionInputs) :
    (V1.comap V6.subtype) ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [middle_fixed_eq_geometricCenter D, finrank_geometricCenter, Module.finrank_self])

theorem intrinsicCenter_ne_bot (D : SextetTransvectionInputs) : V1.comap V6.subtype ≠ ⊥ := by
  rw [middle_fixed_eq_geometricCenter D]
  intro he
  have hd := finrank_geometricCenter
  rw [he, finrank_bot] at hd
  omega

theorem kernelAction_mem_intrinsicRadical (D : SextetTransvectionInputs) (k : K) :
    cocodeKernelAction k ∈ BinaryLinear.radical (V1.comap V6.subtype) := by
  rw [middle_fixed_eq_geometricCenter D]
  exact kernelAction_mem_radical D k

/-- Evaluation of actual displacements, not a dimension-only module identification. -/
def middleDuality [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) :
    (V6 ⧸ (V1.comap V6.subtype)) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive K) :=
  quotientDuality cocodeKernelAction (V1.comap V6.subtype) (centerCoordinate D)
    (kernelAction_mem_intrinsicRadical D) (kernelAction_faithful D)
    (intrinsicCenter_ne_bot D) (kernelAction_full_intrinsic D)

theorem middleDuality_equivariant [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs)
    (g : Q) (v : V6 ⧸ (V1.comap V6.subtype)) :
    middleDuality D ((centerSubrepresentation D).quotientRepresentation g v) =
      kernelConjugation.dual g (middleDuality D v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    apply LinearMap.ext
    intro k
    change form cocodeKernelAction (V1.comap V6.subtype) (centerCoordinate D)
        (kernelAction_mem_intrinsicRadical D) k.toMul
        (linearAction V6Subrepresentation.toRepresentation g v) =
      form cocodeKernelAction (V1.comap V6.subtype) (centerCoordinate D)
        (kernelAction_mem_intrinsicRadical D) (kernelConjugation g⁻¹ k).toMul v
    apply form_intertwines
    · intro w hw
      apply Subtype.ext
      exact W1_fixed g w.val ((middle_fixed_eq_geometricCenter D).le hw)
    · change linearAction V6Subrepresentation.toRepresentation (kernelInclusion k.toMul) *
          linearAction V6Subrepresentation.toRepresentation g =
        linearAction V6Subrepresentation.toRepresentation g *
          linearAction V6Subrepresentation.toRepresentation
            (kernelInclusion (kernelConjugation g⁻¹ k).toMul)
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change k.toMul.val * g.val = g.val * (g.val⁻¹ * k.toMul.val * g.val)
      group

end MathieuCode.M22Quintet.CocodeTransfer
