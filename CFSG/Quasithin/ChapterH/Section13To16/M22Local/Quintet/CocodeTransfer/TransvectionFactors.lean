module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Quintet.CocodeTransfer
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Quintet.CocodeTransfer.TransvectionFactors.ChiefFactors
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Quintet.CocodeTransfer.TransvectionFactors.Hyperplanes

/-!
# The transvection and displacement-pairing branch of H.15.4

These adapters retain the literal pair quotient, intrinsic fixed spaces,
relative conjugation action, and the complete action image. The imported
chief-factor and hyperplane adapters prove chiefness and the universal fixed
dimension from the earlier H.14 conjugation-module structure and one marked
outer involution. The common-four calculation also supplies generation and xi.

All earlier M24, H.14 and involution data remain explicit. Top-section
irreducibility is the permitted intermediate input to be supplied by the S5
marking branch. This completes the conditional transvection branch, while
the natural S5 marking and final H.15.4 assembly remain separate.

Source: Aschbacher--Smith H.15.4, printed p.400, manuscript of 1 March 2004.
-/

public section
noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode MathieuCode.M22Quintet Representation.BinaryOffender
open MathieuCode.M22Quintet.CocodeTransfer

/-- H.15.3(2) transfers to a faithful, full action on the literal V6. -/
theorem m22Quintet_faithful_full_transvections (D : SextetTransvectionInputs) :
    Function.Injective DualAction.cocodeKernelAction ∧
      DualAction.cocodeKernelAction.range = BinaryLinear.radical (V1.comap V6.subtype) :=
  ⟨kernelAction_faithful D, kernelAction_full_intrinsic D⟩

/-- The middle section is genuinely the dual of the conjugation module K. -/
def m22Quintet_middle_duality [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) :
    (V6 ⧸ (V1.comap V6.subtype)) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive K) :=
  middleDuality D

theorem m22Quintet_middle_duality_equivariant [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (g : Q) (v : V6 ⧸ (V1.comap V6.subtype)) :
    m22Quintet_middle_duality D ((centerSubrepresentation D).quotientRepresentation g v) =
      kernelConjugation.dual g (m22Quintet_middle_duality D v) :=
  middleDuality_equivariant D g v

/-- The intrinsic fixed spaces have the stated dimensions and form the strict flag. -/
theorem m22Quintet_strict_flag_of_transvections [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation] :
    W1 = V1 ∧ V1 ≤ V2 ∧ V2 ≤ V6 ∧
    Module.finrank (ZMod 2) V1 = 1 ∧ Module.finrank (ZMod 2) V2 = 2 ∧
    Module.finrank (ZMod 2) V6 = 6 ∧
    (⊥ : Submodule (ZMod 2) M22Cocode) < V1 ∧ V1 < V2 ∧ V2 < V6 ∧ V6 < ⊤ :=
  ⟨W1_eq_V1 D I, V1_le_V2, V2_le_V6 D I, finrank_V1 D I, finrank_V2 D I,
    finrank_V6, cocode_flag_strict D I⟩

/-- The source common-four dimension in U7 is derived, not assumed. -/
theorem m22Quintet_common_four_middle_dimension (D : SextetTransvectionInputs)
    [IsElementaryAbelian 2 E24] (hcard : Nat.card E24 = 4) :
    Module.finrank (ZMod 2)
      (fixedSpace cocodeRepresentation E24 ⊓ U7 : Submodule (ZMod 2) Cocode) = 5 :=
  finrank_common_middle_fixed D hcard

/-- The source involution forces every fixed vector of its hyperplane into V6. -/
theorem m22Quintet_hyperplane_dimension_of_involution [IsElementaryAbelian 2 K]
    (D : SextetTransvectionInputs) (A : Subgroup m22PairStabilizer)
    (hA : A ≤ K) (hi : A.relIndex K = 2)
    (i : m22PairStabilizer) (hia : i ∈ A) (ho : orderOf i = 2)
    (hfix : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i)) = 5) :
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 :=
  finrank_fixed_hyperplane_of_involution D A hA hi i hia ho hfix

/-- H.15.4(3--4) follows with no assumed hyperplane witnesses or hyperplane fixed dimensions.
The common-four ambient dimension is the earlier H.15.2(5) input. -/
theorem m22Quintet_cocode_generation_and_hyperplanes
    [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs)
    [Representation.IsIrreducible (innerConjugation I)]
    [Representation.IsIrreducible V6Subrepresentation.quotientRepresentation]
    (hindecomp : ∀ U W : Subrepresentation kernelConjugation,
      IsCompl U W → U = ⊥ ∨ W = ⊥)
    (i0 : m22PairStabilizer) (hi0 : i0 ∈ K) (hout : i0 ∉ L)
    (horder : orderOf i0 = 2)
    (hfixed : Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i0)) = 5)
    (hEK : E ≤ K) (hE : IsElementaryAbelian 2 E) (hcard : Nat.card E = 4)
    [IsElementaryAbelian 2 E24] (hcard24 : Nat.card E24 = 4)
    (hcommon : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation E24) = 6) :
    fourFixedSpan m22OuterCocodeRepresentation K = ⊤ ∧
      ∀ A : Subgroup m22PairStabilizer, A ≤ K → A.relIndex K = 2 →
        fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ ∧
          Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 :=
  cocode_generation_and_hyperplane_fixed_dimensions D I hindecomp i0 hi0 hout horder
    hfixed hEK hE hcard hcard24 hcommon

end CFSG.Quasithin.ChapterH.Section13To16
