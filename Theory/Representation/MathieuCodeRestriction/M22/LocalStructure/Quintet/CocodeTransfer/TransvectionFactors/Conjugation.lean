module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Duality
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Flag

/-!
# The actual quintet conjugation modules and their inclusion

The canonical A0 = K ∩ L is elementary abelian and embeds linearly in
Additive K. Its conjugation action and this inclusion use ambient conjugation
inside the pair stabilizer, with normality only relative to Q. The H.14 orders
give dimensions four and five. Irreducibility and indecomposability of these
actual actions are earlier H.14 inputs, not consequences of their dimensions.

These shared definitions support the lower chief factors and hyperplane
involution-selection arguments in Aschbacher--Smith H.15.4, printed p.400.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
namespace MathieuCode.M22Quintet.CocodeTransfer

instance innerElementary [IsElementaryAbelian 2 K] : IsElementaryAbelian 2 A0 where
  is_comm := ⟨fun a b => Subtype.ext (congrArg (fun k : K => k.val)
    (mul_comm (⟨a.val,a.property.1⟩ : K) ⟨b.val,b.property.1⟩))⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun a =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a.val a.property.1))

def innerConjugation [IsElementaryAbelian 2 K] (I : InnerInputs) :
    Representation (ZMod 2) Q (Additive A0) :=
  Representation.BinaryInternalFixedSpaceCodimension.representation A0 Q I.normalizer

@[simp] theorem innerConjugation_apply [IsElementaryAbelian 2 K] (I : InnerInputs)
    (g : Q) (a : Additive A0) :
    ((innerConjugation I g a).toMul : m22PairStabilizer) =
      g.val * a.toMul.val * g.val⁻¹ := rfl

def innerInclusion [IsElementaryAbelian 2 K] : Additive A0 →ₗ[ZMod 2] Additive K :=
  (Subgroup.inclusion (show A0 ≤ K from inf_le_left)).toAdditive.toZModLinearMap 2

theorem innerInclusion_injective [IsElementaryAbelian 2 K] :
    Function.Injective innerInclusion := by
  intro a b he
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun k : Additive K => k.toMul.val) he

theorem innerInclusion_equivariant [IsElementaryAbelian 2 K] (I : InnerInputs)
    (g : Q) (a : Additive A0) :
    innerInclusion (innerConjugation I g a) = kernelConjugation g (innerInclusion a) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rfl

def innerSubrepresentation [IsElementaryAbelian 2 K] (I : InnerInputs) :
    Subrepresentation kernelConjugation where
  toSubmodule := innerInclusion.range
  apply_mem_toSubmodule g v hv := by
    obtain ⟨a,rfl⟩ := hv
    exact ⟨innerConjugation I g a, innerInclusion_equivariant I g a⟩

theorem finrank_kernel [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) :
    Module.finrank (ZMod 2) (Additive K) = 5 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive K)
  simpa only [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive K ≃ K), D.card_kernel]
    using hc.symm

theorem finrank_inner [IsElementaryAbelian 2 K] (D : SextetTransvectionInputs) (I : InnerInputs) :
    Module.finrank (ZMod 2) (Additive A0) = 4 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A0)
  simpa only [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive A0 ≃ A0),
    card_hyperplane D A0 inf_le_left I.index] using hc.symm

end MathieuCode.M22Quintet.CocodeTransfer
