module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.CocodeTransfer.TransvectionFactors.Conjugation
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Sections

/-!
# Chief factors of the canonical outer M22 cocode flag

Restricting the native displacement pairing to A0 = K ∩ L gives a surjective
Q-equivariant map from V6 onto the dual of the actual A0 conjugation module.
Its kernel is exactly V2 inside V6. Thus earlier H.14 irreducibility of A0
proves irreducibility of the literal four-dimensional quotient V6/V2.
The two one-dimensional factors and the earlier top-section irreducibility
then give all four covers in the lattice of Q-invariant subspaces.

The section and cover lemmas are reused from the hexad development; their
statements are general representation-theoretic lemmas. Normality throughout
is relative to Q. No middle-factor irreducibility or chief flag is assumed.

Source: Aschbacher--Smith H.15.4(1), printed p.400, using H.14.3(2),
printed p.397, manuscript of 1 March 2004. This is a conditional deduction
from the explicit earlier transvection, inner-kernel and top-section inputs.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
open Representation
namespace MathieuCode.M22Quintet.CocodeTransfer
open DualAction BinaryTransvectionGroups.LineAction
open MathieuCode.Hexad.ChiefFlag.Actions (sectionSubrepresentation covBy_of_finrank
  covBy_of_irreducible_section irreducible_section_of_covBy irreducible_transport eq_ker_or_top)

private theorem irreducible_dual {F G X : Type*} [Field F] [Group G]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (ρ : Representation F G X) [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial X := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

variable [IsElementaryAbelian 2 K]

/-- Restriction of the actual middle displacement pairing to the inner kernel. -/
def innerPairing (D : SextetTransvectionInputs) :
    V6 →ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive A0) :=
  innerInclusion.dualMap.comp
    ((middleDuality D).toLinearMap.comp (V1.comap V6.subtype).mkQ)

@[simp] theorem innerPairing_apply (D : SextetTransvectionInputs) (v : V6) (a : Additive A0) :
    innerPairing D v a =
      form cocodeKernelAction (V1.comap V6.subtype) (centerCoordinate D)
        (kernelAction_mem_intrinsicRadical D) (innerInclusion a).toMul v := rfl

theorem innerPairing_surjective (D : SextetTransvectionInputs) :
    Function.Surjective (innerPairing D) :=
  (LinearMap.dualMap_surjective_of_injective innerInclusion_injective).comp
    ((middleDuality D).surjective.comp (V1.comap V6.subtype).mkQ_surjective)

theorem innerPairing_ker (D : SextetTransvectionInputs) :
    (innerPairing D).ker = V2.comap V6.subtype := by
  ext v
  constructor
  · intro hv a
    have hz := LinearMap.congr_fun (show innerPairing D v = 0 from hv) (Additive.ofMul a)
    have hf := (form_eq_zero_iff cocodeKernelAction (V1.comap V6.subtype)
      (centerCoordinate D) (kernelAction_mem_intrinsicRadical D)
      (innerInclusion (Additive.ofMul a)).toMul v).mp hz
    exact congrArg Subtype.val hf
  · intro hv
    apply LinearMap.ext
    intro a
    apply (form_eq_zero_iff cocodeKernelAction (V1.comap V6.subtype)
      (centerCoordinate D) (kernelAction_mem_intrinsicRadical D)
      (innerInclusion a).toMul v).mpr
    apply Subtype.ext
    exact hv a.toMul

theorem innerPairing_equivariant (D : SextetTransvectionInputs) (I : InnerInputs)
    (g : Q) (v : V6) :
    innerPairing D (V6Subrepresentation.toRepresentation g v) =
      (innerConjugation I).dual g (innerPairing D v) := by
  have he := middleDuality_equivariant D g ((V1.comap V6.subtype).mkQ v)
  apply LinearMap.ext
  intro a
  change middleDuality D ((centerSubrepresentation D).quotientRepresentation g
      ((V1.comap V6.subtype).mkQ v)) (innerInclusion a) =
    middleDuality D ((V1.comap V6.subtype).mkQ v)
      (innerInclusion (innerConjugation I g⁻¹ a))
  rw [he, innerInclusion_equivariant]
  rfl

/-- The literal inner fixed subspace inside V6, with its inherited Q action. -/
def innerFixedSubrepresentation (I : InnerInputs) :
    Subrepresentation V6Subrepresentation.toRepresentation :=
  sectionSubrepresentation (V2Subrepresentation I) V6Subrepresentation

/-- Restriction identifies the four-dimensional factor with the dual of actual A0. -/
def innerFactorDuality (D : SextetTransvectionInputs) :
    (V6 ⧸ (V2.comap V6.subtype)) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive A0) :=
  (Submodule.quotEquivOfEq _ _ (innerPairing_ker D).symm).trans
    ((innerPairing D).quotKerEquivOfSurjective (innerPairing_surjective D))

@[simp] theorem innerFactorDuality_mk (D : SextetTransvectionInputs) (v : V6) :
    innerFactorDuality D ((V2.comap V6.subtype).mkQ v) = innerPairing D v := rfl

theorem innerFactorDuality_equivariant (D : SextetTransvectionInputs) (I : InnerInputs)
    (g : Q) (v : V6 ⧸ (V2.comap V6.subtype)) :
    innerFactorDuality D ((innerFixedSubrepresentation I).quotientRepresentation g v) =
      (innerConjugation I).dual g (innerFactorDuality D v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact innerPairing_equivariant D I g v

theorem finrank_innerFactor (D : SextetTransvectionInputs) (I : InnerInputs) :
    Module.finrank (ZMod 2) (V6 ⧸ (V2.comap V6.subtype)) = 4 := by
  rw [(innerFactorDuality D).finrank_eq, Subspace.dual_finrank_eq, finrank_inner D I]

theorem innerFactor_irreducible (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsIrreducible (innerConjugation I)] :
    IsIrreducible (innerFixedSubrepresentation I).quotientRepresentation :=
  irreducible_transport _ (innerConjugation I).dual (MonoidHom.id Q)
    Function.surjective_id (innerFactorDuality D) (innerFactorDuality_equivariant D I)
    (irreducible_dual (innerConjugation I))

/-- The canonical ambient fixed line with its inherited Q action. -/
def V1Subrepresentation (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsIrreducible V6Subrepresentation.quotientRepresentation] :
    Subrepresentation cocodeAction where
  toSubmodule := V1
  apply_mem_toSubmodule g v hv := by
    rw [← W1_eq_V1 D I] at hv ⊢
    rw [show cocodeAction g v = v from W1_fixed g v hv]
    exact hv

def firstSection (D : SextetTransvectionInputs) (I : InnerInputs)
    [IsIrreducible V6Subrepresentation.quotientRepresentation] :
    Subrepresentation (V2Subrepresentation I).toRepresentation :=
  sectionSubrepresentation (V1Subrepresentation D I) (V2Subrepresentation I)

variable (D : SextetTransvectionInputs) (I : InnerInputs)
  [IsIrreducible V6Subrepresentation.quotientRepresentation]
  [IsIrreducible (innerConjugation I)]

theorem cocode_chief_covers :
    (⊥ : Subrepresentation cocodeAction) ⋖ V1Subrepresentation D I ∧
    V1Subrepresentation D I ⋖ V2Subrepresentation I ∧
    V2Subrepresentation I ⋖ V6Subrepresentation ∧
    V6Subrepresentation ⋖ (⊤ : Subrepresentation cocodeAction) := by
  have hs := cocode_flag_strict D I
  refine ⟨covBy_of_finrank bot_le ?_, covBy_of_finrank V1_le_V2 ?_,
    covBy_of_irreducible_section (show V2Subrepresentation I < V6Subrepresentation from hs.2.2.1)
      (innerFactor_irreducible D I), ?_⟩
  · change Module.finrank (ZMod 2) V1 =
      Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) M22Cocode) + 1
    rw [finrank_bot, finrank_V1 D I]
  · change Module.finrank (ZMod 2) V2 = Module.finrank (ZMod 2) V1 + 1
    rw [finrank_V2 D I, finrank_V1 D I]
  · refine ⟨(show V6Subrepresentation < (⊤ : Subrepresentation cocodeAction) from hs.2.2.2), ?_⟩
    intro P h6P hPtop
    rcases eq_ker_or_top cocodeAction V6Subrepresentation.quotientRepresentation V6Subrepresentation.toSubmodule.mkQ
      (fun _ _ => rfl) inferInstance P (by rw [Submodule.ker_mkQ]; exact h6P.le) with h | h
    · rw [Submodule.ker_mkQ] at h
      exact h6P.ne (Subrepresentation.toSubmodule_injective h).symm
    · exact hPtop.ne (Subrepresentation.toSubmodule_injective h)

/-- The canonical flag with all four covers proved for the actual Q action. -/
def cocodeChiefFlag : CocodeFlag where
  one := V1Subrepresentation D I
  two := V2Subrepresentation I
  one_eq := rfl
  two_eq := rfl
  chief01 := (cocode_chief_covers D I).1
  chief12 := (cocode_chief_covers D I).2.1
  chief26 := (cocode_chief_covers D I).2.2.1
  chief6top := (cocode_chief_covers D I).2.2.2
  dim1 := finrank_V1 D I
  dim2 := finrank_V2 D I
  dim6 := finrank_V6

/-- Irreducibility of each literal subspace or quotient action in the chief flag. -/
theorem cocode_chief_factors_irreducible :
    IsIrreducible (V1Subrepresentation D I).toRepresentation ∧
    IsIrreducible (firstSection D I).quotientRepresentation ∧
    IsIrreducible (innerFixedSubrepresentation I).quotientRepresentation ∧
    IsIrreducible V6Subrepresentation.quotientRepresentation := by
  have hc := cocode_chief_covers D I
  exact ⟨(Subrepresentation.irreducible_iff_isAtom _).mpr (bot_covBy_iff.mp hc.1),
    irreducible_section_of_covBy hc.2.1, innerFactor_irreducible D I, inferInstance⟩

end MathieuCode.M22Quintet.CocodeTransfer
