module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.Spectrum.Averaging
public import Theory.Representation.BinaryPermutation.OrbitFixedSpace

/-!
# Fixed dimensions of the native Mathieu quotients at odd order

Odd-order averaging makes fixed dimensions additive on the native filtration
constant line ≤ Golay code ≤ even-weight core ≤ full permutation module.
The published cyclic code–cocode duality identifies the two middle quotient
fixed dimensions. Consequently the fixed Golay dimension is half the number
of point orbits, and the cocode fixed dimension is one less than that half.

Source: Aschbacher–Smith, H.13, printed pp.395–396, and H.15.7,
printed pp.401–402. No Mathieu conjugacy or fixed-point table is assumed.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender
namespace MathieuCode

private def nativeCore : Subrepresentation fullRepresentation where
  toSubmodule := BinaryPermutation.core (Fin 24)
  apply_mem_toSubmodule g := fun {_v} hv => BinaryPermutation.core_invariant (Fin 24) g.val hv

theorem finrank_core_fixed_add_one (D : Subgroup M24) (ho : Odd (Nat.card D)) :
    Module.finrank (ZMod 2) (fixedSpace coreRepresentation D) + 1 =
      Module.finrank (ZMod 2) (fixedSpace fullRepresentation D) := by
  have h := finrank_fixedSpace_surjection_of_odd fullRepresentation
    (Representation.trivial (ZMod 2) M24 (ZMod 2))
    (BinaryPermutation.augmentation (Fin 24))
    (fun g v => BinaryPermutation.augmentation_permute (Fin 24) g.val v)
    (BinaryPermutation.augmentation_surjective (Fin 24)) D ho
  have ht : fixedSpace (Representation.trivial (ZMod 2) M24 (ZMod 2)) D = ⊤ := by
    ext v
    change (∀ a : D, v = v) ↔ True
    simp
  rw [ht, finrank_top, Module.finrank_self] at h
  have he := (subrepresentationFixedEquiv fullRepresentation nativeCore D).finrank_eq
  change Module.finrank (ZMod 2) (fixedSpace coreRepresentation D) =
    Module.finrank (ZMod 2) ((BinaryPermutation.augmentation (Fin 24)).ker ⊓
      fixedSpace fullRepresentation D : Submodule (ZMod 2) Full) at he
  omega

theorem finrank_golay_fixed_eq_code_add_one (D : Subgroup M24) (ho : Odd (Nat.card D)) :
    Module.finrank (ZMod 2) (fixedSpace golayRepresentation D) =
      Module.finrank (ZMod 2) (fixedSpace codeRepresentation D) + 1 := by
  have h := finrank_fixedSpace_quotient_of_odd golayRepresentation codeLineSubrepresentation D ho
  have ht : fixedSpace codeLineSubrepresentation.toRepresentation D = ⊤ := by
    apply top_unique
    intro v _ a
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨c, hc⟩ := (BinaryPermutation.mem_constants_iff v.val.val).mp v.property
    funext i
    change v.val.val (a.val.val.symm i) = v.val.val i
    rw [hc, hc]
  rw [ht, finrank_top] at h
  change Module.finrank (ZMod 2) (fixedSpace codeRepresentation D) +
    Module.finrank (ZMod 2) codeLine = _ at h
  rw [finrank_codeLine] at h
  exact h.symm

theorem finrank_core_fixed_eq_cocode_add_golay (D : Subgroup M24) (ho : Odd (Nat.card D)) :
    Module.finrank (ZMod 2) (fixedSpace coreRepresentation D) =
      Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) +
      Module.finrank (ZMod 2) (fixedSpace golayRepresentation D) := by
  have h := finrank_fixedSpace_quotient_of_odd coreRepresentation codeInCoreSubrepresentation D ho
  let e : codeInCore ≃ₗ[ZMod 2] golay := Submodule.comapSubtypeEquivOfLe golay_le_core
  let ef : fixedSpace codeInCoreSubrepresentation.toRepresentation D ≃ₗ[ZMod 2]
      fixedSpace golayRepresentation D :=
    { toFun := fun v => ⟨e v.val, fun a => congrArg e (v.property a)⟩
      invFun := fun v => ⟨e.symm v.val, fun a => congrArg e.symm (v.property a)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he := ef.finrank_eq
  change Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) + _ = _ at h
  omega

theorem twice_cocode_fixed_add_two (D : Subgroup M24) [IsCyclic D]
    (ho : Odd (Nat.card D)) :
    2 * (Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) + 1) =
      Module.finrank (ZMod 2) (fixedSpace fullRepresentation D) := by
  have := finrank_core_fixed_add_one D ho
  have := finrank_golay_fixed_eq_code_add_one D ho
  have := finrank_core_fixed_eq_cocode_add_golay D ho
  have := code_cocode_fixed_finrank_cyclic D
  omega

theorem twice_golay_fixed (D : Subgroup M24) [IsCyclic D] (ho : Odd (Nat.card D)) :
    2 * Module.finrank (ZMod 2) (fixedSpace golayRepresentation D) =
      Module.finrank (ZMod 2) (fixedSpace fullRepresentation D) := by
  have := twice_cocode_fixed_add_two D ho
  have := finrank_golay_fixed_eq_code_add_one D ho
  have := code_cocode_fixed_finrank_cyclic D
  omega

theorem finrank_full_fixed_eq_orbits (D : Subgroup M24) :
    Module.finrank (ZMod 2) (fixedSpace fullRepresentation D) =
      Nat.card (MulAction.orbitRel.Quotient D (Fin 24)) := by
  have he : fixedSpace fullRepresentation D =
      RespectfulFunctions (ZMod 2) (Fin 24) (MulAction.orbitRel D (Fin 24)) := by
    ext v
    constructor
    · intro hv i j hij
      obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.mp hij
      change a.val.val j = i at ha
      subst i
      have h := congrFun (hv a) (a.val.val j)
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, fullRepresentation,
        BinaryPermutation.representation_apply, Equiv.symm_apply_apply] using h.symm
    · intro hv a
      funext i
      apply hv
      exact MulAction.orbitRel_apply.mpr ⟨a⁻¹, rfl⟩
  rw [he]
  exact quotientFunctionsLinearEquivRespectful_finrank (ZMod 2) (Fin 24) _

theorem twice_cocode_fixed_add_two_eq_orbits (D : Subgroup M24) [IsCyclic D]
    (ho : Odd (Nat.card D)) :
    2 * (Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) + 1) =
      Nat.card (MulAction.orbitRel.Quotient D (Fin 24)) :=
  (twice_cocode_fixed_add_two D ho).trans (finrank_full_fixed_eq_orbits D)
end MathieuCode
