module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.NativeFixers.MatrixFixers
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.Native
public import Theory.FieldTheory.ScalarTwistedFixedPoints
/-!
# Component pointwise fixers on the descended symplectic tensor

The coordinate calculation identifies the full fixer of a central involution's
displacement with its alpha line having sigma-fixed parameters. The actual
scalar-extension intertwiner preserves this pointwise-fixing equation in both
directions. Group-theoretic involution conjugacy therefore identifies the full
fixer on the original binary representation with a transported conjugate of
that concrete subgroup.

The fixed coefficient field has order 2^s: its square is the extension's order,
which follows from the genuine degree-two extension and the Schur-field order.
For a₂ and c₂, native freeness identifies the fixed-space fixer with the same
subgroup. The final adapters compute the literal fixer inside an ambient
component L. No ambient containment or diagram-preservation premise is used.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
For arbitrary central coefficients, sigma fixes the *parameter*; identification
with the fixed subgroup of sigma on alpha(j) additionally requires sigma(a)=a
and sigma(b)=b, as in AlphaGroups.mem_centralSigmaAlpha_iff_fixed.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open scoped Matrix TensorProduct Classical
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {F : Type*} [Field F] [Finite F]
omit [Finite F] in
lemma centralSigmaAlpha_card (σ : F ≃+* F) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    Nat.card (centralSigmaAlpha σ a b) = Nat.card (FixedBy.subfield F σ) := by
  rw [centralSigmaAlpha, ← Nat.card_congr
    ((sigmaFixedCoefficients σ).equivMapOfInjective (centralAlphaParameter a b)
      (centralAlphaParameter_injective hab)).toEquiv]
  exact Nat.card_congr {
    toFun := fun t => ⟨t.val.toAdd,t.property⟩
    invFun := fun t => ⟨Multiplicative.ofAdd t.val,t.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation.BinaryOffender
variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- The fixed-coefficient order is derived from the field extension, not
assumed as an extra certificate. -/
theorem TensorIdentification.sigma_fixed_card {s : ℕ} (h : TensorIdentification ρ F s) :
    Nat.card (FixedBy.subfield F h.sigma.toRingEquiv) = 2^s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : Module.Finite (SchurField ρ) F := Module.finite_of_finrank_eq_succ h.extension_degree
  have he : Nat.card F = (2^s)^2 := by
    rw [Module.natCard_eq_pow_finrank (K := SchurField ρ) (V := F),
      h.extension_degree,h.schur_card]
  have hn : h.sigma.toRingEquiv ≠ RingEquiv.refl F := by
    intro he
    apply h.sigma_ne
    ext x
    exact DFunLike.congr_fun he x
  have hh := FiniteField.card_involution_fixed_sq h.sigma.toRingEquiv h.sigma_involutive hn
  rw [he] at hh
  exact (Nat.pow_left_injective (by decide : 2 ≠ 0)) hh

/-- Pointwise displacement fixing descends and ascends through the actual
scalar-extension intertwiner. -/
theorem TensorIdentification.fixes_displacement_iff_matrix {s : ℕ}
    (h : TensorIdentification ρ F s) (g j : D) :
    (∀ v, ρ g (ρ j v - v) = ρ j v - v) ↔
      ∀ X, TensorGeometry.matrixAction h.sigma.toRingEquiv (h.groupEquiv g)
        (TensorGeometry.matrixAction h.sigma.toRingEquiv (h.groupEquiv j) X - X) =
        TensorGeometry.matrixAction h.sigma.toRingEquiv (h.groupEquiv j) X - X := by
  constructor
  · intro hf X
    have hv (v : ρ.asModule) : ρ.endFieldRep g (ρ.endFieldRep j v - v) = ρ.endFieldRep j v - v := by
      apply ρ.asModuleEquiv.injective
      simpa only [endFieldRep_apply', map_sub] using hf (ρ.asModuleEquiv v)
    have hE (z : F ⊗[SchurField ρ] ρ.asModule) :
        extendScalars F ρ.endFieldRep g (extendScalars F ρ.endFieldRep j z - z) =
          extendScalars F ρ.endFieldRep j z - z := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add]; rw [add_sub_add_comm, map_add, hx, hy]
      | tmul c v =>
        simp only [extendScalars_apply, LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub, hv]
    have hh := congrArg (fun z => TensorGeometry.coordinates (h.linearEquiv z))
      (hE (h.linearEquiv.symm (TensorGeometry.coordinates.symm X)))
    simpa only [map_sub, h.intertwines, TensorGeometry.coordinates_action,
      LinearEquiv.apply_symm_apply] using hh
  · intro hf v
    apply h.tensorEmbedding_injective ρ
    apply TensorGeometry.coordinates.injective
    simpa only [map_sub, h.tensorEmbedding_intertwines, TensorGeometry.coordinates_action] using
      hf (TensorGeometry.coordinates (h.tensorEmbedding ρ v))

end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry
variable {K D U : Type*} [Field K] [Group D] [AddCommGroup U] [Module K U]
private lemma fixes_displacement_conj (ρ : Representation K D U) (g j c : D) :
    (∀ v, ρ g (ρ j v - v) = ρ j v - v) ↔
      ∀ v, ρ (c*g*c⁻¹) (ρ (c*j*c⁻¹) v - v) = ρ (c*j*c⁻¹) v - v := by
  have ht (a b c : D) (hf : ∀ v, ρ a (ρ b v - v) = ρ b v - v) (v : U) :
      ρ (c*a*c⁻¹) (ρ (c*b*c⁻¹) v - v) = ρ (c*b*c⁻¹) v - v := by
    have hh := congrArg (ρ c) (hf (ρ c⁻¹ v))
    simpa [map_mul, Module.End.mul_apply, map_sub] using hh
  constructor
  · exact ht g j c
  · intro hf
    have hh := ht (c*g*c⁻¹) (c*j*c⁻¹) c⁻¹ hf
    simpa [mul_assoc] using hh
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry

namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation.BinaryOffender TensorGeometry
open SymplecticConjugatePair.Involutions
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- A specified central conjugate gives the full component fixer, with the
literal conjugation and group identification in its inclusion map. -/
theorem TensorIdentification.displacement_fixer_eq_centralSigmaAlpha {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (c : Sp F) (a b : F)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (hc : c * h.groupEquiv j * c⁻¹ = rootElement 0 a * rootElement 4 b) :
    subspaceKernel ρ (LinearMap.range (displacement ρ j)) ⊤ =
      (centralSigmaAlpha h.sigma.toRingEquiv a b).map
        (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  ext g
  have hg : g ∈ subspaceKernel ρ (LinearMap.range (displacement ρ j)) ⊤ ↔
      ∀ v, ρ g (ρ j v - v) = ρ j v - v := by
    simp only [mem_subspaceKernel, Subgroup.mem_top, true_and, LinearMap.mem_range]
    constructor
    · intro hh v
      exact hh _ ⟨v,rfl⟩
    · rintro hh _ ⟨v,rfl⟩
      exact hh v
  rw [hg, h.fixes_displacement_iff_matrix ρ,
    fixes_displacement_conj (matrixAction h.sigma.toRingEquiv) (h.groupEquiv g)
      (h.groupEquiv j) c, hc,
    fixes_central_displacement_iff h.sigma.toRingEquiv a b hab]
  rw [Subgroup.mem_map_equiv]
  rfl

lemma TensorIdentification.centralSigmaAlpha_card {s : ℕ}
    (h : TensorIdentification ρ F s) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    Nat.card (centralSigmaAlpha h.sigma.toRingEquiv a b) = 2^s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  rw [TensorGeometry.centralSigmaAlpha_card _ hab, h.sigma_fixed_card ρ]

/-- Every native involution has the calculated full component fixer. -/
theorem TensorIdentification.involution_displacement_fixer {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2) :
    ∃ (c : Sp F) (a b : F), (a ≠ 0 ∨ b ≠ 0) ∧
      c * h.groupEquiv j * c⁻¹ = rootElement 0 a * rootElement 4 b ∧
      subspaceKernel ρ (LinearMap.range (displacement ρ j)) ⊤ =
        (centralSigmaAlpha h.sigma.toRingEquiv a b).map
          (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have ho : orderOf (h.groupEquiv j) = 2 := (h.groupEquiv.orderOf_eq j).trans hj
  obtain ⟨c,a,b,hc⟩ := involution_conjugate_central h.field_card (h.groupEquiv j) ho
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra! hz
    have he := (MulAut.conj c).orderOf_eq (h.groupEquiv j)
    change orderOf (c*h.groupEquiv j*c⁻¹) = orderOf (h.groupEquiv j) at he
    rw [hc,hz.1,hz.2] at he
    simp [RootSubgroup.element_zero,ho] at he
  exact ⟨c,a,b,hab,hc,h.displacement_fixer_eq_centralSigmaAlpha ρ j c a b hab hc⟩

/-- The component displacement fixer has the order asserted in K.3.4.2. -/
theorem TensorIdentification.involution_displacement_fixer_card {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2) :
    Nat.card (subspaceKernel ρ (LinearMap.range (displacement ρ j)) ⊤) = 2^s := by
  obtain ⟨c,a,b,hab,_,he⟩ := h.involution_displacement_fixer ρ j hj
  rw [he, ← Nat.card_congr
    ((centralSigmaAlpha h.sigma.toRingEquiv a b).equivMapOfInjective
      (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom
      (h.groupEquiv.trans (MulAut.conj c)).symm.injective).toEquiv]
  exact h.centralSigmaAlpha_card ρ hab

variable [Finite D]

/-- For a₂ and c₂ the fixed-space fixer has the same order. -/
theorem TensorIdentification.nonB1_fixedSpace_fixer_card {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv j)) :
    Nat.card (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) ⊤) = 2^s := by
  rw [h.nonB1_fixedSpace_eq_displacement ρ j hj hB]
  exact h.involution_displacement_fixer_card ρ j hj

/-- Native freeness gives the literal fixed-space fixer, including its
transported subgroup description. -/
theorem TensorIdentification.nonB1_fixedSpace_fixer {s : ℕ}
    (h : TensorIdentification ρ F s) (j : D) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv j)) :
    ∃ (c : Sp F) (a b : F), (a ≠ 0 ∨ b ≠ 0) ∧
      c * h.groupEquiv j * c⁻¹ = rootElement 0 a * rootElement 4 b ∧
      subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) ⊤ =
        (centralSigmaAlpha h.sigma.toRingEquiv a b).map
          (h.groupEquiv.trans (MulAut.conj c)).symm.toMonoidHom := by
  rw [h.nonB1_fixedSpace_eq_displacement ρ j hj hB]
  exact h.involution_displacement_fixer ρ j hj
end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic
open Representation.BinaryOffender TensorGeometry
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

omit [Finite G] [FiniteDimensional (ZMod 2) V] [IsIrreducible (ρ.comp L.subtype)] in
private lemma component_kernel_map (W : Submodule (ZMod 2) V) :
    (subspaceKernel (ρ.comp L.subtype) W ⊤).map L.subtype = subspaceKernel ρ W L := by
  ext g
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k.property,hk.2⟩
  · rintro ⟨hg,hfix⟩
    exact ⟨⟨g,hg⟩,⟨Subgroup.mem_top _,hfix⟩,rfl⟩

omit [Finite G] in
/-- The exact component fixer inside the original ambient representation. -/
theorem TensorIdentification.component_involution_displacement_fixer_card {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : orderOf j = 2) :
    Nat.card (subspaceKernel ρ (LinearMap.range (displacement ρ j)) L) = 2^s := by
  have ho : orderOf (⟨j,hjL⟩ : L) = 2 := (Subgroup.orderOf_coe (⟨j,hjL⟩ : L)).symm.trans hj
  rw [← component_kernel_map ρ L,
    ← Nat.card_congr ((subspaceKernel (ρ.comp L.subtype)
      (LinearMap.range (displacement ρ j)) ⊤).equivMapOfInjective L.subtype
        Subtype.val_injective).toEquiv]
  exact h.involution_displacement_fixer_card (ρ.comp L.subtype) ⟨j,hjL⟩ ho

/-- The corresponding ambient component calculation for a₂ and c₂. -/
theorem TensorIdentification.component_nonB1_fixedSpace_fixer_card {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    (j : G) (hjL : j ∈ L) (hj : orderOf j = 2)
    (hB : ¬ IsB1 (h.groupEquiv ⟨j,hjL⟩)) :
    Nat.card (subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) L) = 2^s := by
  rw [h.component_nonB1_fixedSpace_eq_displacement ρ L j hjL hj hB]
  exact h.component_involution_displacement_fixer_card ρ L j hjL hj
end CFSG.Quasithin.ChapterK.Symplectic
