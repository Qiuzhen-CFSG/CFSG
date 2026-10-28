module

public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Mathlib.GroupTheory.Index

/-!
# An invariant singular line for binary tensor two-groups

The determinant module has 75 nonzero singular matrices. A two-group in
its full binary normalizer therefore fixes a nonzero singular matrix.
Semilinearity preserves the coefficient line through this vector. Its
induced action on the four-element additive coefficient group fixes the
nonzero coefficient one, so the action kernel has index at most two.
All displacements of the line remain in that same singular line.

This supplies the first geometric step of Aschbacher–Smith 9.4.5,
combined manuscript of 1 March 2004, printed p.736. The homomorphism and
its actual matrix operators are retained for the weak-closure consumer.
-/

@[expose] public noncomputable section
open Module Matrix Subgroup
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private abbrev NonzeroSingular := {v : V // v.det = 0 ∧ v ≠ 0}

private theorem card_nonzeroSingular : Nat.card NonzeroSingular = 75 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Every binary tensor-normalizer two-group fixes a nonzero singular matrix. -/
theorem exists_fixed_nonzero_singular {H : Type*} [Group H]
    (f : H →* linearNormalizer action) (hH : IsPGroup 2 H) :
    ∃ v : V, v ≠ 0 ∧ v.det = 0 ∧ ∀ h : H, (f h).val.val v = v := by
  let e (h : H) : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (f h).val
  let : MulAction H NonzeroSingular := {
    smul := fun h v => ⟨e h v, (normalizer_det_zero_iff (e h)
      (normalizer_linearEquiv_mem (f h)) v).mpr v.property.1,
      fun hz => v.property.2 ((e h).injective (hz.trans (map_zero (e h)).symm))⟩
    one_smul := by intro v; apply Subtype.ext; change (f 1).val.val v = v; rw [map_one]; rfl
    mul_smul := by
      intro h k v
      apply Subtype.ext
      change (f (h*k)).val.val v = (f h).val.val ((f k).val.val v)
      rw [map_mul]
      rfl }
  obtain ⟨v,hv⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card NonzeroSingular
    (by rw [card_nonzeroSingular]; decide)
  exact ⟨v,v.property.2,v.property.1,fun h => congrArg Subtype.val (hv h)⟩

/-- The binary-linear parametrization of a coefficient line. -/
def singularFieldLineMap (v : V) : F →ₗ[ZMod 2] V where
  toFun c := c • v
  map_add' a b := add_smul a b v
  map_smul' c a := smul_assoc c a v

/-- The coefficient line through a matrix, viewed as a binary subspace. -/
def singularFieldLine (v : V) : Submodule (ZMod 2) V :=
  (singularFieldLineMap v).range

theorem mem_singularFieldLine (v w : V) :
    w ∈ singularFieldLine v ↔ ∃ c : F, c • v = w := Iff.rfl

theorem singularFieldLine_eq_span (v : V) :
    singularFieldLine v = (Submodule.span F ({v} : Set V)).restrictScalars (ZMod 2) := by
  ext w
  exact Submodule.mem_span_singleton.symm

theorem card_singularFieldLine (v : V) (hv : v ≠ 0) :
    Nat.card (singularFieldLine v) = 4 := by
  have hi : Function.Injective (singularFieldLineMap v) := smul_left_injective F hv
  rw [singularFieldLine,
    Nat.card_congr (LinearEquiv.ofInjective (singularFieldLineMap v) hi).toEquiv.symm]
  simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field

theorem singularFieldLine_singular (v : V) (hv : v.det = 0) :
    ∀ w ∈ singularFieldLine v, w.det = 0 := by
  rintro w ⟨c,rfl⟩
  change (c • v).det = 0
  rw [Matrix.det_smul,hv,mul_zero]

/-- A singular coefficient line with a pointwise kernel of index at most two. -/
structure NormalizerSingularLineData {H : Type*} [Group H]
    (f : H →* linearNormalizer action) where
  vector : V
  vector_ne_zero : vector ≠ 0
  vector_singular : vector.det = 0
  vector_fixed : ∀ h : H, (f h).val.val vector = vector
  kernel : Subgroup H
  index_le_two : kernel.index ≤ 2
  fixed : ∀ h ∈ kernel, ∀ v ∈ singularFieldLine vector, (f h).val.val v = v
  moved : ∀ h : H, ∀ v ∈ singularFieldLine vector,
    (f h).val.val v - v ∈ singularFieldLine vector

/-- The literal normalizer action supplies the required singular-line geometry. -/
theorem exists_normalizerSingularLineData {H : Type*} [Group H]
    (f : H →* linearNormalizer action) (hH : IsPGroup 2 H) :
    Nonempty (NormalizerSingularLineData f) := by
  obtain ⟨v,hv,hvs,hfix⟩ := exists_fixed_nonzero_singular f hH
  let e (h : H) : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (f h).val
  choose σ hσ using fun h : H => normalizer_semilinear (e h)
    (normalizer_linearEquiv_mem (f h))
  have hscalar (h : H) (c : F) : (f h).val.val (c • v) = σ h c • v := by
    change e h (c • v) = σ h c • v
    rw [hσ]
    exact congrArg (fun w : V => σ h c • w) (hfix h)
  let ρ : H →* MulAut (Multiplicative F) := {
    toFun h := AddEquiv.toMultiplicative (σ h).toAddEquiv
    map_one' := by
      apply MulEquiv.ext
      intro c
      change σ 1 c.toAdd = c.toAdd
      apply smul_left_injective F hv
      dsimp only
      rw [←hscalar,map_one]
      rfl
    map_mul' := by
      intro h k
      apply MulEquiv.ext
      intro c
      change σ (h*k) c.toAdd = σ h (σ k c.toAdd)
      apply smul_left_injective F hv
      dsimp only
      rw [←hscalar,←hscalar,←hscalar]
      rw [map_mul]
      rfl }
  have hcard : Nat.card (Multiplicative F) = 4 := by
    rw [Nat.card_congr Multiplicative.ofAdd.symm]
    simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field
  have hbound : Nat.card ρ.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hcard
      (Multiplicative.ofAdd (1 : F)) (by change (1 : F) ≠ 0; exact one_ne_zero) ρ.range (by
        rintro a ⟨h,rfl⟩
        change σ h 1 = 1
        exact map_one (σ h))
  refine ⟨{
    vector := v
    vector_ne_zero := hv
    vector_singular := hvs
    vector_fixed := hfix
    kernel := ρ.ker
    index_le_two := by rw [index_ker]; exact hbound
    fixed := ?_
    moved := ?_ }⟩
  · intro h hh w hw
    obtain ⟨c,rfl⟩ := hw
    change (f h).val.val (c • v) = c • v
    rw [hscalar]
    have hc := MulEquiv.congr_fun hh (Multiplicative.ofAdd c)
    change Multiplicative.ofAdd (σ h c) = Multiplicative.ofAdd c at hc
    exact congrArg (fun a : Multiplicative F => a.toAdd • v) hc
  · intro h w hw
    obtain ⟨c,rfl⟩ := hw
    refine ⟨σ h c - c,?_⟩
    change (σ h c - c) • v = (f h).val.val (c • v) - c • v
    rw [hscalar,sub_smul]

namespace NormalizerSingularLineData
variable {H : Type*} [Group H] {f : H →* linearNormalizer action}

/-- The actual invariant binary subspace supplied by the geometry. -/
abbrev line (D : NormalizerSingularLineData f) : Submodule (ZMod 2) V :=
  singularFieldLine D.vector

theorem line_card (D : NormalizerSingularLineData f) : Nat.card D.line = 4 :=
  card_singularFieldLine D.vector D.vector_ne_zero

theorem line_singular (D : NormalizerSingularLineData f) :
    ∀ v ∈ D.line, v.det = 0 :=
  singularFieldLine_singular D.vector D.vector_singular

theorem vector_mem (D : NormalizerSingularLineData f) : D.vector ∈ D.line :=
  ⟨1,one_smul F D.vector⟩

theorem line_stable (D : NormalizerSingularLineData f) (h : H)
    (v : V) (hv : v ∈ D.line) : (f h).val.val v ∈ D.line := by
  have hh := D.line.add_mem (D.moved h v hv) hv
  simpa only [sub_add_cancel] using hh

end NormalizerSingularLineData

/-- Choose the proved line and its actual action kernel. -/
def normalizerSingularLineData {H : Type*} [Group H]
    (f : H →* linearNormalizer action) (hH : IsPGroup 2 H) :
    NormalizerSingularLineData f :=
  (exists_normalizerSingularLineData f hH).some

/-- Application to the original elementary actor subgroup, without replacing
its operators or changing the source action. -/
theorem exists_elementary_normalizerSingularLineData
    (B : Subgroup (linearNormalizer action)) (hB : IsElementaryTwo B) :
    Nonempty (NormalizerSingularLineData B.subtype) := by
  let := hB.2
  exact exists_normalizerSingularLineData B.subtype (IsElementaryAbelian.isPGroup 2 B)

end ClassicalOrthogonal.FourPlusMatrix.Binary
