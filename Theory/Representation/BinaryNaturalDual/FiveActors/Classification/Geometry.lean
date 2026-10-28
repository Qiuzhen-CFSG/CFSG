module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Basic
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Duality
public import Theory.ElementaryAbelian.GeneratorRank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Quadratic elementary subgroups in degree five

If all products of two displacement operators vanish, the span of their
images is fixed pointwise. The subgroup therefore lies in the unipotent
radical at that span. Encoding a radical element by its induced map
`X/W → W` bounds its order by `2^(dim(W)*(5-dim(W)))`. An elementary
subgroup of rank at least five consequently has displacement span of
dimension two or three.

This is the geometric part of an alternative proof of Aschbacher–Smith,
H.9.2(3), combined manuscript (1 March 2004), printed pp.390–391.
Quadraticity of arbitrary large elementary subgroups is a separate obligation.
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.FiveActors.Classification

/-- All products of two natural displacement operators vanish. -/
def Quadratic (E : Subgroup G) : Prop :=
  ∀ a ∈ E, ∀ b ∈ E, ∀ x : X, a (b x - x) = b x - x

def displacementSpan (E : Subgroup G) : Submodule (ZMod 2) X :=
  ⨆ b : E, (b.val.toLinearMap - LinearMap.id).range

theorem le_radical_displacementSpan (E : Subgroup G) (hE : Quadratic E) :
    E ≤ radical (displacementSpan E) := by
  intro a ha
  constructor
  · intro x hx
    have hle : displacementSpan E ≤ (a.toLinearMap - LinearMap.id).ker := by
      apply iSup_le
      intro b y hy
      obtain ⟨z, rfl⟩ := hy
      change a (b.val z - z) - (b.val z - z) = 0
      exact sub_eq_zero.mpr (hE a ha b.val b.property z)
    exact sub_eq_zero.mp (hle hx)
  · intro x
    have hle : (a.toLinearMap - LinearMap.id).range ≤ displacementSpan E :=
      le_iSup (fun b : E => (b.val.toLinearMap - LinearMap.id).range) ⟨a, ha⟩
    exact hle ⟨x, rfl⟩

private def radicalCoordinate (W : Submodule (ZMod 2) X) (g : radical W) :
    (X ⧸ W) →ₗ[ZMod 2] W :=
  W.liftQ ((g.val.toLinearMap - LinearMap.id).codRestrict W g.property.2)
    (by intro x hx; exact Subtype.ext (sub_eq_zero.mpr (g.property.1 x hx)))

private theorem radicalCoordinate_injective (W : Submodule (ZMod 2) X) :
    Function.Injective (radicalCoordinate W) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun f : (X ⧸ W) →ₗ[ZMod 2] W => (f (W.mkQ x)).val) he
  change g.val x - x = h.val x - x at hh
  exact sub_left_injective hh

theorem card_radical_le (W : Submodule (ZMod 2) X) :
    Nat.card (radical W) ≤ 2 ^ ((5 - Module.finrank (ZMod 2) W) *
      Module.finrank (ZMod 2) W) := by
  let : Finite ((X ⧸ W) →ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : (X ⧸ W) →ₗ[ZMod 2] W => (f : (X ⧸ W) → W))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective _ (radicalCoordinate_injective W)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (X ⧸ W) →ₗ[ZMod 2] W), Nat.card_zmod,
    Module.finrank_linearMap, Submodule.finrank_quotient] at h
  simpa [X, Space] using h

theorem radical_dimension (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hE : Quadratic E) (hr : 5 ≤ primeRank 2 E) :
    Module.finrank (ZMod 2) (displacementSpan E) = 2 ∨
      Module.finrank (ZMod 2) (displacementSpan E) = 3 := by
  let W := displacementSpan E
  have hle := le_radical_displacementSpan E hE
  have hcard : Nat.card E ≤ 2 ^ ((5 - Module.finrank (ZMod 2) W) *
      Module.finrank (ZMod 2) W) :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)).trans (card_radical_le W)
  have hd := hr.trans (IsElementaryAbelian.primeRank_le_of_card_le E hcard)
  have hb : Module.finrank (ZMod 2) W ≤ 5 := by
    simpa [X, Space] using W.finrank_le
  interval_cases hw : Module.finrank (ZMod 2) W <;> simp_all

end BinaryNaturalDual.FiveActors.Classification
