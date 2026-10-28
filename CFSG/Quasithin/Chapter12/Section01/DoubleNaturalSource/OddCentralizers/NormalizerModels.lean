module

public import Theory.Representation.BinaryNaturalDual.NaturalIsotypicExclusion
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Action

/-!
# Excluding the two linear-module alternatives in the original doubled orbit

Transport the invariant-form obstruction through the literal component
embedding and its natural-plus-dual coordinates. An independent marking
of L/O₂(L) is allowed. The other alternative has dimension six, whereas
the original full orbit has dimension eight or ten. These statements
exclude the actual module alternatives; they do not assert the ambient
4.4.3 classification producing those alternatives.

Source: Aschbacher--Smith, 4.4.3(i.a) and 12.1.9(1), printed pp.619,793.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
open BinaryNaturalDual BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- Source 4.4.3(i.a) is incompatible with the literal component action,
even after an arbitrary new identification of L/O₂(L) with GLₙ(2). -/
theorem no_natural_isotypic_marking {ι : Type*} [Fintype ι]
    (a : (L ⧸ pCore 2 L) ≃* LinearGroup n)
    (e : Additive (componentOrbit V (T : Subgroup G)) ≃ₗ[ZMod 2]
      (ι → BinaryLinear.OuterCyclic.Space n))
    (he : ∀ (q : L ⧸ pCore 2 L) w,
      e (B.quotientRepresentation (B.componentEmbedding q) w) = fun i => a q (e w i)) : False := by
  let E := B.linearCoordinates.symm.trans e
  let α := B.component.symm.trans a
  apply no_natural_copies_equiv (by have := B.degree; omega : 3 ≤ n) α E
  intro g v
  have ht : B.linearCoordinates.symm (naturalDualRepresentation g v) =
      B.quotientRepresentation (B.componentEmbedding (B.component.symm g))
        (B.linearCoordinates.symm v) := by
    apply B.linearCoordinates.injective
    rw [B.linearCoordinates.apply_symm_apply,B.componentEmbedding_coordinates,
      B.component.apply_symm_apply,B.linearCoordinates.apply_symm_apply]
  change e (B.linearCoordinates.symm (naturalDualRepresentation g v)) = _
  rw [ht,he]
  rfl

include B in
/-- The orthogonal exception of 4.4.3(i.a) has dimension six, whereas the
original full orbit has dimension eight or ten. -/
theorem no_six_dimensional_marking {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (e : Additive (componentOrbit V (T : Subgroup G)) ≃ₗ[ZMod 2] U)
    (hd : Module.finrank (ZMod 2) U = 6) : False := by
  have hh := e.finrank_eq
  rw [B.finrank_eq,hd] at hh
  have := B.degree
  omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

