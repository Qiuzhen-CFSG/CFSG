module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import Theory.Representation.SymplecticConjugatePair.Ambient.Transport
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Involutions.CentralTypes
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Diagram preservation for the descended symplectic tensor

A diagram-moving automorphism is inner-field times the exceptional graph map.
It sends the standard b₁ root involution to a conjugate of the standard a₂
root involution. Ambient conjugation preserves fixed dimension, so the native
fixed dimensions 10s and 8s exclude this possibility when s is positive.
The native calculations remain explicit and are produced independently.

Source: Aschbacher–Smith, K.3.4.2, printed pp.456–457.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes
open Representation.OneCohomology.SymplecticFour
open SymplecticConjugatePair.Involutions

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F]

theorem preservesDiagram_of_native_fixed_dimensions (e : Sp F ≃* L)
    {s : ℕ} (hs : 0 < s)
    (hb : ∀ x : Sp F, IsB1 x →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (e x).val)) = 10 * s)
    (ha : ∀ x : Sp F, IsA2 x →
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (e x).val)) = 8 * s)
    (g : G) : PreservesDiagram (extensionAction L e g) := by
  by_contra hn
  obtain ⟨c, τ, he⟩ := SymplecticConjugatePair.Ambient.moving_eq_inner_field_graph _ hn
  let x : Sp F := rootElement 0 1
  have hx : IsB1 x := by
    simpa only [RootSubgroup.element_zero, mul_one] using
      (central_isB1 (F := F) (one_ne_zero : (1 : F) ≠ 0))
  have hy : IsA2 (extensionAction L e g x) := by
    rw [he]
    change IsA2 (c * fieldAutomorphism τ (graphAut x) * c⁻¹)
    apply (isA2_conj_iff c _).mpr
    have hgx : graphAut x = rootElement 4 (1 : F) := by
      simpa [x, graphAut_apply, rootPermutation, rootParameter] using
        (graphEnd_root (F := F) 0 1)
    rw [hgx, fieldAutomorphism_root, map_one]
    simpa only [RootSubgroup.element_zero, one_mul] using
      (central_isA2 (F := F) (one_ne_zero : (1 : F) ≠ 0))
  have hbx := hb x hx
  have hay := ha _ hy
  have hc := fixedCodim_zpowers_conj ρ (e x).val g
  have hsx := fixedCodim_add_finrank ρ (zpowers (e x).val)
  have hsy := fixedCodim_add_finrank ρ (zpowers (e (extensionAction L e g x)).val)
  rw [extensionAction_apply] at hay hsy
  omega

end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer
