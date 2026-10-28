module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSaturation
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Projection

/-!
# Marked coordinates on the lifted pencil span

An elementary abelian group of order sixteen, with a specified subgroup of
order four, admits binary coordinates taking that subgroup to the first
summand of F₂² ⊕ F₂². Choose a linear complement and bases of the two
summands. The cardinalities force both dimensions to be two.

The final application uses the literal subgroup U(V₂)=⟨V^Y⟩ and its
embedded V₂. No coordinate equivalence is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.55(3)
and 14.7.56(2), printed p.1066. Elementary abelianness and the source
orders sixteen and four remain earlier-source inputs.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions

open scoped IsMulCommutative
open Subgroup BinaryLinear.FourParabolicRadical
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open SpanSaturation

private theorem marked_linear_coordinates {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] [Finite A] (D : Submodule (ZMod 2) A)
    (hA : Module.finrank (ZMod 2) A = 4)
    (hD : Module.finrank (ZMod 2) D = 2) :
    ∃ e : A ≃ₗ[ZMod 2] BSpace, ∀ x, e x ∈ plane ↔ x ∈ D := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl D
  let s := D.prodEquivOfIsCompl C hC
  have hc : Module.finrank (ZMod 2) C = 2 := by
    have h := s.finrank_eq
    rw [Module.finrank_prod, hA, hD] at h
    omega
  let a : D ≃ₗ[ZMod 2] Vec := LinearEquiv.ofFinrankEq D Vec (by simp [hD, Vec])
  let b : C ≃ₗ[ZMod 2] Vec := LinearEquiv.ofFinrankEq C Vec (by simp [hc, Vec])
  refine ⟨s.symm.trans (a.prodCongr b), fun x => ?_⟩
  change b (s.symm x).2 = 0 ↔ x ∈ D
  rw [b.map_eq_zero_iff]
  exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero D C hC

/-- Construct coordinates preserving the specified four-subgroup. -/
theorem exists_marked_coordinates {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    (D : Subgroup A) (hA : Nat.card A = 16) (hD : Nat.card D = 4) :
    ∃ E : A ≃* Multiplicative BSpace,
      D.map E.toMonoidHom = plane.toAddSubgroup.toSubgroup := by
  let D' : Submodule (ZMod 2) (Additive A) := AddSubgroup.toZModSubmodule 2 D.toAddSubgroup
  have ha : Module.finrank (ZMod 2) (Additive A) = 4 := by
    apply (Nat.pow_right_injective (by decide : 1 < 2))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    change Nat.card A = _ at hc
    simpa [hA] using hc.symm
  have hd : Module.finrank (ZMod 2) D' = 2 := by
    apply (Nat.pow_right_injective (by decide : 1 < 2))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D')
    have hcard : Nat.card D' = 4 := hD
    simpa [hcard] using hc.symm
  obtain ⟨e, he⟩ := marked_linear_coordinates D' ha hd
  let E : A ≃* Multiplicative BSpace :=
    { toFun := fun a => .ofAdd (e (.ofMul a))
      invFun := fun b => (e.symm b.toAdd).toMul
      left_inv a := e.symm_apply_apply a
      right_inv b := e.apply_symm_apply b
      map_mul' a b := e.map_add a b }
  refine ⟨E, ?_⟩
  ext b
  rw [mem_map_equiv]
  exact (he (e.symm b.toAdd)).symm.trans (by rw [e.apply_symm_apply]; rfl)

/-- The coordinate witness required by `spanCoordinateAction`, constructed
from the source ranks on the actual generated line family. -/
theorem source_span_coordinates {G : Type*} [Group G] [Finite G]
    (V V₂ Y : Subgroup G) [IsElementaryAbelian 2 (generatedLineFamily V Y)]
    (hV₂ : V₂ ≤ V) (hW : Nat.card (generatedLineFamily V Y) = 16)
    (hD : Nat.card V₂ = 4) :
    ∃ E : generatedLineFamily V Y ≃* Multiplicative BSpace,
      (V₂.subgroupOf (generatedLineFamily V Y)).map E.toMonoidHom =
        plane.toAddSubgroup.toSubgroup := by
  apply exists_marked_coordinates _ hW
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (hV₂.trans (original_le_generated V Y))).toEquiv, hD]

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.SpanSourceActions
