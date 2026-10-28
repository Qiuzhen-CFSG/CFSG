module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.ComponentSection
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.Representation.SL2CubicFixedSection

/-!
# Literal component commutators and compatible Borel markings

The image of [U_H,L₀] in U_H/Z is exactly the moved subspace for L₀*.
The proof compares generators through the actual quotient map, using only
the public membership description of the component section. Conjugating
an SL₂ actor marking requires applying the same matrix to its natural
coordinates; the resulting intertwiner retains the original quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1144. Natural-module selection is a separate step.
-/

public section

open Subgroup Matrix Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
open scoped IsMulCommutative MatrixGroups commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
variable {G : Type*} [Group G]

private theorem difference_eq (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (h : H) (u : U) :
    action.representation (QuotientGroup.mk' (pCore 2 H) h)
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) -
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
        (⟨(h : G) * (u : G) * (h : G)⁻¹,
          le_normalizer_iff.mp action.normalizes h h.property u u.property⟩ * u⁻¹)) := by
  rw [action.on_representatives]
  rw [map_mul, map_inv, sub_eq_add_neg]
  rfl

/-- The component is the literal commutator subspace for its star actor. -/
theorem componentSection_eq_moved (Z H ZS L T : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hL0H : localSpan L T ≤ H) :
    componentSection Z H ZS L T =
      subspaceCommutator action.representation ⊤ (starImage H (localSpan L T)) := by
  let U := localSpan ZS H
  let K := localSpan L T
  let W := subspaceCommutator action.representation ⊤ (starImage H K)
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let P : Subgroup U :=
    { carrier := {u | Additive.ofMul (q u) ∈ W}
      one_mem' := by
        change Additive.ofMul (q 1) ∈ W
        rw [map_one]
        exact W.zero_mem
      mul_mem' := by
        intro a b ha hb
        change Additive.ofMul (q (a * b)) ∈ W
        rw [map_mul]
        exact W.add_mem ha hb
      inv_mem' := by
        intro a ha
        change Additive.ofMul (q a⁻¹) ∈ W
        rw [map_inv]
        exact W.neg_mem ha }
  have hcomm : ⁅K, U⁆ ≤ P.map U.subtype := by
    apply commutator_le.mpr
    intro k hk u hu
    let kH : H := ⟨k, hL0H hk⟩
    let uU : U := ⟨u, hu⟩
    let c : U := ⟨k * u * k⁻¹,
      le_normalizer_iff.mp action.normalizes k kH.property u hu⟩ * uU⁻¹
    refine ⟨c, ?_, rfl⟩
    change Additive.ofMul (q c) ∈ W
    rw [← difference_eq H U Z action kH uU]
    apply Submodule.subset_span
    exact ⟨QuotientGroup.mk' (pCore 2 H) kH, ⟨kH, hk, rfl⟩,
      Additive.ofMul (q uU), trivial, rfl⟩
  apply le_antisymm
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := (mem_componentSection Z H ZS L T v).mp hv
    rw [commutator_comm] at hu
    obtain ⟨p, hp, he⟩ := hcomm hu
    have he' : p = u := Subtype.ext he
    exact he' ▸ hp
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ha, w, _, rfl⟩
    obtain ⟨h, hh, rfl⟩ := ha
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
    have hw : Additive.ofMul (q u) = w := congrArg Additive.ofMul hu
    rw [← hw, difference_eq H U Z action h u]
    apply (mem_componentSection Z H ZS L T _).mpr
    refine ⟨_, ?_, rfl⟩
    change ⁅(h : G), (u : G)⁆ ∈ ⁅U, K⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hh u.property

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

private noncomputable def naturalLinearEquiv (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
  ((Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL g)).toLinearEquiv).restrictScalars (ZMod 2)

open Representation.SL2CubicFixedSection

/-- Re-mark the actor and its natural coordinates by the same conjugating matrix. -/
noncomputable def conjugateSection
    {ρ : Representation (ZMod 2) K V} {J : Subgroup K} {D : Submodule (ZMod 2) V}
    (s : NaturalComponentSection (F := F) ρ J D)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) : NaturalComponentSection (F := F) ρ J D where
  model := s.model.trans (MulAut.conj g)
  invariant := s.invariant
  coordinates := s.coordinates.trans (naturalLinearEquiv g)
  equivariant l d := by
    change g.val *ᵥ s.coordinates (Submodule.Quotient.mk
      ⟨ρ l d, s.invariant l d⟩) =
        (g * s.model l * g⁻¹).val *ᵥ (g.val *ᵥ s.coordinates (Submodule.Quotient.mk d))
    rw [s.equivariant]
    simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]

/-- The geometric Borel-placement output changes both markings compatibly. -/
theorem exists_borel_marking
    {ρ : Representation (ZMod 2) K V} {J Y : Subgroup K} {D : Submodule (ZMod 2) V}
    (hYJ : Y ≤ J) (s : NaturalComponentSection (F := F) ρ J D)
    (hB : ∀ e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F,
      ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, ∀ y : Y,
        g * e ⟨y, hYJ y.property⟩ * g⁻¹ ∈ Matrix.SpecialLinearGroup.rankOneBorel F) :
    ∃ s' : NaturalComponentSection (F := F) ρ J D, ∀ y : Y,
      s'.model ⟨y, hYJ y.property⟩ ∈ Matrix.SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨g, hg⟩ := hB s.model
  exact ⟨conjugateSection s g, hg⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
