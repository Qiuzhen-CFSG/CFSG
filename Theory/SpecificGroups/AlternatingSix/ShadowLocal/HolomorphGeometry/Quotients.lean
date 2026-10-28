module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Centralizers
public import Theory.Frattini.BinarySquares

/-!
# The elementary and central quotients of the holomorph

The parity of the rotation and the multiplier modulo inversion give the
quotient by the inner D₈. Squares and commutators generate exactly `⟨r²⟩`.
The center of the quotient by `⟨r⁴⟩` is computed using the canonical quotient
map, and is the image of `⟨r²,b⟩`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, pp.568–570.
-/

@[expose] public section
namespace AlternatingSix.ShadowLocal.Holomorph
open Subgroup
open scoped commutatorElement
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- The two quotient coordinates: rotation parity and multiplier modulo inversion. -/
def innerQuotientHom : Model →* E4 where
  toFun x := (.ofAdd (x.left.toAdd.val : ZMod 2),
    .ofAdd (if x.right = 1 ∨ x.right = -1 then 0 else 1))
  map_one' := rfl
  map_mul' := by decide +kernel

theorem innerQuotientHom_surjective : Function.Surjective innerQuotientHom := by decide +kernel

theorem innerQuotientHom_ker : innerQuotientHom.ker = innerD := by
  ext x
  simp only [MonoidHom.mem_ker, mem_innerD]
  revert x
  decide +kernel

noncomputable def innerQuotientEquiv : (Model ⧸ innerD) ≃* E4 :=
  (QuotientGroup.quotientMulEquivOfEq innerQuotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ innerQuotientHom_surjective)

theorem derived_model : commutator Model = cyclicFour := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x _ y _
    have h : ∀ x y : Model, ∃ i, fourEmbedding i = ⁅x, y⁆ := by decide +kernel
    exact (mem_cyclicFour _).mpr (h x y)
  · apply zpowers_le.mpr
    have h : ⁅rotation, reflection⁆ = rotation ^ 2 := by decide +kernel
    rw [← h]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

theorem frattini_model : frattini Model = cyclicFour := by
  have hp : IsPGroup 2 Model := IsPGroup.of_card (by simpa using card_model : Nat.card Model = 2 ^ 5)
  rw [hp.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    have h : ∀ x : Model, ∃ i, fourEmbedding i = x ^ 2 := by decide +kernel
    exact (mem_cyclicFour _).mpr (h x)
  · exact zpowers_le.mpr (subset_closure ⟨rotation, rfl⟩)

private theorem central_quotient_mem (x : Model) :
    QuotientGroup.mk' centralTwo x ∈ center (Model ⧸ centralTwo) ↔
      ∀ g : Model, (g * x) / (x * g) ∈ centralTwo := by
  rw [mem_center_iff]
  constructor
  · intro h g
    exact QuotientGroup.eq_iff_div_mem.mp (h (QuotientGroup.mk' centralTwo g))
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective centralTwo q
    exact QuotientGroup.eq_iff_div_mem.mpr (h g)

theorem central_quotient_center_preimage :
    (center (Model ⧸ centralTwo)).comap (QuotientGroup.mk' centralTwo) =
      cyclicFour ⊔ transpositionSubgroup := by
  ext x
  simp only [mem_comap, central_quotient_mem, mem_centralTwo,
    mem_cyclicFour_sup_transposition]
  revert x
  decide +kernel

/-- The source identity `Z(P/Z) = (Y P₀)/Z`, using the actual quotient map. -/
theorem center_central_quotient :
    center (Model ⧸ centralTwo) =
      (cyclicFour ⊔ transpositionSubgroup).map (QuotientGroup.mk' centralTwo) := by
  rw [← central_quotient_center_preimage]
  exact (Subgroup.map_comap_eq_self (by
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective centralTwo)]
    exact le_top)).symm

end AlternatingSix.ShadowLocal.Holomorph
