module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Kernel
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The rank-one quotient over the original marked field

The PSL₂ recognition in 11.3.5--6 initially allows any finite field of the
specified order. Uniqueness of finite fields transports it to the original
field of the chosen natural module. In characteristic two PSL₂ and SL₂ agree.
The identification of the literal residual star group is transported along
the already proved kernel equality, retaining the original quotient map.

Source: Aschbacher--Smith, 11.3.7(1), printed p.773. The field transport uses
the attributed ATLAS construction already in the repository.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The matrix carrier uses the very same field as the chosen source module. -/
theorem source_residual_matrix_equiv
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    Nonempty ((outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hmodel
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : Fintype S.field.Carrier := Fintype.ofFinite S.field.Carrier
  let f : F ≃+* S.field.Carrier := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans S.field.card_eq.symm)
  exact ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL
      (F := S.field.Carrier)).symm⟩

/-- Both matrix identifications commute with the literal projection from K.
This discharges the field and group-marking part of the natural coordinates. -/
theorem source_compatible_matrix_equivs
    (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree)) :
    ∃ (e : (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier)
      (eStar : residualStar T H ≃* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier),
      ∀ k : outsideResidual H,
        eStar ⟨starProjection T H (inclusion (outsideResidual_le H) k),
          mem_map_of_mem (starProjection T H) k.property⟩ =
        e (QuotientGroup.mk' _ k) := by
  let := source_residualQuotient_simple hmodel
  obtain ⟨e⟩ := source_residual_matrix_equiv hmodel
  let d := residualStarEquiv T H s.outside.1.1.2 s.moves_omega_center
  refine ⟨e,d.symm.trans e,?_⟩
  intro k
  change e (d.symm (d (QuotientGroup.mk' _ k))) = e (QuotientGroup.mk' _ k)
  rw [d.symm_apply_apply]

/-- Each actual Sylow subgroup of K-star has rank n, measured after its
inclusion in H-star. This uses cardinality transport, not a family label. -/
theorem source_residualStar_sylow_rank
    (s : Hypothesis1131At D S U₁ H)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (R : Sylow 2 (residualStar T H)) :
    Representation.BinaryOffender.rank
      ((R : Subgroup (residualStar T H)).map (residualStar T H).subtype) =
        S.field.degree := by
  obtain ⟨_,e,_⟩ := source_compatible_matrix_equivs s hmodel
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card
      ((R : Subgroup (residualStar T H)).map (residualStar T H).subtype) =
      2 ^ S.field.degree := calc
    _ = Nat.card R := (Nat.card_congr
      ((R : Subgroup (residualStar T H)).equivMapOfInjective
        (residualStar T H).subtype (residualStar T H).subtype_injective).toEquiv).symm
    _ = Nat.card P := Nat.card_congr
      ((R : Subgroup (residualStar T H)).equivMapOfInjective
        e.toMonoidHom e.injective).toEquiv
    _ = Nat.card S.field.Carrier := (Nat.card_congr
      (Matrix.SpecialLinearGroup.sylowEquivAdditive S.field.Carrier 2 P).toEquiv).symm
    _ = 2 ^ S.field.degree := S.field.card_eq
  rw [Representation.BinaryOffender.rank,hc,Nat.log_pow (by decide : 1 < 2)]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
