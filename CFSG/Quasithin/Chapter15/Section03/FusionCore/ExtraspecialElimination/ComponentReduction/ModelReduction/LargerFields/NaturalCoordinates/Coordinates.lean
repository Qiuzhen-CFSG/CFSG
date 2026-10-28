module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Transport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Coordinates on the actual central quotient

A B.5.1 moved section for the restricted actor has the same underlying
subspace as the component commutator. Its central subrepresentation is
exactly the fixed-space kernel in the requested quotient. The identity
on representatives therefore induces an equivariant quotient isomorphism.

The order polynomial q(q²−1) determines the defining field size of SL₂.
Finite-field uniqueness then changes both the actor matrices and vector
coordinates to the field selected by the rank-reduction step.

Source: Aschbacher–Smith, B.5.1(1), printed p.99, and proof of 15.3.49,
printed p.1144. No natural-module selection is assumed by the transports.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Representation.SL2CubicFixedSection
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) K V) (J : Subgroup K)

/-- Restricting the actor preserves its literal moved subspace. -/
theorem moved_restrict : moved (ρ.comp J.subtype) ⊤ = moved ρ J := by
  unfold moved subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨x, _, w, hw, rfl⟩
    exact ⟨x, x.property, w, hw, rfl⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hx⟩, trivial, w, hw, rfl⟩

/-- Identify the literal quotient by the component fixed space with the B.5.1 section. -/
noncomputable def quotientEquiv
    (s : MovedSection (ρ.comp J.subtype) ⊤)
    (D : Submodule (ZMod 2) V) (hD : D = moved ρ J) :
    (D ⧸ (fixedSpace ρ J).comap D.subtype) ≃ₗ[ZMod 2]
      (s.space.toSubmodule ⧸ s.central.toSubmodule) := by
  let E := LinearEquiv.ofEq D s.space.toSubmodule
    (hD.trans ((moved_restrict ρ J).symm.trans s.space_eq.symm))
  refine Submodule.Quotient.equiv _ _ E ?_
  rw [s.central_eq]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩ x
    apply Subtype.ext
    exact hw x
  · intro hv
    refine ⟨E.symm v, ?_, E.apply_symm_apply v⟩
    intro x
    exact congrArg Subtype.val (hv ⟨x, trivial⟩)

/-- Transfer a classified natural action to the original component quotient. -/
noncomputable def of_movedSection
    {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (s : MovedSection (ρ.comp J.subtype) ⊤)
    (D : Submodule (ZMod 2) V) (hD : D = moved ρ J)
    (hstable : ∀ (j : J) (v : D), ρ j v ∈ D)
    (e : ActionEquiv (s.action.comp (⊤ : Subgroup J).subtype)
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2))) :
    NaturalComponentSection (F := F) ρ J D where
  model := Subgroup.topEquiv.symm.trans e.groupEquiv
  invariant := hstable
  coordinates := (quotientEquiv ρ J s D hD).trans e.linearEquiv
  equivariant j v := by
    have he := e.intertwines ⟨j, trivial⟩
      (quotientEquiv ρ J s D hD (Submodule.Quotient.mk v))
    exact he
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
variable {F E : Type*} [Field F] [Field E]

private theorem order_polynomial_strictMono :
    StrictMonoOn (fun q : ℕ => q * (q ^ 2 - 1)) (Set.Ici 2) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hsq : x ^ 2 < y ^ 2 := by nlinarith
  have hmul := Nat.mul_lt_mul_of_pos_left (show x ^ 2 - 1 < y ^ 2 - 1 by omega)
    (show 0 < x by omega)
  exact hmul.trans_le (Nat.mul_le_mul_right (y ^ 2 - 1) hxy.le)

/-- An actual SL₂ isomorphism determines an isomorphism of its finite defining fields. -/
noncomputable def fieldEquiv_of_sl2Equiv [Finite F] [Finite E]
    (e : SL(2,F) ≃* SL(2,E)) : F ≃+* E := by
  let _ := Fintype.ofFinite F
  let _ := Fintype.ofFinite E
  apply FiniteField.ringEquivOfCardEq
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  apply order_polynomial_strictMono.injOn (show 2 ≤ Nat.card F from Finite.one_lt_card)
    (show 2 ≤ Nat.card E from Finite.one_lt_card)
  simpa only [Atlas.card_sl_two] using Nat.card_congr e.toEquiv

variable [Algebra (ZMod 2) F] [Algebra (ZMod 2) E]

private noncomputable def fieldCoordinates (f : F ≃+* E) :
    (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → E) :=
  let e := AddEquiv.piCongrRight (fun _ : Fin 2 => f.toAddEquiv)
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 2) e.bijective

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- Change the field of a natural action, retaining compatible actor and vector maps. -/
noncomputable def transport_natural (ρ : Representation (ZMod 2) D V)
    (a : ActionEquiv ρ (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 2)))
    (f : F ≃+* E) :
    ActionEquiv ρ (restrictScalars (k := ZMod 2) (specialLinearNatural (k := E) 2)) where
  groupEquiv := a.groupEquiv.trans (Atlas.fieldEquivSL 2 f)
  linearEquiv := a.linearEquiv.trans (fieldCoordinates f)
  intertwines g v := by
    change fieldCoordinates f (a.linearEquiv (ρ g v)) = _
    rw [a.intertwines]
    ext i
    change f ((a.groupEquiv g).val.mulVec (a.linearEquiv v) i) =
      (((a.groupEquiv g).val.map f).mulVec (fun j => f (a.linearEquiv v j))) i
    exact RingHom.map_mulVec f.toRingHom _ _ i

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
