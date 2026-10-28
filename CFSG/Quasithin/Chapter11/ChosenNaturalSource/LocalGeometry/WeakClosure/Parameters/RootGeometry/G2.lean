module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.FieldKernel
public import Theory.Representation.G2NaturalNormalizerOffenders

/-!
# Inner A₂ actors for the original natural G₂ module

The actual normalizer conjugation identifies each operator with a scalar
multiple of an inner-field operator. Its coefficient kernel has index at
most two on an elementary actor. Exact fixed-vector lifting through the
original octonion cover makes the A₂ equality remove the field action;
square one then removes the scalar. Faithfulness identifies the remaining
operator with the literal component image, and the Sylow intersection
lifts it to L O₂(LT). No splitting is assumed.

Source: Aschbacher--Smith B.4.6(9) and 11.2.2(4), printed pp.89,768.
The Source endpoint applies this calculation to the actual weak closure.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open FullAutomizer Atlas.G2
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- A₂ actors in the original G₂ automizer are inner. The coefficient kernel
and exact fixed-vector lifting retain every nonsplit central attachment. -/
theorem g2_original_two_family_inner
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := D.elementary
    ∀ A : Subgroup (Automizer V),
      A ∈ fixedSpaceFamily (automizerRepresentation V) 2 → A ≤ inducedAutomizer V L := by
  let := D.elementary
  intro A hA
  let c := Coordinates.g2 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  let : Nontrivial c.Space := Module.nontrivial_of_finrank_pos
    (by change 0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier)
        rw [Natural.finrank_space]; decide)
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
  let : Nontrivial (Natural.Space S.field.Carrier) := Module.nontrivial_of_finrank_pos
    (by rw [Natural.finrank_space]; decide :
      0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier))
  let f : c.Space →+ Natural.Space S.field.Carrier := {
    toFun := id
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  let E : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective (f.toZModLinearMap 2) Function.bijective_id
  let τ : Representation (ZMod 2) (Automizer V) (Natural.Space S.field.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (a : Automizer V) (v : c.Space) : E (ρ a v) = τ a (E v) := by
    change E (ρ a v) = E (ρ a (E.symm (E v)))
    rw [E.symm_apply_apply]
  let eL : inducedAutomizer V L ≃* Model S.field.Carrier := layerEquiv D S c
  have hres' (b : inducedAutomizer V L) (v : Natural.Space S.field.Carrier) :
      τ b v = Natural.action S.field.Carrier (eL b) v := by
    change E (ρ b (E.symm v)) = _
    rw [hres]
    change Natural.action S.field.Carrier (eL b) (E (E.symm v)) = _
    rw [E.apply_symm_apply]
  let ν := Natural.Normalizer.binary S.field.Carrier
  have hnat (b : inducedAutomizer V L) :
      τ.asGroupHom b = ν.asGroupHom (eL b) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change τ b v = ν (eL b) v
    exact (hres' b v).trans (LinearMap.congr_fun
      (Natural.Normalizer.binary_apply S.field.Carrier (eL b)) v).symm
  have himage : actionImage (τ.comp (inducedAutomizer V L).subtype) = actionImage ν := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨eL b,(hnat b).symm⟩
    · rintro ⟨g,rfl⟩
      refine ⟨eL.symm g,?_⟩
      exact (hnat (eL.symm g)).trans
        (congrArg ν.asGroupHom (eL.apply_symm_apply g))
  let k : Automizer V →* linearNormalizer ν := τ.asGroupHom.codRestrict _ (fun a => by
    change τ.asGroupHom a ∈ normalizer (actionImage ν : Set _)
    rw [← himage]
    exact actionImage_le_linearNormalizer τ (inducedAutomizer V L) ⟨a,rfl⟩)
  have hq : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary
  let e := MulEquiv.ofBijective (LieAutomorphismExtensions.semilinearAction (F := S.field.Carrier))
    ⟨LieAutomorphismExtensions.semilinearAction_injective hq,
      LieAutomorphismExtensions.semilinearAction_surjective hq⟩
  let ψ := e.symm.toMonoidHom.comp ((Natural.Normalizer.normalizerAutomorphism S.field.Carrier).comp k)
  let π := SemidirectProduct.rightHom.comp ψ
  have hψ (a : Automizer V) : LieAutomorphismExtensions.semilinearAction (ψ a) =
      Natural.Normalizer.normalizerAutomorphism S.field.Carrier (k a) := e.apply_symm_apply _
  have hsemi : ∀ a (r : S.field.Carrier) v, τ a (r • v) = π a r • τ a v := by
    intro a r v
    obtain ⟨b,hb⟩ := Natural.Normalizer.normalizer_scalar_factor S.field.Carrier
      (k a) (ψ a).left (ψ a).right (hψ a).symm
    change (k a).val.val (r • v) = (ψ a).right r • (k a).val.val v
    rw [hb,hb,Natural.Normalizer.field_smul,map_smul,smul_comm]
  apply two_family_inner_of_fixed_lifting (inducedAutomizer V L)
    (automizerRepresentation V) τ (E.toLinearMap.comp (projectionLinear D S c))
    (E.surjective.comp (projectionLinear_surjective D S c))
    (fun a v => (congrArg E (he a v)).trans (hτ a _)) π hsemi _ _ hA
  swap
  · intro a ha v hv
    apply original_layer_fixed_lifts D S c ρ hres a ha v
    apply E.injective
    exact (hτ a _).trans hv
  intro a ha hk
  have hka : k a ^ 2 = 1 := by rw [← map_pow,ha,map_one]
  obtain ⟨g,hg⟩ := Natural.Normalizer.inner_involution_mem S.field.Carrier
    hq (k a) hka (ψ a) (hψ a) hk
  have heq : a = eL.symm g := hρ (by
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [hτ,hτ,hres',eL.apply_symm_apply]
    exact (congrArg (fun t : linearNormalizer ν => t.val.val (E v)) hg).symm.trans
      (LinearMap.congr_fun (Natural.Normalizer.binary_apply S.field.Carrier g) (E v)))
  rw [heq]
  exact (eL.symm g).property

/-- Source 11.2.2's A₂ containment for G₂ in the literal original T. -/
theorem g2_two_family
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := D.elementary
    ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
      A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let := D.elementary
  intro A hAT hA
  exact le_component_join_core_of_image D S hAT
    (g2_original_two_family_inner D S m _ hA)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootActors
