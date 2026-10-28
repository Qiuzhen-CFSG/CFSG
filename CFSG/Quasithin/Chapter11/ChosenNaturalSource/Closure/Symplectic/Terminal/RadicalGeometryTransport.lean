module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transport to the original normalizer action in 11.5.7

When O₂(L)=V, the chosen component action factors through the supplied
symplectic quotient marking. Its action on the original V is faithful,
because its induced action on V/C_V(L) is the natural matrix action.
The factorization identifies actual subgroup images and transports their
two-cores, using the genuine two-group kernel.

The local residual and its Sylow-join radical normalize each other and
normalize V. These containments justify every use of the action-image
commutator identity in RadicalGeometry; no action is silently restricted
to an intersection with the normalizer.

Source: Aschbacher--Smith, 11.5.7, printed pp.783--784. The earlier marked
local-factor identities are retained by the terminal assembly.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup
open scoped Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D}

/-- The original marked projection, with the native symplectic group instance. -/
@[expose] def componentQuotient (m : MarkedFlag E) :
    L →* Matrix.symplecticGroup (Fin 2) E.input.field.Carrier :=
  m.action.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem componentQuotient_surjective (m : MarkedFlag E) :
    Function.Surjective (componentQuotient m) :=
  m.action.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

@[expose] def componentAction : L →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion D.normalizes)

theorem componentAction_ker_of_core (m : MarkedFlag E)
    (hcore : L.pCoreIn 2 = V) :
    (componentQuotient m).ker ≤ (componentAction (D := D)).ker := by
  intro l hl
  have hlc : l ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply m.action.groupEquiv.injective
    exact hl.trans (m.action.groupEquiv.map_one).symm
  have hlV : (l : G) ∈ V := hcore ▸ mem_map_of_mem L.subtype hlc
  let := D.elementary
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change (l : G) * (v : G) * (l : G)⁻¹ = (v : G)
  exact mul_inv_eq_iff_eq_mul.mpr ((V.le_centralizer hlV) v v.property).symm

/-- The marked symplectic group acts on the original V via the original quotient map. -/
@[expose] def modelAction (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V) :
    Matrix.symplecticGroup (Fin 2) E.input.field.Carrier →* MulAut V :=
  (componentQuotient m).liftOfSurjective
    (componentQuotient_surjective m)
    ⟨componentAction, componentAction_ker_of_core m hcore⟩

theorem modelAction_quotient (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V) (l : L) :
    modelAction m hcore ((componentQuotient m) l) = componentAction (D := D) l := by
  unfold modelAction
  rw [MonoidHom.liftOfRightInverse_comp_apply]

/-- Faithfulness follows from the actual natural quotient action. -/
theorem modelAction_injective (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V) :
    Function.Injective (modelAction m hcore) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply ((modelAction m hcore).ker.eq_bot_iff_forall).mpr
  intro g hg
  obtain ⟨l,rfl⟩ := (componentQuotient_surjective m) g
  have hl : componentAction (D := D) l = 1 := by
    simpa only [MonoidHom.mem_ker, modelAction_quotient] using hg
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨v,hv⟩ := (Coordinates.sp4 m.action).projection_surjective
    (Multiplicative.ofAdd x)
  have he := (Coordinates.sp4 m.action).projection_component_conjugation l v
  change ((Coordinates.sp4 m.action).projection (componentAction (D := D) l v)).toAdd =
    _ at he
  rw [hl] at he
  change ((Coordinates.sp4 m.action).projection v).toAdd = _ at he
  change _ = _ *ᵥ ((Coordinates.sp4 m.action).projection v).toAdd at he
  rw [hv] at he
  change x = (componentQuotient m l).val *ᵥ x at he
  simpa using he.symm

/-- Action images of subgroups of L use the same quotient and the same lift. -/
theorem actionImage_component (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V)
    (A : Subgroup G) (hA : A ≤ L) :
    actionImage (V := V) A =
      ((A.subgroupOf L).map (componentQuotient m)).map
        (modelAction m hcore) := by
  rw [map_map]
  have he : (modelAction m hcore).comp (componentQuotient m) =
      componentAction (D := D) := MonoidHom.ext (modelAction_quotient m hcore)
  rw [he]
  change _ = (A.subgroupOf L).map (V.normalizerMonoidHom.comp (inclusion D.normalizes))
  rw [← map_map]
  unfold actionImage
  congr 1
  apply map_injective (normalizer (V : Set G)).subtype_injective
  rw [map_subgroupOf_eq_of_le (hA.trans D.normalizes), map_map]
  change A = (A.subgroupOf L).map L.subtype
  exact (map_subgroupOf_eq_of_le hA).symm

/-- The marked component quotient has its genuine two-group kernel. -/
theorem quotientMap_ker_two (m : MarkedFlag E) :
    IsPGroup 2 (componentQuotient m).ker := by
  have he : (componentQuotient m).ker = pCore 2 L := by
    ext l
    change m.action.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ _
    rw [map_eq_one_iff _ m.action.groupEquiv.injective]
    exact QuotientGroup.eq_one_iff l
  rw [he]
  exact pCore_isPGroup

/-- Faithfulness of the model identifies the actual component-action kernel. -/
theorem componentAction_ker_two (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V) :
    IsPGroup 2 (componentAction (D := D)).ker := by
  have he : (componentAction (D := D)).ker =
      (componentQuotient m).ker := by
    ext l
    change componentAction (D := D) l = 1 ↔ _
    rw [← modelAction_quotient m hcore,
      map_eq_one_iff _ (modelAction_injective m hcore)]
    rfl
  rw [he]
  exact quotientMap_ker_two m

/-- Restricting the ambient action to L gives its ordinary homomorphic image. -/
theorem actionImage_eq_component_map (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V)
    (A : Subgroup G) (hA : A ≤ L) :
    actionImage (V := V) A = (A.subgroupOf L).map (componentAction (D := D)) := by
  rw [actionImage_component m hcore A hA, map_map]
  congr 1
  exact MonoidHom.ext (modelAction_quotient m hcore)

/-- The two-core image is computed for the original action, with its two-group kernel. -/
theorem actionImage_localCore (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V)
    (A : Subgroup G) (hA : A ≤ L) :
    actionImage (V := V) (A.pCoreIn 2) = (actionImage (V := V) A).pCoreIn 2 := by
  have he : (A.pCoreIn 2).subgroupOf L = (A.subgroupOf L).pCoreIn 2 := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hA),
      map_pCoreIn_of_injective, map_subgroupOf_eq_of_le hA]
    exact L.subtype_injective
  rw [actionImage_eq_component_map m hcore _ ((pCoreIn_le 2 A).trans hA), he,
    map_pCoreIn_of_ker_isPGroup _ (componentAction_ker_two m hcore),
    actionImage_eq_component_map m hcore A hA]

omit [Finite G] in
/-- Actual action images preserve normalization once both normalizer bounds are checked. -/
theorem actionImage_normalizes (A B : Subgroup G)
    (hA : A ≤ normalizer (V : Set G)) (hB : B ≤ normalizer (V : Set G))
    (hAB : A ≤ normalizer (B : Set G)) :
    actionImage (V := V) A ≤ normalizer (actionImage (V := V) B : Set (MulAut V)) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  rw [← actionImage_commutator V A B hA hB]
  exact actionImage_mono (le_normalizer_iff_commutator_le_right.mp hAB)

omit [Finite G] in
/-- A two-group has a two-group image under the original normalizer action. -/
theorem actionImage_two (A : Subgroup G) (hA : IsPGroup 2 A) :
    IsPGroup 2 (actionImage (V := V) A) :=
  hA.comap_subtype.map V.normalizerMonoidHom

include E in
/-- All containments for the literal local residual and its Sylow-join radical. -/
theorem local_normalizations (U : Subgroup G)
    (hT : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    localResidual L U ≤ normalizer (V : Set G) ∧
    localRadical T L U ≤ normalizer (V : Set G) ∧
    localResidual L U ≤ normalizer (localRadical T L U : Set G) ∧
    localRadical T L U ≤ normalizer (localResidual L U : Set G) ∧
    (localResidual L U).pCoreIn 2 ≤ localRadical T L U := by
  have hn := sylow_normalizes_localResidual D U hT
  have hJ := sup_le (localResidual L U).le_normalizer hn
  refine ⟨(localResidual_le U).trans inf_le_left |>.trans D.normalizes,
    (localRadical_le_sylow U).trans E.input.sylow_normalizes,
    ?_, (localRadical_le_sylow U).trans hn, ?_⟩
  · exact (le_sup_left.trans (localResidual L U ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  · exact pCoreIn_mono_of_normalizes le_sup_left hJ

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometry
