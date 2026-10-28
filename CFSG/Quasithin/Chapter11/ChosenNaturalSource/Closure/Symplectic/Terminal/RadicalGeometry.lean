module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometryModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometryTransport

/-!
# Original radical displacement and separation in symplectic 11.5.7

Write Jᵢ and Qᵢ for the actual action images of Lᵢ and Rᵢ on V.
Mutual normalization gives [Q₂,J₂] ≤ O₂(J₂) ≤ Q₂. The preceding
compatible local markings identify O₂(J₂) with the intrinsic plane
radical, whose commutator generation makes both bounds exact. Its only
proper invariant subgroups are central, so every nonzero B ≤ Q₂ with
[B,J₂]=B is this entire displacement.

The plane radical also lies in the point local group. If its image lay
in Q₁, normality would place it in O₂(J₁), contradicting the explicit
shear separating the two intrinsic radicals. Both local groups use the
same reorientation of the original L/O₂(L) marking, and the action on
V is constructed from the actual normalizer action.

The theorem retains O₂(L)=V and the two preceding marked local-factor
identities. It proves RadicalDisplacement and applies it to the actual
moved-seed consumer; it does not assert the full closure theorem.
Source: Aschbacher--Smith, 11.5.7, printed pp.783--784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D}
namespace RadicalGeometry

theorem local_action_core_bounds (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V)
    (U : Subgroup G) (hT : (T : Subgroup G) ≤ normalizer (U : Set G)) :
    let J := actionImage (V := V) (localResidual L U)
    let Q := actionImage (V := V) (localRadical T L U)
    J ≤ normalizer (Q : Set (MulAut V)) ∧
    J.pCoreIn 2 ≤ Q ∧ ⁅Q,J⁆ ≤ J.pCoreIn 2 ∧ IsPGroup 2 Q := by
  dsimp only
  obtain ⟨hLN,hRN,hLR,hRL,hcoreR⟩ := local_normalizations (E := E) U hT
  have hLR' := actionImage_normalizes _ _ hLN hRN hLR
  have hRL' := actionImage_normalizes _ _ hRN hLN hRL
  have htwo := actionImage_two (V := V) (localRadical T L U)
    (isPGroup_pCoreIn 2 (localResidual L U ⊔ (T : Subgroup G)))
  refine ⟨hLR', ?_, commutator_le_localCore _ _ htwo hLR' hRL', htwo⟩
  rw [← actionImage_localCore m hcore _ ((localResidual_le U).trans inf_le_left)]
  exact actionImage_mono hcoreR

/-- The calculation for a common faithful model of the two literal local action images. -/
theorem displacement_of_local_images (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V)
    (j : Sp E.input.field.Carrier →* MulAut V) (hj : Function.Injective j)
    (hpoint : (pointLocal (F := E.input.field.Carrier)).map j = actionImage (V := V) E.L₁)
    (hplane : (planeLocal (F := E.input.field.Carrier)).map j = actionImage (V := V) E.L₂) :
    RadicalDisplacement E := by
  have hT1 : (T : Subgroup G) ≤ normalizer (E.V₁ : Set G) := m.sylow_le_point_normalizer
  have hT2 : (T : Subgroup G) ≤ normalizer (E.V₂ : Set G) := by
    rw [m.plane_preimage]
    exact m.flag.invariant 1
  obtain ⟨hn1,_,_,htwo1⟩ := local_action_core_bounds m hcore E.V₁ hT1
  obtain ⟨_,hcore2,hcomm2,_⟩ := local_action_core_bounds m hcore E.V₂ hT2
  change actionImage (V := V) E.L₁ ≤ normalizer (actionImage (V := V) E.R₁ : Set (MulAut V)) at hn1
  change IsPGroup 2 (actionImage (V := V) E.R₁) at htwo1
  change (actionImage (V := V) E.L₂).pCoreIn 2 ≤ actionImage (V := V) E.R₂ at hcore2
  change ⁅actionImage (V := V) E.R₂,actionImage (V := V) E.L₂⁆ ≤
    (actionImage (V := V) E.L₂).pCoreIn 2 at hcomm2
  have hc1 : (actionImage (V := V) E.L₁).pCoreIn 2 = (pointRadical (F := E.input.field.Carrier)).map j := by
    rw [← hpoint, ← map_pCoreIn_of_injective 2 _ j hj]
    congr 1
    exact congrArg (Subgroup.map pointLocal.subtype)
      (pointLocal_core_eq E.input.field.card_eq E.input.nonbinary)
  have hc2 : (actionImage (V := V) E.L₂).pCoreIn 2 = (planeRadical (F := E.input.field.Carrier)).map j := by
    rw [← hplane, ← map_pCoreIn_of_injective 2 _ j hj]
    congr 1
    exact congrArg (Subgroup.map planeLocal.subtype)
      (planeLocal_core_eq E.input.field.card_eq E.input.nonbinary)
  let jp := j.comp (planeLocal (F := E.input.field.Carrier)).subtype
  have hjp : Function.Injective jp := hj.comp Subtype.val_injective
  have hrange : jp.range = actionImage (V := V) E.L₂ := by
    rw [MonoidHom.range_comp, range_subtype]
    exact hplane
  have hrad : Plane.radical.map jp = (planeRadical (F := E.input.field.Carrier)).map j := by
    rw [map_map]
  have hmove : ⁅(planeRadical (F := E.input.field.Carrier)).map j,
      actionImage (V := V) E.L₂⁆ = (planeRadical (F := E.input.field.Carrier)).map j := by
    rw [← hrad, ← hrange, MonoidHom.range_eq_map, ← map_commutator,
      Plane.radical_commutator_eq E.input.field.card_eq E.input.nonbinary]
  have hd : ⁅actionImage (V := V) E.R₂,actionImage (V := V) E.L₂⁆ =
      (planeRadical (F := E.input.field.Carrier)).map j := by
    refine le_antisymm (hcomm2.trans hc2.le) ?_
    rw [← hmove]
    exact commutator_mono (hc2.symm.le.trans hcore2) le_rfl
  refine ⟨?_, ?_⟩
  · intro B hB hm hne
    rw [hd]
    have hBrad : B ≤ Plane.radical.map jp := by
      rw [hrad, ← hd]
      exact hm.symm.le.trans (commutator_mono hB le_rfl)
    rw [← hrange] at hm
    exact (plane_moved_image E.input.field.card_eq E.input.nonbinary jp hjp B hBrad hm hne).trans hrad
  · rw [hd]
    intro hR
    have hJ : (planeRadical (F := E.input.field.Carrier)).map j ≤ actionImage (V := V) E.L₁ := by
      rw [← hpoint]
      exact map_mono planeRadical_le_pointLocal
    have hc := (le_inf hR hJ).trans (inf_le_localCore _ _ htwo1 hn1)
    rw [hc1] at hc
    exact planeRadical_not_le_pointRadical ((map_le_map_iff_of_injective hj).mp hc)

/-- Transport both local factors using one reorientation of the original marking. -/
theorem local_image_of_reframed_quotient (m : MarkedFlag E) (hcore : L.pCoreIn 2 = V)
    (σ : MulAut (Sp E.input.field.Carrier)) (A : Subgroup G) (hA : A ≤ L)
    (P : Subgroup (Sp E.input.field.Carrier))
    (hP : (A.subgroupOf L).map (σ.toMonoidHom.comp (componentQuotient m)) = P) :
    P.map ((modelAction m hcore).comp σ.symm.toMonoidHom) = actionImage (V := V) A := by
  rw [← hP, map_map, actionImage_component m hcore A hA, map_map]
  congr 1
  ext l
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

end RadicalGeometry

/-- Original 11.5.7 radical displacement and separation. The only model premises
are the preceding compatible local-residual identities in the marked L/O₂(L).
No radical, displacement, separation or terminal conclusion is assumed. -/
theorem radicalDisplacement_of_local_marking (m : MarkedFlag E)
    (hcore : L.pCoreIn 2 = V)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hpoint : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = pointLocal)
    (hplane : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = planeLocal) :
    RadicalDisplacement E := by
  let j := (RadicalGeometry.modelAction m hcore).comp σ.symm.toMonoidHom
  apply RadicalGeometry.displacement_of_local_images m hcore j
    ((RadicalGeometry.modelAction_injective m hcore).comp σ.symm.injective)
  · exact RadicalGeometry.local_image_of_reframed_quotient m hcore σ E.L₁ E.L₁_le _ hpoint
  · exact RadicalGeometry.local_image_of_reframed_quotient m hcore σ E.L₂
      ((residualIn_le _).trans inf_le_left) _ hplane

/-- The actual moved-seed consumer with its radical-displacement premise discharged. -/
theorem false_of_moved_seed_of_local_marking (m : MarkedFlag E)
    (hcore : L.pCoreIn 2 = V)
    (σ : MulAut (Sp E.input.field.Carrier))
    (hpoint : (E.L₁.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = pointLocal)
    (hplane : (E.L₂.subgroupOf L).map
      (σ.toMonoidHom.comp (RadicalGeometry.componentQuotient m)) = planeLocal)
    (A : Subgroup G) (hAR : A ≤ E.R₁)
    (hAN : A ≤ normalizer (V : Set G))
    (hmoved : ⁅A,E.L₂⁆ = A) (hne : ¬ A ≤ centralizer (V : Set G)) : False :=
  false_of_moved_seed E m (radicalDisplacement_of_local_marking m hcore σ hpoint hplane)
    A hAR hAN hmoved hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal
