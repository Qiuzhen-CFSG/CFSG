module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The original L₃ commutator from Thompson movement

Let Q = C_T(V). The marked original module identifies Ω₁Z(Q) with the
literal reduced module R₂(LT). Transfer the supplied Thompson movement to
the Sylow subgroup of LT and its faithful centralizer-quotient action.
The component image lies in the actual offender subgroup, so complete
known-simple B.5.1 applies to that action and its literal moved space.

The chosen V lies in the moved space because V = [V,L]. Its nonzero fixed
subgroup rules out a complementary fixed space. B.5.1(2) therefore puts the
larger moved space in Irr⁺, and Irr⁺ minimality identifies it with V.
Transporting the displacements to the ambient group gives [Ω₁Z(Q),L] = V.
The final theorem applies the existing cohomological supplement calculation.
Thompson movement remains the explicit premise supplied by the independent
source argument; no classification or commutator callback remains.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 12.4.5,
printed pp.813–814, using B.5.1, pp.99–103.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
open Section02 ChapterB.InternalThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

omit [Finite G] in
private theorem reduced_action_comp :
    (action (ReducedModule (L ⊔ (T : Subgroup G)))).comp
      (actionMk (ReducedModule (L ⊔ (T : Subgroup G)))) =
        reducedRepresentation (L ⊔ (T : Subgroup G)) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  exact action_apply _ g v

/-- The larger moved space is the original chosen member of Irr⁺. -/
private theorem reduced_moved_eq_chosen
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (E : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) : Set G)) :
    subspaceCommutator (reducedRepresentation (L ⊔ (T : Subgroup G))) ⊤
      (L.subgroupOf (L ⊔ (T : Subgroup G))) = D.space := by
  let H := L ⊔ (T : Subgroup G)
  let W := ReducedModule H
  let K := L.subgroupOf H
  let P : Sylow 2 H := T.subtype le_sup_right
  let q := actionMk W
  let σ := action W
  let ρ := reducedRepresentation H
  let B := K.map q
  let J := offenderSubgroup σ
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hKP : K ⊔ (P : Subgroup H) = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hcore : pCore 2 (ActionQuotient W) = ⊥ :=
    isPReduced_reducedPSubgroup.quotient_pCore_eq_bot
  have hmove' : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    intro hc
    apply hmove
    have hj : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le le_sup_right
    rw [← hj]
    rintro _ ⟨a, ha, rfl⟩ z hz
    rw [omega_center_eq_reduced D E h hTV] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact congrArg H.subtype (hc ha w hw)
  have hK : K.IsCComponent := h.maximal_faithful.1.1.1
  let : IsQuasisimple B := quasisimple_of_thompson_movement
    ChapterB.SourceInduction.adequateClassification_knownSimple h.toHypothesis1221.join_sqtk
    P K W hK hKP hcore hmove'
  have hBJ : B ≤ J := component_le_offenderSubgroup P K W hKP hcore hmove'
  obtain ⟨c⟩ := quasisimple_source_conclusion_of_thompson_movement
    h.toHypothesis1221.join_sqtk P K W hK hKP hcore hmove'
  have hcomp : σ.comp q = ρ := reduced_action_comp (T := T) (L := L)
  have hmoved : c.sectionData.space.toSubmodule = subspaceCommutator ρ ⊤ K := by
    rw [c.sectionData.space_eq]
    change subspaceCommutator (σ.comp J.subtype) ⊤ (B.subgroupOf J) = _
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hBJ]
    change subspaceCommutator σ ⊤ (K.map q) = _
    rw [← subspaceCommutator_comp_map, hcomp]
  have hfixed : fixedSpace (σ.comp J.subtype) (B.subgroupOf J) = fixedSpace ρ K := by
    rw [fixedSpace_subgroupOf σ B J hBJ]
    change fixedSpace σ (K.map q) = _
    rw [← fixedSpace_comp_map, hcomp]
  have hle : D.space ≤ subspaceCommutator ρ ⊤ K := by
    rw [← D.irrPlus.isIrrPlus.choose_spec.1]
    exact subspaceCommutator_mono_left ρ le_top K
  have hn : ¬ IsCompl c.sectionData.space.toSubmodule
      (fixedSpace (σ.comp J.subtype) (B.subgroupOf J)) := by
    intro hc
    rw [hmoved, hfixed] at hc
    have hz : D.space ⊓ fixedSpace ρ K = ⊥ := (hc.disjoint.mono_left hle).eq_bot
    have hi := ReducedNormal.subspaceImage_inf_fixedSpace H D.space L le_sup_left
    change subspaceImage H (D.space ⊓ fixedSpace ρ K) =
      subspaceImage H D.space ⊓ centralizer (L : Set G) at hi
    rw [D.image_eq, hz] at hi
    exact hne (hi.symm.trans (ReducedNormal.subspaceImage_bot H))
  have hirr : IsIrrPlus σ B c.sectionData.space.toSubmodule :=
    (IsIrrPlus.subgroupOf_iff σ B J hBJ _).mp (c.clause_two hn).1
  have hirr' : IsIrrPlus ρ K c.sectionData.space.toSubmodule := by
    have hh := IsIrrPlus.map_embedding ρ σ q (LinearMap.id) Function.injective_id
      (fun g v => by change ρ g v = σ (q g) v; rw [← hcomp]; rfl)
      K c.sectionData.space.toSubmodule hirr
    simpa only [Submodule.map_id] using hh
  rw [hmoved] at hirr'
  exact (IsIrrPlus.eq_of_le ρ D.irrPlus.isIrrPlus hirr' hle).symm

/-- The B.5.1 commutator bound on the original module, with Thompson
movement supplied explicitly. All action and subspace transports are proved. -/
theorem omega_commutator_le_of_thompson_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (E : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) : Set G)) :
    ⁅omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)), L⁆ ≤ V := by
  let H := L ⊔ (T : Subgroup G)
  have he := reduced_moved_eq_chosen D h E hTV hne hmove
  rw [omega_center_eq_reduced D E h hTV, commutator_comm]
  apply commutator_le.mpr
  rintro l hl _ ⟨w, hw, rfl⟩
  let l' : H := ⟨l, mem_sup_left hl⟩
  let v : Additive (ReducedModule H) := Additive.ofMul ⟨w, hw⟩
  have hm : reducedRepresentation H l' v - v ∈ D.space := by
    rw [← he]
    exact Submodule.subset_span ⟨l', hl, v, Submodule.mem_top, rfl⟩
  rw [← D.image_eq]
  have hm' : (reducedRepresentation H l' v - v).toMul ∈
      D.space.toAddSubgroup.toSubgroup' := hm
  have hmG := mem_map_of_mem H.subtype (mem_map_of_mem (ReducedModule H).subtype hm')
  change l * (w : G) * l⁻¹ / (w : G) ∈ subspaceImage H D.space at hmG
  change l * (w : G) * l⁻¹ * (w : G)⁻¹ ∈ subspaceImage H D.space
  simpa only [commutatorElement_def, div_eq_mul_inv] using hmG

/-- The full source commutator is the original chosen space. The reverse
inclusion uses its original Irr⁺ commutator generation. -/
theorem omega_commutator_eq_of_thompson_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (E : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) : Set G)) :
    ⁅omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)), L⁆ = V :=
  le_antisymm (omega_commutator_le_of_thompson_movement D h E hTV hne hmove)
    (D.eq_commutator.le.trans (commutator_mono (chosen_le_omega_center D) le_rfl))

/-- Actual 12.4.5(2) consumer of the B.5.1 calculation, conditional only
on the independently supplied Thompson movement. -/
theorem fixed_supplement_of_thompson_movement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (E : SLThreeExtension D)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) : Set G)) :
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V :=
  fixed_supplement_of_commutator_le D E h hTV hne
    (omega_commutator_le_of_thompson_movement D h E hTV hne hmove)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
