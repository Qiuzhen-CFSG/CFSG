module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Movement
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.PCoreImage

/-!
# The two-core commutator in the natural HS branch

Write Q=O₂(H). The parabolic factorization H∩G₂=C_H(V₂)U and
X∩Q=E≤U give [Q,X]≤U. The image of X in the literal S₅ quotient
is nontrivial. Its normal closure contains the perfect residual, so the
commutator bound extends to the original component K. Together with
[U,K]=U and U≤O₂(K), this proves U=[O₂(K),K].

All component fields are constructed here. Natural coordinates remain a
source obligation of qt-d-hs-action-source; centerlessness belongs to
qt-d-hs-local-structure. The earlier source inputs retain their original
owners described in SourceAction.Geometry.

Source: Aschbacher--Smith 14.3.32(4), printed p.1004.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem parabolic_core_bound [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) (htwo : IsPGroup 2 F.U)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hindex : F.W.relIndex F.U = 2)
    (g : G) (hg : g ∈ F.Gi 2) (hinter : F.X g ⊓ F.H.pCoreIn 2 ≤ F.U) :
    ⁅F.H.pCoreIn 2, F.X g⁆ ≤ F.U := by
  let Q := F.H.pCoreIn 2
  let C := centralizer (F.Vi 2 : Set G)
  let D := commutatorPreimage F.H (F.X g) F.U
  have hHU := le_normalizer_conjugateSpanBy V F.H
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes htwo F.U_le_H hHU
  have hQH : Q ≤ F.H := pCoreIn_le 2 F.H
  have hHQ : F.H ≤ normalizer (Q : Set G) := F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hh hq
    exact hx
  have hUG : F.U ≤ F.Gi 2 := F.U_le_G₂_of_commutator hcomm
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  let : IsElementaryAbelian 2 (F.Vi 2) :=
    IsElementaryAbelian.of_injective (inclusion (F.le_seed 2)) (inclusion_injective _)
  have hfact := F.H2_eq_plane_centralizer_sup_U (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex)
  have hUD : F.U ≤ D := le_commutatorPreimage F.U_le_H
    (le_normalizer_iff_commutator_le_left.mp (F.X_normalizes_U g hg))
  have hCD : Q ⊓ C ≤ D := by
    apply le_commutatorPreimage (inf_le_left.trans hQH)
    apply le_trans (le_inf
      (le_normalizer_iff_commutator_le_right.mp
        (inf_le_right.trans (F.plane_centralizer_normalizes_actors g hg).1))
      ((commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp ((F.X_le_H g hg).trans hHQ))))
      hinter
  have hQD : Q ≤ D := by
    intro q hq
    have hqgen : q ∈ C ⊔ F.U := hfact ▸ ⟨hQH hq, F.invariant 2 (hQT hq)⟩
    have hprod : ((C ⊔ F.U : Subgroup G) : Set G) = (C : Set G) * (F.U : Set G) :=
      coe_mul_of_right_le_normalizer_left C F.U
        (hUG.trans (normalizer_le_normalizer_centralizer _))
    obtain ⟨c, hc, w, hw, he⟩ := hprod ▸ (show q ∈ ((C ⊔ F.U : Subgroup G) : Set G) from hqgen)
    have hcQ : c ∈ Q := by
      have hcw : c * w ∈ Q := by rwa [show c * w = q from he]
      exact (Q.mul_mem_cancel_right (hUQ hw)).mp hcw
    rw [← he]
    exact D.mul_mem (hCD ⟨hcQ, hc⟩) (hUD hw)
  exact (commutator_mono hQD le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hHU)

private theorem residual_bound_of_symmetricFive {J : Type*} [Group J] [Finite J]
    (e : (J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5))
    (U X : Subgroup J) [U.Normal] (hX : ¬ X ≤ pCore 2 J)
    (hbound : ⁅pCore 2 J, X⁆ ≤ U) : ⁅pCore 2 J, solvableResidual J⁆ ≤ U := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let N := normalClosure (X : Set J)
  let : (N.map f).Normal := Normal.map inferInstance f hf
  have hn : N.map f ≠ ⊥ := by
    intro hn
    have hle := (map_eq_bot_iff N).mp hn
    exact hX ((show X ≤ N from le_normalClosure).trans (hle.trans_eq hk))
  have ha : alternatingGroup (Fin 5) ≤ N.map f :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hn)
  have hm : (solvableResidual J).map f ≤ N.map f := by
    rw [map_solvableResidual_eq f hf,
      Theory.SpecificGroups.SymmetricFive.WreathComponents.symmetric_residual]
    exact ha
  have hp : IsPPerfect 2 (solvableResidual J) := by
    intro A hA hq
    let := hA
    let := hq.isNilpotent
    exact top_unique (by simpa using solvableResidual_le_of_solvable_quotient A)
  have hKN : solvableResidual J ≤ N :=
    isPPerfect_le_of_map_le_of_kernel_normalizes f _ _ hp
      (hk ▸ pCore_isPGroup) le_normalizer_of_normal hm
  exact (commutator_mono le_rfl hKN).trans
    (commutator_normalClosure_le_of_normal _ _ _ hbound)


/-- The original component satisfies the upper commutator bound. -/
theorem source_component_core_bound (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    ⁅(sourceComponent F).pCoreIn 2, sourceComponent F⁆ ≤ F.U := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, _, hVZ⟩ := source_closure d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F alternatives)
  obtain ⟨β, _, b, _, hcuts, _, _⟩ := F.exists_marked_naturalFlag L chosen.normalizes h.full_L_action
  obtain ⟨g, hgP, hgH, _⟩ := SetupFlagGeometry.exists_adjacent_lift F (by decide)
    chosen.normalizes (show (T : Subgroup G) ≤ normalizer (V : Set G) from F.last ▸ F.invariant 3)
    (h.binarySeedAction_surjective F) β b hcuts
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hXH := F.X_le_H g hgG
  have hker := (F.binary_source_action_kernel_intersections (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare
    (source_seed_geometry d earlier hq chosen F).2.1 hne hVZ g hgP hgH).1
  rw [hc.kernel F] at hker
  have hbound : ⁅F.H.pCoreIn 2, F.X g⁆ ≤ F.U :=
    parabolic_core_bound F htwo hcomm
      (source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH).2.2.2
      g hgG (hker.le.trans (inf_le_left.trans inf_le_left))
  have hnot : ¬ (F.X g).subgroupOf F.H ≤ pCore 2 F.H := by
    intro hh
    apply source_conjugate_center_image_nontrivial d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH
    apply le_bot_iff.mp
    rintro _ ⟨z, rfl⟩
    change F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1
    apply (show _ ∈ F.uhatAction.ker from ?_)
    rw [hc.kernel F]
    exact hh (F.conjugate_ZU_le_X g z.property)
  let : (F.U.subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V F.H)
  have hb : ⁅pCore 2 F.H, (F.X g).subgroupOf F.H⁆ ≤ F.U.subgroupOf F.H := by
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hXH]
    exact hbound
  obtain ⟨e, _, _⟩ := hc
  have hr := map_mono (f := F.H.subtype) (residual_bound_of_symmetricFive
    (e.trans Representation.SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv)
    (F.U.subgroupOf F.H) ((F.X g).subgroupOf F.H) hnot hb)
  rw [map_commutator, map_subgroupOf_eq_of_le F.U_le_H] at hr
  exact (commutator_mono
    (pCoreIn_mono_of_normalizes (sourceComponent_le F)
      ((normal_subgroupOf_iff_le_normalizer (sourceComponent_le F)).mp (sourceComponent_normal F)))
    le_rfl).trans hr


/-- Construct the complete original component from the natural-action branch. -/
theorem source_component_of_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) (hc : NaturalCoordinates F) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      F.H = K ⊔ (T : Subgroup G) ∧ F.U = ⁅K.pCoreIn 2, K⁆ ∧
      TildeIndecomposable F K := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have hcard := (source_center_of_natural d earlier hq chosen structural alternatives F hne hI hc).2
  refine ⟨sourceComponent F, sourceComponent_le F, hc.sourceComponent_isCComponent F,
    hc.sourceComponent_supplement F, ?_, hc.tildeIndecomposable F htwo hphi hne hcard⟩
  apply le_antisymm
  · rw [← hc.commutator_eq_self F htwo hphi hne hcard]
    exact commutator_mono (hc.le_component_core F htwo hphi hne hcard) le_rfl
  · exact source_component_core_bound d earlier hq chosen structural alternatives F hne hZ hI hc

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
