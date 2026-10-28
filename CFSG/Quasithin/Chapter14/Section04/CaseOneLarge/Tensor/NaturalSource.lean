module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.CommonSource
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.NaturalConstituent
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Recognition

/-!
# The original natural tensor branch

The selected natural constituent and the original index-two hyperplane
supply the natural geometry, so both tensor residuals lie in Y. The local
14.4.8 commutator identity excludes the alternating-five actor: its marked
second parabolic has cyclic quotient of order three. The symmetric-five
overlap then gives the whole S₃ × S₃ quotient and the actual Partner used
by A₃ recognition.

All group and module identifications are those of the prescribed tensor
row, with the original flag and conjugator. Catalogue exhaustiveness is
separate; no recognition or geometry callback is assumed here.

Source: Aschbacher--Smith 14.4.8(2), 14.4.10(3), printed pp.1009--1011.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

namespace TensorGeometry

/-- The local commutator clause forces a nonabelian whole-parabolic quotient. -/
theorem not_commutative_parabolic {H I₂ L₂ V₂ X E : Subgroup G} {T : Sylow 2 G}
    (hX : X ∈ YFamily H T V₂ E) (a : FullMovedSpaceAction T I₂ L₂ V₂ X) :
    ¬ IsMulCommutative (coreQuotient (X ⊔ (T : Subgroup G))) := by
  intro hab
  let J := X ⊔ (T : Subgroup G)
  let := hab
  have hc : ⁅J, J⁆ ≤ J.pCoreIn 2 := by
    have hh : commutator J ≤ pCore 2 J :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hab
    change ⁅(⊤ : Subgroup J), ⊤⁆ ≤ pCore 2 J at hh
    have hm := map_mono (f := J.subtype) hh
    simpa only [Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype, pCoreIn] using hm
  have hle : X ≤ J.pCoreIn 2 := by
    rw [a.X_commutator]
    exact (commutator_mono le_sup_left (inf_le_left.trans le_sup_right)).trans hc
  exact hX.1.not_le_twoGroup (isPGroup_pCoreIn 2 J) hle

/-- The actual alternating placement has a quotient of order three, which
contradicts the local action clause. -/
theorem symmetric_actor_of_action {H I₂ L₂ V₂ E : Subgroup G} {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ H)
    (hmodel : Nonempty (coreQuotient H ≃* Three × Five) ∨
      Nonempty (coreQuotient H ≃* Three × AltFive))
    (hX : second H T ∈ YFamily H T V₂ E)
    (a : FullMovedSpaceAction T I₂ L₂ V₂ (second H T)) :
    Nonempty (coreQuotient H ≃* Three × Five) := by
  rcases hmodel with hs | hs
  · exact hs
  obtain ⟨ha⟩ := hs
  exfalso
  let S := T.subtype hT
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hT
  let e := Placements.alternatingPlacement S hS ha
  let q := (starCoreQuotientEquiv (sup_le (second_le H T) hT)).trans
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  have hc : Nat.card (coreQuotient (second H T ⊔ (T : Subgroup G))) = 3 :=
    (Nat.card_congr q.toEquiv).trans Theory.SpecificGroups.TensorThreeFive.small_quotient_card
  let : IsCyclic (coreQuotient (second H T ⊔ (T : Subgroup G))) := isCyclic_of_prime_card hc
  let : CommGroup (coreQuotient (second H T ⊔ (T : Subgroup G))) := IsCyclic.commGroup
  exact not_commutative_parabolic hX a inferInstance

end TensorGeometry

/-- In the original natural-tensor row the second residual belongs to Y. -/
theorem source_tensor_natural_second (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hnatural : IsNaturalFour hAD c.constituent) :
    second F.H (T : Subgroup G) ∈ YFamily F.H T (F.Vi 2) (F.E g) := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  let h := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point (by decide) h.two h.frattini_point
  obtain ⟨hpair, _, hfirst, ⟨s⟩⟩ :=
    source_tensor_common d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH c
  obtain ⟨e, f, hf⟩ := hnatural
  let n := TensorGeometry.naturalConstituent c s e f hf
  let A := TensorGeometry.preimage c s.firstSpace
  have hSylow : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map F.H.subtype = T :=
    map_subgroupOf_eq_of_le (F.invariant 1)
  have hPU : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hpoint : Nat.card (Natural.tilde F.U (F.Vi 2)) = 2 :=
    card_plane_hat F (by decide) ((source_seed_geometry d earlier hq chosen F).2.2 hne)
  have hPA : Natural.tilde F.U (F.Vi 2) ≤ Natural.tilde F.U A := by
    apply c.image_le_iff.mp
    rw [show A = TensorGeometry.preimage c s.firstSpace from rfl, TensorGeometry.image_preimage]
    exact s.point_le_fixed.trans s.fixed_le_first
  obtain ⟨hXT, hbound, hindex⟩ := source_tensor_conjugate_geometry d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hfix : ∀ a : F.H, (a : G) ∈ (T : Subgroup G) ∨ (a : G) ∈ F.X g →
      ∀ q ∈ Natural.tilde F.U (F.Vi 2),
        Natural.Geometry.representation c.H_normalizes_U a (Additive.ofMul q) = Additive.ofMul q := by
    intro a ha q hqp
    have hnorm : (a : G) ∈ normalizer (F.Vi 2 : Set G) := by
      rcases ha with ha | ha
      · exact F.invariant 2 ha
      · exact (Subgroup.centralizer_le_normalizer _ (F.X_le_plane_centralizer g hgG ha))
    apply (TensorGeometry.linearCoordinates c).injective
    rw [TensorGeometry.natural_coordinates_equivariant]
    have hv : TensorGeometry.linearCoordinates c (Additive.ofMul q) ∈ c.image (F.Vi 2) := by
      rw [TensorGeometry.image_eq_map]
      exact ⟨Additive.ofMul q, hqp, rfl⟩
    have ha' : c.actor (QuotientGroup.mk' (pCore 2 F.H) a) ∈
        c.actorImage (F.H ⊓ F.Gi 2) := ⟨_, ⟨a, ⟨a.property, hnorm⟩, rfl⟩, rfl⟩
    exact c.point_fixed_of_normalizes (show F.H ⊓ F.Gi 2 ≤ F.H from inf_le_left)
      inf_le_right (source_tensor_point_rank d earlier hq chosen F hne c) hv ⟨_, ha'⟩
  obtain ⟨coords⟩ := Natural.Geometry.exists_coordinates_of_model c.H_normalizes_U n
    (Natural.geometry_placements_of_sylow (T.subtype (F.invariant 1)) hSylow n.componentEquiv c.actor_models)
    c.actor_models hpoint hPA hfix
    (source_tensor_actor_card d earlier hq chosen structural alternatives F hne hZ g hgP hgH c).2
  have hZP : center F.U ≤ (F.Vi 2).subgroupOf F.U := by
    intro z hz
    exact F.monotone (by omega : 1 ≤ 2) (hZ ▸ (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩))
  have hPE : F.Vi 2 ≤ F.E g :=
    (F.le_seed 2).trans (F.seed_le_E_of_normalizes g (chosen.normalizes hg))
  have hsecond : second F.H (T : Subgroup G) ∈ XFamily F.H (T : Subgroup G) := by
    rw [hpair]; simp
  exact coords.second_mem_Y hsecond
    (source_closure_le_sylow d earlier hq chosen structural alternatives F) hPU hZP
    (hZP.trans (subgroupOf_mono F.U hPE)) (TensorGeometry.preimage_le c _)
    (hXT.trans (F.invariant 1))
    (TensorGeometry.preimage_le_hyperplane c s hindex hbound)
    (by rwa [commutator_comm])

/-- The natural tensor row constructs the actual partner, including the
whole S₃ × S₃ quotient, without any geometry callback. -/
theorem source_tensor_natural_partner (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hnatural : IsNaturalFour hAD c.constituent) : Partner T L V F g := by
  have hsecond := source_tensor_natural_second d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH c hnatural
  obtain ⟨hpair, hneq, hfirst, _⟩ :=
    source_tensor_common d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH c
  let a := source_local_data d earlier hq chosen structural alternatives classification
    F hne hZ g hg hgP hgH
  obtain ⟨e⟩ := TensorGeometry.symmetric_actor_of_action (F.invariant 1) c.actor_models
    hsecond (a.action _ hsecond)
  let q := Placements.overlapQuotient (T.subtype (F.invariant 1))
    (map_subgroupOf_eq_of_le (F.invariant 1)) e
  have hquot (A : Subgroup G) (hA : A = overlap F.H T) :
      Nonempty (coreQuotient A ≃* Three × Three) := by
    subst A
    exact ⟨q⟩
  have hL := (source_first_actor d earlier hq chosen structural F g hg).1
  have hLX : F.Li L 1 ∈ XFamily F.H T := hL.1
  rw [hpair] at hLX
  rcases Set.mem_insert_iff.mp hLX with heq | heq
  · refine ⟨second F.H T, hsecond, ?_, ?_⟩
    · rw [heq]
      exact hneq.symm
    · apply hquot
      rw [heq]
      rfl
  · have heq := Set.mem_singleton_iff.mp heq
    refine ⟨first F.H, hfirst, ?_, ?_⟩
    · rw [heq]
      exact hneq
    · apply hquot
      rw [heq, sup_comm (second F.H (T : Subgroup G)) (first F.H)]
      rfl

/-- The existing A₃ recognition closes the original natural tensor branch. -/
theorem source_tensor_natural_contradiction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hnatural : IsNaturalFour hAD c.constituent) : False :=
  contradiction_of_partner d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hg hgP hgH
    (source_tensor_natural_partner d earlier hq chosen structural alternatives classification
      F hne hZ g hg hgP hgH c hnatural)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
