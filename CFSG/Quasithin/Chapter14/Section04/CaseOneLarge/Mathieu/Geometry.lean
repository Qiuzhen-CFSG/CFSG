module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.PointStabilizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.SourceAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Hyperplane
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Original Mathieu hyperplane geometry

The literal central quotient U/Z(U), together with a genuine equivariant
Mathieu module marking, gives the source central action. The index-two
plane centralizer contains every Sylow commutator. The native displacement
calculation and properness therefore identify it with the native marked
hyperplane, without assuming compatibility of invariant forms.

Source: Aschbacher--Smith, 12.8.8--11 and 14.4.12, pp.852--854,1011--1012.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Mathieu LargerDimension.LocalAction.Components
open LargerDimension.Mathieu.ModuleGeometry.Native hiding Group

universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The central quotient marking retains the literal original action. -/
@[expose] def mathieuCentralAction (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w)) :
    CentralAction (Q:=F.Uhat) F.H F.U e where
  projection := QuotientGroup.mk' (center F.U)
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  coordinates := c
  normalizes := le_normalizer_conjugateSpanBy V F.H
  equivariant := fun a w => by
    rw [he]
    exact congrArg c (congrArg Additive.ofMul (F.terminalHatAction_apply_mk a w))

/-- Sylow marking determines the actual source hyperplane, without assuming
compatibility between the original and native alternating forms. -/
theorem source_mathieu_hyperplane (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (e : coreQuotient F.H ≃* ActorCatalogue.Native.Model)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] ActorCatalogue.Native.Space)
    (he : ∀ (a : F.H) (w : Additive F.Uhat),
      ActorCatalogue.Native.action (ActorCatalogue.starProjection F.H e a) (c w) =
        c (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w))
    (hS : ((T.subtype (F.invariant 1) : Sylow 2 F.H) : Subgroup F.H).map
      (ActorCatalogue.starProjection F.H e) = markedSylow) :
    (mathieuCentralAction F e c he).image F.W = markedPerp := by
  let := chosen.elementary
  let ca := mathieuCentralAction F e c he
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hTU : (T : Subgroup G) ≤ normalizer (F.U : Set G) :=
    (F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H)
  have hTW : (T : Subgroup G) ≤ normalizer (F.W : Set G) :=
    (le_inf hTU ((F.invariant 2).trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hUT : ⁅F.U,(T : Subgroup G)⁆ ≤ F.W :=
    commutator_le_of_normalized_index_two _ _ _ inf_le_left hindex hTU hTW
  have hU : ca.image F.U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨w,rfl⟩ := c.surjective v
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
    exact ⟨w,⟨a,a.property,ha⟩,rfl⟩
  have hm : subspaceCommutator ActorCatalogue.Native.action ⊤ (markedSylow : Subgroup ActorCatalogue.Native.Model) ≤
      ca.image F.W := by
    have hh := ca.image_mono hUT
    rw [ca.image_commutator _ _ le_rfl (F.invariant 1),hU] at hh
    have ht : ((T : Subgroup G).subgroupOf F.H).map
        (ActorCatalogue.starProjection F.H e) = markedSylow := hS
    rwa [ht] at hh
  apply mathieu_markedPerp_eq_of_le _ (mathieu_markedPerp_le_sylow_moved.trans hm)
  intro htop
  have hcenter : center F.U ≤ F.W.subgroupOf F.U := by
    intro z hz
    exact F.ZU_le_W (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩)
  have hUW : F.U ≤ F.W := ca.le_of_image_le _ _ le_rfl hcenter (by rw [htop]; exact le_top)
  have heq : F.W = F.U := le_antisymm inf_le_left hUW
  rw [heq,relIndex_self] at hindex
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
