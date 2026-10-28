module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Terminal
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.A5
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.FiniteImages

/-!
# The original deleted-tensor reduction

For the deleted four-dimensional A₅ constituent in 14.4.2(5), the actual
Borel fixes the quotient line V₂/Z(U). Coprime two-layer lifting makes its
two-residual X₂ centralize V₂. Consequently X₂ is outside Y and the first
actor is the original L₁. Commutation of the tensor factors then makes X₂
centralize V, hence normalize L, L₂ and I₂. The quotient marking and the
source conjugator are retained throughout.

This is the reduction preceding the O₂(⟨I₂,H∞⟩) split, not that split's
exclusion or an exhaustive classification of the source actions.
Source: Aschbacher--Smith 14.4.10(3), printed pp.1011–1012.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The source quotient point has binary rank one in every prescribed tensor marking. -/
theorem source_tensor_point_rank (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    finrank (ZMod 2) (c.image (F.Vi 2)) = 1 := by
  let := chosen.elementary
  have hcard : Nat.card (c.image (F.Vi 2)) = 2 :=
    (c.image_card _).trans (card_plane_hat F (by decide)
      ((source_seed_geometry d earlier hq chosen F).2.2 hne))
  let : Finite (c.image (F.Vi 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := c.image (F.Vi 2))
  rw [Nat.card_zmod, hcard] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm

/-- The deleted constituent forces the original X₂ to centralize V₂. -/
theorem source_tensor_deleted_plane_centralizer (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    second F.H (T : Subgroup G) ≤ centralizer (F.Vi 2 : Set G) := by
  let := chosen.elementary
  have hcent : (center F.U).map F.U.subtype = F.Vi 1 := hZ
  have hfix := TensorDeleted.second_fixes_image c hdel (T.subtype (F.invariant 1))
    (map_subgroupOf_eq_of_le (F.invariant 1)) (F.invariant 2)
    (source_tensor_point_rank d earlier hq chosen F hne c)
  have hbound := TensorDeleted.commutator_le_center_of_fixed_image c
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) (second_le _ _) hfix
  rw [hcent] at hbound
  have hp : IsPGroup 2 (F.Vi 1) :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (F.le_seed 1))
      (inclusion_injective _)
  have hH : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  exact A5.second_centralizes_of_two_layers hp ((second_le _ _).trans hH) hbound

/-- The source reduction before the two-core split in the deleted tensor case.
The actual first actor is L₁, the second centralizes V and normalizes I₂.
All source marks, including the original conjugator g, are retained. -/
theorem source_tensor_deleted_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    XFamily F.H (T : Subgroup G) = {first F.H, second F.H (T : Subgroup G)} ∧
      first F.H ≠ second F.H (T : Subgroup G) ∧
      second F.H (T : Subgroup G) ∉ YFamily F.H T (F.Vi 2) (F.E g) ∧
      F.Li L 1 = first F.H ∧
      second F.H (T : Subgroup G) ≤ centralizer (F.Vi 2 : Set G) ∧
      second F.H (T : Subgroup G) ≤ centralizer (V : Set G) ∧
      second F.H (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      second F.H (T : Subgroup G) ≤ normalizer (F.Li L 2 : Set G) ∧
      second F.H (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have hcent : (center F.U).map F.U.subtype = F.Vi 1 := hZ
  have hplane := source_tensor_deleted_plane_centralizer d earlier hq chosen F hne hZ c hdel
  obtain ⟨hpair,hneq⟩ := family_eq_pair_of_model (T.subtype (F.invariant 1))
    (map_subgroupOf_eq_of_le (F.invariant 1)) c.actor_models
  have hnot : second F.H (T : Subgroup G) ∉ YFamily F.H T (F.Vi 2) (F.E g) := by
    intro hy
    have he : movedSpace (F.Vi 2) (second F.H (T : Subgroup G)) = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hplane)
    have hc := hy.2.1
    rw [he, Subgroup.card_bot] at hc
    norm_num at hc
  have hfirst := source_first_actor d earlier hq chosen structural F g hg
  have hL : first F.H = F.Li L 1 := A5.first_eq_L₁_of_second_not_mem_Y hpair hfirst.1 hnot
  have hmove : movedSpace (F.Vi 2) (first F.H) = V := by rw [hL]; exact hfirst.2.1
  have hfix := TensorDeleted.second_fixes_first_moved_image c hdel
    (T.subtype (F.invariant 1)) (map_subgroupOf_eq_of_le (F.invariant 1)) (F.invariant 2)
    (source_tensor_point_rank d earlier hq chosen F hne c)
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
  rw [hmove] at hfix
  have hbound := TensorDeleted.commutator_le_center_of_fixed_image c
    (le_conjugateSpanBy V F.H) (second_le _ _) hfix
  rw [hcent] at hbound
  have hp : IsPGroup 2 (F.Vi 1) :=
    (IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (F.le_seed 1))
      (inclusion_injective _)
  have hH : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hV := A5.second_centralizes_of_two_layers hp ((second_le _ _).trans hH) hbound
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hM := hV.trans (h.seed_centralizer_le structural unique)
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  obtain ⟨e,_,_,_,hIG,hIN,_⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare
    (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  have hI := (hplane.trans (Subgroup.centralizer_le_normalizer _)).trans
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN)
  have hLN : (L.subgroupOf (normalizer (L : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer L.le_normalizer).mpr le_rfl
  have hL₂ := A5.second_normalizes_L₂ L.le_normalizer hLN hM hplane
    (LargerDimension.LocalAction.NaturalFlags.Li_eq_residual F 2)
  exact ⟨hpair,hneq,hnot,hL.symm,hplane,hV,hM,hL₂,hI⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
