module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCubicModule

/-!
# The containing core's exact action on the original module

The original wreath action gives [T:O₂(L₀T)]=128, whereas the actual
parabolic quotient gives [T:O₂(H)]=8. Hence O₂(H) has action image of
order sixteen on V. Under collapse, the previously proved equality of
action images transfers this calculation to Q=O₂(K).

The kernel of this literal action of Q is Q∩O₂(L₀T), of index sixteen
in Q. It contains the original cubic moved subgroup [V,P], of order
sixteen. Consequently 16 divides the order of the common kernel and
256 divides the order of Q. All intersections, quotient maps, the cubic
complement, and the original module are retained. The last two theorems
apply these calculations to the actual remaining source configuration
and the two requested source contracts.

This does not exclude the collapsed configuration. Its exclusion and
assembly of StabilizerNormalizerAt and HalfSylowUniqueAt remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only external
premise; its final discharge remains with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

private theorem sylow_core_relIndex {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) :
    (pCore 2 A).relIndex (S : Subgroup A) =
      2 ^ (Nat.card (A ⧸ pCore 2 A)).factorization 2 := by
  have hh := relIndex_ker (S : Subgroup A) (QuotientGroup.mk' (pCore 2 A))
  rw [QuotientGroup.ker_mk'] at hh
  rw [hh]
  exact (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 A))).card_eq_multiplicity

/-- The full original Sylow acts with image of order 128. -/
theorem LiftData.join_core_relIndex_sylow (f : LiftData s hz) :
    ((localJoin T L).pCoreIn 2).relIndex (T : Subgroup G) = 128 := by
  let J := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hk : ((J.pCoreIn 2).subgroupOf J) = pCore 2 J :=
    comap_map_eq_self_of_injective J.subtype_injective _
  rw [←relIndex_subgroupOf (show (T : Subgroup G) ≤ J from le_sup_right),hk,
    ←f.kernel_eq_join_core,relIndex_ker]
  change Nat.card (S.mapSurjective f.surjective) = 128
  rw [Sylow.card_eq_multiplicity,RegularWreathProduct.card,Matrix.PSL3Two.card_SL]
  change 2 ^ (168 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 2 = 128
  rw [Nat.card_zmod]
  decide +kernel

namespace Parabolics
variable {H P : Subgroup G}

/-- The quotient of the original parabolic Sylow by its own core is dihedral eight. -/
theorem Data.core_relIndex_sylow (h : Data D H) :
    (H.pCoreIn 2).relIndex (T : Subgroup G) = 8 := by
  obtain ⟨e⟩ := h.quotient
  have hk : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [←relIndex_subgroupOf h.sylow_le,hk]
  change (pCore 2 H).relIndex (T.subtype h.sylow_le : Subgroup H) = 8
  rw [sylow_core_relIndex,Nat.card_congr e.toEquiv]
  let a := RegularWreathProduct.congr
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  rw [Nat.card_congr a.toEquiv,RegularWreathProduct.card]
  simp only [Nat.card_perm,Nat.card_fin]
  change 2 ^ (6 ^ Nat.card (ZMod 2) * Nat.card (ZMod 2)).factorization 2 = 8
  rw [Nat.card_zmod]
  decide +kernel

/-- The original parabolic core acts with order sixteen, modulo the original join core. -/
theorem Data.join_core_relIndex_parabolic_core (h : Data D H) (f : LiftData s hz) :
    ((localJoin T L).pCoreIn 2).relIndex (H.pCoreIn 2) = 16 := by
  have hQH : (localJoin T L).pCoreIn 2 ≤ H.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      ((join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le))
    exact h.le_join.trans ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have he := relIndex_mul_relIndex ((localJoin T L).pCoreIn 2) (H.pCoreIn 2)
    (T : Subgroup G) hQH (h.core_le_stabilizer.trans inf_le_left)
  rw [h.core_relIndex_sylow,f.join_core_relIndex_sylow] at he
  omega

/-- The same order sixteen is measured through the literal conjugation action. -/
theorem Data.parabolic_core_action_card (h : Data D H) (f : LiftData s hz) :
    Nat.card (((H.pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D)) = 16 := by
  rw [←relIndex_ker,←f.kernel_eq_action_kernel,f.kernel_eq_join_core]
  have hk : (((localJoin T L).pCoreIn 2).subgroupOf (localJoin T L)) =
      pCore 2 (localJoin T L) := comap_map_eq_self_of_injective (localJoin T L).subtype_injective _
  rw [←hk,relIndex_subgroupOf ((pCoreIn_le 2 H).trans h.le_join)]
  exact h.join_core_relIndex_parabolic_core f

/-- In the collapsed case the containing radical has this exact nontrivial action. -/
theorem Data.collapsed_core_action_card (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    Nat.card ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map
      (joinAction D)) = 16 := by
  rw [h.collapsed_core_action_image f hi hP hc]
  exact h.parabolic_core_action_card f

/-- The action kernel on the containing radical has index exactly sixteen. -/
theorem Data.collapsed_core_centralizer_relIndex (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ((enlargedResidual T L H).pCoreIn 2 ⊓ centralizer (D.fullModule : Set G)).relIndex
      ((enlargedResidual T L H).pCoreIn 2) = 16 := by
  rw [inf_relIndex_left,←relIndex_subgroupOf
    (h.enlargedResidual_core_le_intersection.trans
      (inf_le_left.trans (inf_le_left.trans (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)))),
    ←joinAction_ker,relIndex_ker]
  exact h.collapsed_core_action_card f hi hP hc

/-- The containing action kernel is exactly the intersection of the two original cores. -/
theorem Data.core_action_kernel_eq_intersection (h : Data D H) (f : LiftData s hz) :
    (enlargedResidual T L H).pCoreIn 2 ⊓ centralizer (D.fullModule : Set G) =
      (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 := by
  have hk : (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) =
      ((localJoin T L).pCoreIn 2).subgroupOf (localJoin T L) := by
    rw [←joinAction_ker,←f.kernel_eq_action_kernel,f.kernel_eq_join_core]
    exact (comap_map_eq_self_of_injective (localJoin T L).subtype_injective _).symm
  have hQJ : (enlargedResidual T L H).pCoreIn 2 ≤ localJoin T L :=
    h.enlargedResidual_core_le_intersection.trans
      (inf_le_left.trans (inf_le_left.trans le_sup_right))
  ext x
  constructor
  · rintro ⟨hx,hc⟩
    exact ⟨hx,show (⟨x,hQJ hx⟩ : localJoin T L) ∈
      ((localJoin T L).pCoreIn 2).subgroupOf (localJoin T L) from hk ▸ hc⟩
  · rintro ⟨hx,hc⟩
    exact ⟨hx,show (⟨x,hQJ hx⟩ : localJoin T L) ∈
      (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) from hk.symm ▸ hc⟩

/-- The original cubic movement lies in the common kernel of the two core maps. -/
theorem Data.collapsed_cubic_moved_le_common_core (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ⁅D.fullModule,P⁆ ≤
      (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 := by
  have hm := (h.collapsed_cubic_module f hi hP hc).2.1
  exact le_inf (hm.trans inf_le_right)
    ((hm.trans inf_le_left).trans (s.full_eq_local.symm ▸ D.module_le_core))

/-- Both the containing core and its original action kernel have forced two-parts. -/
theorem Data.collapsed_common_core_card_dvd (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    16 ∣ Nat.card ((enlargedResidual T L H).pCoreIn 2 ⊓
      (localJoin T L).pCoreIn 2 : Subgroup G) ∧
      256 ∣ Nat.card ((enlargedResidual T L H).pCoreIn 2) := by
  have hd := card_dvd_of_le (h.collapsed_cubic_moved_le_common_core f hi hP hc)
  rw [(h.collapsed_cubic_module f hi hP hc).1] at hd
  refine ⟨hd,?_⟩
  have hi16 := h.collapsed_core_centralizer_relIndex f hi hP hc
  rw [h.core_action_kernel_eq_intersection f] at hi16
  have he := relIndex_mul_relIndex (⊥ : Subgroup G)
    ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2)
    ((enlargedResidual T L H).pCoreIn 2) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hi16] at he
  rw [←he]
  obtain ⟨n,hn⟩ := hd
  refine ⟨n,?_⟩
  rw [hn]
  omega

end Parabolics
end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction


namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The remaining source configuration has a core action of order sixteen,
with the original cubic movement in the intersection of the two cores. -/
theorem SourceCubicNormalizerEnlargement.exists_core_action_section
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
        (residual H) P (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
      (p % 24 = 11 ∨ p % 24 = 13) ∧
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      ((enlargedResidual T L H).pCoreIn 2 ⊓ centralizer (D.fullModule : Set G)) =
        (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 ∧
      (((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2).relIndex
        ((enlargedResidual T L H).pCoreIn 2) = 16) ∧
      ⁅D.fullModule,P⁆ ≤
        (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 ∧
      16 ∣ Nat.card ((enlargedResidual T L H).pCoreIn 2 ⊓
        (localJoin T L).pCoreIn 2 : Subgroup G) ∧
      256 ∣ Nat.card ((enlargedResidual T L H).pCoreIn 2) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have hk := h.core_action_kernel_eq_intersection f
  have hi := h.collapsed_core_centralizer_relIndex f hs.toLocalInput hP hcollapse
  rw [hk] at hi
  exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,h24,hcollapse,hk,hi,
    h.collapsed_cubic_moved_le_common_core f hs.toLocalInput hP hcollapse,
    h.collapsed_common_core_card_dvd f hs.toLocalInput hP hcollapse⟩

/-- Both original source contracts reduce to the same collapsed configuration
with its literal action kernel and the forced core divisibility. No extra
normalizer, model or point-control premise is introduced. -/
theorem sourceContracts_or_cubicCoreActionSection (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2).relIndex
            ((enlargedResidual T L H).pCoreIn 2) = 16 ∧
          16 ∣ Nat.card ((enlargedResidual T L H).pCoreIn 2 ⊓
            (localJoin T L).pCoreIn 2 : Subgroup G) ∧
          256 ∣ Nat.card ((enlargedResidual T L H).pCoreIn 2) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,_,_,h,_,_,_,_,_,_,_,_,hi,_,hd⟩ := hc.exists_core_action_section
    exact Or.inr ⟨L,D,hc,H,h,hi,hd⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
