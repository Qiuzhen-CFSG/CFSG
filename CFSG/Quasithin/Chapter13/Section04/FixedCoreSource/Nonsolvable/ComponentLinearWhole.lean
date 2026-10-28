module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearModule
public import CFSG.Quasithin.Chapter12.Section08.Setup.ChosenLinearThree
public import Theory.Representation.PSL3Two.DoubledCentralFour
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The whole reduced moved module of the selected linear-three component

The constructed natural omega-orbit makes K supplement O₂(KT). Classify
W=[R₂(KT),K] using B.5.1: in the minimal case its nonzero fully moved
omega-orbit equals W. In the doubled case, the core centralizes W and
both natural summands are KT-normal. Their Sylow-fixed lines already
span the full central four-group, forcing the escaping central involution
into a fixed-free module. This contradiction proves the literal equality
without an additional whole-module or minimality premise.

The same application identifies the action kernel of the original full
omega-orbit and KT/O₂(KT). Both original A₆ covering rows are allowed.
The earlier module and structural premises and LargeDistanceInput retain
the producers documented in ComponentLinearModule. Their final discharge
belongs to qt-d-1341-fixed-core-source. The covered-original linear row,
selected covered-A₆ fixed-free row, centralizer-overgroup equality and
comparison/commutator/graph assembly remain with qt-d-1341-nonsolvable-source.
Universal nonsolvability is still needed at both escaping weights; no
universal Structural1222 is inferred from Structural1222At.
Source: Aschbacher–Smith 13.4.10(1,4–5), printed pp.907–909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter12.Section08 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- The constructed natural omega-orbit is the whole reduced moved module.
Its full action also identifies the literal quotient of KT. -/
theorem linear_component_whole
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let H := K ⊔ (T : Subgroup G)
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    U = ⁅(ReducedModule H).map H.subtype,K⁆ ∧
      H ⊓ centralizer (U : Set G) = H.pCoreIn 2 ∧
      H ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K : Set G) =
        H.pCoreIn 2 ∧
      K ⊔ H.pCoreIn 2 = H ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BinaryLinearThree.Group) := by
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let A := K.subgroupOf H
  let B := U.subgroupOf H
  let R := ReducedModule H
  let W := ⁅R,A⁆
  have hKH : K ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  obtain ⟨DK,q,e,he,_,_,_,hfour⟩ := linear_component_marking hl h₀ h structural modules
    D m h1332 fixed hindex z hzT hzL hKz hHN hKM hfK eK
  have hUH : U ≤ H := DK.le_reduced.trans (map_subtype_le _)
  have hredU := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hHU : H ≤ normalizer (U : Set G) :=
    le_normalizer_of_normal_subgroupOf hUH (hK := hredU.normal)
  obtain ⟨hC,hsupp,hquot⟩ := chosen_linear_three_join DK (hTH.trans hHU) q e he
  refine ⟨?_,hC,(component_seed_action_kernel h₀ hzT hz1 hKz hTK).trans hC,hsupp,hquot⟩
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let : B.Normal := hredU.normal
  let : Group.IsPerfect A := hfK.1.1.perfect
  have hperfect : IsPPerfect 2 A := by
    intro N hN hQ
    let := hN
    have hh : Subsingleton (A ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hQ.isNilpotent
    apply eq_top_iff.mpr
    intro a _
    exact (QuotientGroup.eq_one_iff a).mp (Subsingleton.elim _ _)
  let S := T.subtype hTH
  have hsup : A ⊔ (S : Subgroup H) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hKH hTH,subgroupOf_self]
  have hres : pResidual 2 H = A :=
    pResidual_eq_of_isPPerfect_sup A (S : Subgroup H) hperfect S.isPGroup' hsup
  have hred : IsPReduced 2 W := by
    have hh := (isPReduced_reducedPSubgroup (p := 2) (G := H)).moved R
    rwa [hres] at hh
  let : W.Normal := hred.normal
  let : IsElementaryAbelian 2 W := hred.elementary
  have hmove : ⁅W,A⁆ = W := commutator_isPPerfect_idempotent A R hperfect
    (IsElementaryAbelian.isPGroup 2 R) le_normalizer_of_normal
  have hBmove : ⁅B,A⁆ = B := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hKH]
    exact component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hBW : B ≤ W := by
    rw [←hBmove]
    exact commutator_mono hredU.le_reducedPSubgroup le_rfl
  have hBne : B ≠ ⊥ := by
    intro hh
    have hm := congrArg (map H.subtype) hh
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hm
    exact DK.ne_bot hm
  have hWne : W ≠ ⊥ := fun hh => hBne (bot_unique (hBW.trans_eq hh))
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  let a := subgroupOfEquivOfLe hKH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let := component_quotient_quasisimple h1332 hfK
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hcard : Nat.card (A ⧸ pCore 2 A) = 168 := by
    rw [Nat.card_congr (aq.trans eK).toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    norm_num
  have hgenA : ⁅A,elementaryAbelianMaxJ (S : Subgroup H)⁆ = A := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKH,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change ⁅K,elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype)⁆ = K
    rw [map_subgroupOf_eq_of_le hTH]
    exact component_thompson_generation (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  rcases linear_reduced_component_minimal_or_double S A W hSQ hred hfK.1.1
      hqA hcard hsup hgenA hmove hWne with hmin | ⟨qW,eW,heW⟩
  · have hEq : B = W := (hmin B hBW le_normalizer_of_normal).resolve_right (by
      intro hc
      have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
      rw [hBmove] at hh
      exact hBne hh)
    have hm := congrArg (map H.subtype) hEq
    rwa [map_subgroupOf_eq_of_le hUH,map_commutator,map_subgroupOf_eq_of_le hKH] at hm
  · have hAC : A ⊔ pCore 2 H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,←MonoidHom.range_eq_map,range_subtype]
      exact hsupp
    let zH : H := ⟨z.val,hTH ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).1⟩
    have hzS : zH ∈ omegaOneCenterAmbient (S : Subgroup H) := by
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨((mem_omegaOneCenterAmbient_iff _ _).mp hzT).1,?_,?_⟩
      · exact Subtype.ext ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1
      · intro t ht
        exact Subtype.ext (((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2 t.val ht)
    have hzA : zH ∈ centralizer (A : Set H) := by
      intro k hk
      apply Subtype.ext
      exact (hKz hk z.val (Set.mem_singleton _)).symm
    have hZ : (omegaOneCenterAmbient (S : Subgroup H)).map H.subtype =
        omegaOneCenterAmbient (T : Subgroup G) := by
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
      change omegaOneCenterAmbient (((T : Subgroup G).subgroupOf H).map H.subtype) = _
      rw [map_subgroupOf_eq_of_le hTH]
    have hfourS : Nat.card (omegaOneCenterAmbient (S : Subgroup H)) = 4 := by
      rw [←hfour,←hZ]
      exact Nat.card_congr (equivMapOfInjective _ _ H.subtype_injective).toEquiv
    exact (doubled_natural_not_central_four S A W hAC hred.le_pCore
      (le_centralizer_iff.mp hred.le_centralizer_pCore)
      (qW.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A)))
      (qW.surjective.comp (QuotientGroup.mk'_surjective _)) eW heW hzS
      (fun hh => hz1 (congrArg Subtype.val hh)) hzA hfourS).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
