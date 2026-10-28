module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallFrattiniAction
public import Theory.GroupAction.Quadratic

/-!
# The original module's quadratic action on the containing Frattini section

Retain the original V, E=<N_G(T₁),H>, K=<O²(H)^E>, and Q=O₂(K).
The inclusions Q≤L₀T and V≤E show that Q and V normalize one another.
Hence [Q,V]≤Q∩V, and V being abelian gives [Q,V,V]=1. The same
conjugation and quotient maps transport this to a quadratic action on
Q/Φ(Q), with displacement in the image of Q∩V.

Under collapse the original cubic moved subgroup [V,P] lies in Q and
therefore acts trivially on this section. Coprime splitting makes the
module action image equal to the image of C_V(P), of order four. Thus
its order divides four. The original cubic image centralizes this actor;
the earlier common-kernel calculation gives fixed index dividing sixteen.
If the image has order four, this is an index bound by its squared order.

No nontriviality is asserted: the exact criterion for a trivial image is
[V,Q]≤Φ(Q). In particular, neither the faithful K/O₂(K) action nor the
fixed-index bound alone supplies a nontrivial actor of ratio at most two.
The last two applications retain the original source configuration and
both requested contracts. Exclusion of that configuration, including the
possible trivial or order-two image, and final assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only external
premise, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The action image of the original full module, in the literal core Frattini action. -/
def moduleFrattiniImage (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) : Subgroup (MulAut (CoreFrattiniSection T L H)) :=
  (D.fullModule.subgroupOf (enlargement T L H)).map (coreFrattiniAction T L H)

/-- The original module lies in the actual normalizer enlargement. -/
theorem Data.fullModule_le_enlargement (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) : D.fullModule ≤ enlargement T L H := by
  rw [hfull]
  exact D.module_le_core.trans ((join_core_le_stabilizer D).trans
    (inf_le_left.trans (h.sylow_le.trans le_sup_right)))

/-- Inner conjugation by the containing two-core is trivial on its Frattini quotient. -/
theorem Data.core_le_frattiniAction_kernel (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ((enlargedResidual T L H).pCoreIn 2).subgroupOf (enlargement T L H) ≤
      (coreFrattiniAction T L H).ker := by
  intro q hq
  obtain ⟨k,hk,he⟩ := hq
  have hh : k ∈ ((coreFrattiniAction T L H).comp
      (inclusion h.enlargedResidual_le_enlargement)).ker :=
    h.coreFrattiniAction_kernel hn ▸ hk
  have he' : inclusion h.enlargedResidual_le_enlargement k = q := Subtype.ext he
  exact he' ▸ hh

/-- Mutual normalization puts the original commutator in both groups. -/
theorem Data.core_module_commutator_le (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    ⁅(enlargedResidual T L H).pCoreIn 2,D.fullModule⁆ ≤
      D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 := by
  have hQJ : (enlargedResidual T L H).pCoreIn 2 ≤ localJoin T L :=
    h.enlargedResidual_core_le_intersection.trans
      (inf_le_left.trans (inf_le_left.trans le_sup_right))
  have hQV : (enlargedResidual T L H).pCoreIn 2 ≤ normalizer (D.fullModule : Set G) := by
    rw [hfull]
    exact hQJ.trans D.join_normalizes_module
  exact le_inf (le_normalizer_iff_commutator_le_right.mp hQV)
    (le_normalizer_iff_commutator_le_left.mp
      ((h.fullModule_le_enlargement hfull).trans (enlargement_normalizes_core T L H)))

/-- The original abelian module acts quadratically already on the containing core. -/
theorem Data.core_module_double_commutator (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    ⁅⁅(enlargedResidual T L H).pCoreIn 2,D.fullModule⁆,D.fullModule⁆ = ⊥ := by
  let : IsElementaryAbelian 2 D.fullModule := hfull.symm ▸ D.module_elementary
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact (h.core_module_commutator_le hfull).trans inf_le_left |>.trans
    (le_centralizer_iff_isMulCommutative.mpr inferInstance)

/-- The actual image inherits elementary abelianness from the original module. -/
theorem Data.moduleFrattiniImage_elementary (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    IsElementaryAbelian 2 (moduleFrattiniImage D H) := by
  let : IsElementaryAbelian 2 D.fullModule := hfull.symm ▸ D.module_elementary
  let : IsElementaryAbelian 2 (D.fullModule.subgroupOf (enlargement T L H)) :=
    IsElementaryAbelian.subgroupOf (h.fullModule_le_enlargement hfull)
  exact IsElementaryAbelian.map _

/-- Frattini displacement lies in the image of the original module-core intersection. -/
theorem Data.moduleFrattiniImage_displacement (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    commutatorAction (moduleFrattiniImage D H) (CoreFrattiniSection T L H) ≤
      (D.fullModule.subgroupOf ((enlargedResidual T L H).pCoreIn 2)).map
        (QuotientGroup.mk' _) := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let π := QuotientGroup.mk' (frattini Q)
  rw [commutatorAction_eq_closure,closure_le]
  rintro _ ⟨a,w,rfl⟩
  obtain ⟨v,hv,he⟩ := a.property
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) w
  change (π q)⁻¹ * (a : MulAut (CoreFrattiniSection T L H)) (π q) ∈ _
  rw [←he,coreFrattiniAction_mk,←map_inv,←map_mul]
  apply mem_map_of_mem
  change (q:G)⁻¹ * ((v:G) * (q:G) * (v:G)⁻¹) ∈ D.fullModule
  have hc := (h.core_module_commutator_le hfull).trans inf_le_left
    (commutator_mem_commutator (Q.inv_mem q.property) hv)
  simpa only [commutatorElement_def,inv_inv,mul_assoc,coe_subtype] using hc

/-- The original module fixes its own image inside the Frattini section. -/
theorem Data.moduleFrattiniImage_fixes_module_image (_h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    (D.fullModule.subgroupOf ((enlargedResidual T L H).pCoreIn 2)).map
      (QuotientGroup.mk' _) ≤
        FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H) := by
  let : IsElementaryAbelian 2 D.fullModule := hfull.symm ▸ D.module_elementary
  rintro w ⟨q,hq,rfl⟩ a
  obtain ⟨v,hv,he⟩ := a.property
  change (a : MulAut (CoreFrattiniSection T L H)) (QuotientGroup.mk' _ q) = _
  rw [←he,coreFrattiniAction_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  change (v:G) * (q:G) * (v:G)⁻¹ = (q:G)
  have hh := congrArg Subtype.val (mul_comm (⟨v,hv⟩ : D.fullModule) ⟨q,hq⟩)
  change (v:G) * (q:G) = (q:G) * (v:G) at hh
  rw [hh,mul_inv_cancel_right]

/-- The literal module action is quadratic on the containing-core Frattini section. -/
theorem Data.moduleFrattiniImage_quadratic (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    commutatorAction₂ (moduleFrattiniImage D H) (CoreFrattiniSection T L H) = ⊥ := by
  apply le_antisymm _ bot_le
  apply (closure_le (K := (⊥ : Subgroup (CoreFrattiniSection T L H)))).mpr
  rintro _ ⟨a,w,hw,rfl⟩
  have hf := ((h.moduleFrattiniImage_displacement hfull).trans
    (h.moduleFrattiniImage_fixes_module_image hfull)) hw a
  rw [hf,inv_mul_cancel]
  exact one_mem _

/-- Under collapse, the cubic fixed subgroup induces the entire module action. -/
theorem Data.collapsed_moduleFrattiniImage_eq_fixed_image (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    moduleFrattiniImage D H =
      ((D.fullModule ⊓ centralizer (P : Set G)).subgroupOf (enlargement T L H)).map
        (coreFrattiniAction T L H) := by
  let E := enlargement T L H
  let Q := (enlargedResidual T L H).pCoreIn 2
  have he := (h.collapsed_module_fixed_supplement f hi hP hc).1
  have hVE := h.fullModule_le_enlargement s.full_eq_local
  have he' := congrArg (fun B : Subgroup G =>
    (B.subgroupOf E).map (coreFrattiniAction T L H)) he
  rw [subgroupOf_sup (inf_le_left.trans hVE) (inf_le_left.trans hVE),Subgroup.map_sup] at he'
  have hz' : ((D.fullModule ⊓ Q).subgroupOf E).map (coreFrattiniAction T L H) = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (subgroupOf_mono E inf_le_right).trans (h.core_le_frattiniAction_kernel hn)
  rw [hz',bot_sup_eq] at he'
  exact he'

/-- The actual module action image has order dividing four, allowing the trivial image. -/
theorem Data.collapsed_moduleFrattiniImage_card_dvd (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    Nat.card (moduleFrattiniImage D H) ∣ 4 := by
  rw [h.collapsed_moduleFrattiniImage_eq_fixed_image f hn hi hP hc]
  have hh := card_map_dvd ((D.fullModule ⊓ centralizer (P : Set G)).subgroupOf
    (enlargement T L H)) (coreFrattiniAction T L H)
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (inf_le_left.trans (h.fullModule_le_enlargement s.full_eq_local))).toEquiv,
    f.cubic_fixed_card (hi.complement_le.trans ((map_subtype_le _).trans h.le_join))
      hi.odd_complement.isPGroup hP] at hh
  exact hh

/-- The fixed-index bound belongs to the same faithful action image. -/
theorem Data.collapsed_moduleFrattiniImage_fixed_index (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ∣ 16 := by
  have hle : commonFrattiniImage T L H ≤
      FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H) := by
    intro w hw a
    obtain ⟨v,hv,he⟩ := a.property
    change (a : MulAut (CoreFrattiniSection T L H)) w = w
    rw [←he]
    exact h.fullModule_fixes_commonFrattiniImage s.full_eq_local v hv w hw
  exact h.commonFrattiniImage_index f hi hP hc ▸ index_dvd_of_le hle

omit [Finite G] in
/-- The precise ambient commutator criterion for an element to act trivially. -/
theorem coreFrattiniAction_eq_one_iff (v : enlargement T L H) :
    coreFrattiniAction T L H v = 1 ↔
      ∀ q ∈ (enlargedResidual T L H).pCoreIn 2,
        ⁅(v:G),q⁆ ∈ (frattini ((enlargedResidual T L H).pCoreIn 2)).map
          ((enlargedResidual T L H).pCoreIn 2).subtype := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  constructor
  · intro hv q hq
    let q' : Q := ⟨q,hq⟩
    have he := congrArg (fun a : MulAut (CoreFrattiniSection T L H) =>
      a (QuotientGroup.mk' _ q')) hv
    rw [coreFrattiniAction_mk] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    refine ⟨_,hm,?_⟩
    change (v:G) * q * (v:G)⁻¹ / q = _
    simp only [commutatorElement_def,div_eq_mul_inv]
  · intro hv
    apply MulEquiv.ext
    intro w
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) w
    rw [coreFrattiniAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨x,hx,he⟩ := hv q q.property
    have hh : x = Q.normalizerMonoidHom
        ⟨v,enlargement_normalizes_core T L H v.property⟩ q / q := by
      apply Subtype.ext
      change (x:G) = (v:G) * (q:G) * (v:G)⁻¹ / (q:G)
      simpa only [commutatorElement_def,div_eq_mul_inv,coe_subtype] using he
    exact hh ▸ hx

/-- Triviality of the module action is exactly the original Frattini containment. -/
theorem Data.moduleFrattiniImage_eq_bot_iff (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    moduleFrattiniImage D H = ⊥ ↔
      ⁅D.fullModule,(enlargedResidual T L H).pCoreIn 2⁆ ≤
        (frattini ((enlargedResidual T L H).pCoreIn 2)).map
          ((enlargedResidual T L H).pCoreIn 2).subtype := by
  rw [moduleFrattiniImage,Subgroup.map_eq_bot_iff,commutator_le]
  constructor
  · intro hh v hv q hq
    exact (coreFrattiniAction_eq_one_iff
      (⟨v,h.fullModule_le_enlargement hfull hv⟩ : enlargement T L H)).mp
        (hh hv) q hq
  · intro hh v hv
    exact (coreFrattiniAction_eq_one_iff v).mpr (hh v hv)

/-- The same original cubic complement centralizes the module action image. -/
theorem Data.collapsed_cubic_centralizes_moduleFrattiniImage (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (P.subgroupOf (enlargement T L H)).map (coreFrattiniAction T L H) ≤
      centralizer (moduleFrattiniImage D H : Set (MulAut (CoreFrattiniSection T L H))) := by
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_antisymm _ bot_le
  apply commutator_le.mpr
  rintro a ⟨v,hv,rfl⟩ b ⟨p,hp,rfl⟩
  rw [mem_bot,←map_commutatorElement]
  apply h.core_le_frattiniAction_kernel hn
  exact ((h.cubic_module_moved_le_residual_core hfull hi).trans hc)
    (commutator_mem_commutator hv hp)

/-- An image of order four has the index-square bound; its order is not inferred here. -/
theorem Data.collapsed_moduleFrattiniImage_four_bound (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hfour : Nat.card (moduleFrattiniImage D H) = 4) :
    (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ≤
      Nat.card (moduleFrattiniImage D H) ^ 2 := by
  rw [hfour]
  exact Nat.le_of_dvd (by decide) (h.collapsed_moduleFrattiniImage_fixed_index f hi hP hc)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original remaining source witness supplies a quadratic action of its
own module on the same faithful containing-core Frattini section. Its image
has order dividing four; nontriviality is equivalent to the displayed
ambient commutator not lying in Frattini, and is not assumed here. -/
theorem SourceCubicNormalizerEnlargement.exists_quadratic_frattini_action
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      (∃ a : XiQuotient (enlargedResidual T L H) →* MulAut (CoreFrattiniSection T L H),
        Function.Injective a ∧ ∀ k : enlargedResidual T L H,
          a (QuotientGroup.mk' _ k) =
            coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)) ∧
      IsElementaryAbelian 2 (moduleFrattiniImage D H) ∧
      commutatorAction₂ (moduleFrattiniImage D H) (CoreFrattiniSection T L H) = ⊥ ∧
      Nat.card (moduleFrattiniImage D H) ∣ 4 ∧
      (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ∣ 16 ∧
      (P.subgroupOf (enlargement T L H)).map (coreFrattiniAction T L H) ≤
        centralizer (moduleFrattiniImage D H : Set (MulAut (CoreFrattiniSection T L H))) ∧
      (moduleFrattiniImage D H = ⊥ ↔
        ⁅D.fullModule,(enlargedResidual T L H).pCoreIn 2⁆ ≤
          (frattini ((enlargedResidual T L H).pCoreIn 2)).map
            ((enlargedResidual T L H).pCoreIn 2).subtype) ∧
      (Nat.card (moduleFrattiniImage D H) = 4 →
        (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ≤
          Nat.card (moduleFrattiniImage D H) ^ 2) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  exact ⟨H,P,h,hs.toLocalInput,h.exists_faithful_coreFrattiniAction hn,
    h.moduleFrattiniImage_elementary hfull,h.moduleFrattiniImage_quadratic hfull,
    h.collapsed_moduleFrattiniImage_card_dvd f hn hs.toLocalInput hP hcollapse,
    h.collapsed_moduleFrattiniImage_fixed_index f hs.toLocalInput hP hcollapse,
    h.collapsed_cubic_centralizes_moduleFrattiniImage hfull hn hs.toLocalInput hcollapse,
    h.moduleFrattiniImage_eq_bot_iff hfull,
    h.collapsed_moduleFrattiniImage_four_bound f hs.toLocalInput hP hcollapse⟩

/-- Both requested source contracts retain the same quadratic action and its
exact nontriviality criterion. Excluding the remaining ambient configuration,
including the possible trivial or order-two image, stays with this owner. -/
theorem sourceContracts_or_quadraticFrattiniAction (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          IsElementaryAbelian 2 (moduleFrattiniImage D H) ∧
          commutatorAction₂ (moduleFrattiniImage D H) (CoreFrattiniSection T L H) = ⊥ ∧
          Nat.card (moduleFrattiniImage D H) ∣ 4 ∧
          (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ∣ 16 ∧
          (moduleFrattiniImage D H = ⊥ ↔
            ⁅D.fullModule,(enlargedResidual T L H).pCoreIn 2⁆ ≤
              (frattini ((enlargedResidual T L H).pCoreIn 2)).map
                ((enlargedResidual T L H).pCoreIn 2).subtype) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,h,_,_,hel,hq,hcard,hidx,_,hk,_⟩ := hc.exists_quadratic_frattini_action
    exact Or.inr ⟨L,D,hc,H,h,hel,hq,hcard,hidx,hk⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
