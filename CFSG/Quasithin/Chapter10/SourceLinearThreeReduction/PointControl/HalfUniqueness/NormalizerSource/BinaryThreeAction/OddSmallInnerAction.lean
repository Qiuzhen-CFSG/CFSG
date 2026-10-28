module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallQuadraticAction

/-!
# The original module intersection in the containing quotient

Retain E=<N_G(T₁),H>, K=<O²(H)^E>, Q=O₂(K), and the original
module V. The faithful K/Q action on Q/Φ(Q) is defined using the
original conjugation map. Mapping the actual subgroup (V∩K)Q/Q through
this action agrees with restricting the original V-action to V∩K.
Consequently this inner action is quadratic, has order dividing four,
and has fixed index dividing sixteen in the collapsed source case.
Its order is exactly [V∩K:V∩Q]. The actor centralizes the original cubic
image, lies in the original quotient Sylow, and is preserved by every
element of the original T, including its factor exchanger.

Faithfulness makes its triviality equivalent to V∩K≤Q. We do not infer
V≤K or identify this actor with the whole module image without that
containment. An actor of order four satisfies the index-square bound,
but no order-four or nontriviality assumption is discharged here.
The final applications retain both original source contracts and their
same ambient configuration. Its exclusion and final assembly remain
with qt-d-10-nona5-half-sylow-unique; ModuleChoiceAt is the only external
premise, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The faithful action of the literal containing quotient, with the original marking. -/
def Data.coreQuotientFrattiniAction (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    XiQuotient (enlargedResidual T L H) →* MulAut (CoreFrattiniSection T L H) :=
  QuotientGroup.lift (pCore 2 (enlargedResidual T L H))
    ((coreFrattiniAction T L H).comp (inclusion h.enlargedResidual_le_enlargement))
    (h.coreFrattiniAction_kernel hn).ge

theorem Data.coreQuotientFrattiniAction_injective (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Function.Injective (h.coreQuotientFrattiniAction hn) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (h.coreFrattiniAction_kernel hn).symm

theorem Data.coreQuotientFrattiniAction_mk (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (k : enlargedResidual T L H) :
    h.coreQuotientFrattiniAction hn (QuotientGroup.mk' _ k) =
      coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) := rfl

/-- The image of an arbitrary original subgroup through the two compatible maps. -/
theorem Data.quotientImage_frattini_map (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (A : Subgroup G) :
    (quotientImage (enlargedResidual T L H) A).map (h.coreQuotientFrattiniAction hn) =
      ((A ⊓ enlargedResidual T L H).subgroupOf (enlargement T L H)).map
        (coreFrattiniAction T L H) := by
  ext x
  constructor
  · rintro ⟨q,⟨k,hk,rfl⟩,rfl⟩
    exact ⟨inclusion h.enlargedResidual_le_enlargement k,⟨hk,k.property⟩,rfl⟩
  · rintro ⟨g,⟨hg,hgK⟩,rfl⟩
    exact ⟨QuotientGroup.mk' _ ⟨g,hgK⟩,mem_map_of_mem _ hg,rfl⟩

/-- The module intersection, as a subgroup of the actual containing quotient. -/
def innerModuleQuotient (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) : Subgroup (XiQuotient (enlargedResidual T L H)) :=
  quotientImage (enlargedResidual T L H) D.fullModule

/-- Its actual faithful image in the containing-core Frattini action. -/
def Data.innerModuleFrattiniImage (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Subgroup (MulAut (CoreFrattiniSection T L H)) :=
  (innerModuleQuotient D H).map (h.coreQuotientFrattiniAction hn)

theorem Data.innerModuleFrattiniImage_le (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    h.innerModuleFrattiniImage hn ≤ moduleFrattiniImage D H := by
  rw [innerModuleFrattiniImage,innerModuleQuotient,h.quotientImage_frattini_map hn]
  exact map_mono (subgroupOf_mono _ inf_le_left)

theorem Data.innerModuleFrattiniImage_eq_of_le (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hV : D.fullModule ≤ enlargedResidual T L H) :
    h.innerModuleFrattiniImage hn = moduleFrattiniImage D H := by
  rw [innerModuleFrattiniImage,innerModuleQuotient,h.quotientImage_frattini_map hn,
    inf_eq_left.mpr hV]
  rfl

theorem innerModuleQuotient_eq_bot_iff :
    innerModuleQuotient D H = ⊥ ↔
      D.fullModule ⊓ enlargedResidual T L H ≤ (enlargedResidual T L H).pCoreIn 2 := by
  rw [innerModuleQuotient,quotientImage,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
  constructor
  · intro hh v hv
    exact mem_map_of_mem (enlargedResidual T L H).subtype
      (hh (show (⟨v,hv.2⟩ : enlargedResidual T L H) ∈
        D.fullModule.subgroupOf (enlargedResidual T L H) from hv.1))
  · intro hh v hv
    obtain ⟨q,hq,he⟩ := hh ⟨hv,v.property⟩
    exact (Subtype.ext he : q=v) ▸ hq

theorem Data.innerModuleFrattiniImage_eq_bot_iff (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    h.innerModuleFrattiniImage hn = ⊥ ↔
      D.fullModule ⊓ enlargedResidual T L H ≤ (enlargedResidual T L H).pCoreIn 2 := by
  rw [innerModuleFrattiniImage,
    map_eq_bot_iff_of_injective _ (h.coreQuotientFrattiniAction_injective hn),
    innerModuleQuotient_eq_bot_iff]

theorem Data.innerModuleQuotient_elementary (_h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    IsElementaryAbelian 2 (innerModuleQuotient D H) := by
  let : IsElementaryAbelian 2 D.fullModule := hfull.symm ▸ D.module_elementary
  let : IsElementaryAbelian 2 (D.fullModule.subgroupOf (enlargedResidual T L H)) :=
    IsElementaryAbelian.comap_of_injective (enlargedResidual T L H).subtype
      (enlargedResidual T L H).subtype_injective D.fullModule
  exact IsElementaryAbelian.map _

private theorem quadratic_subgroup {W : Type*} [Group W]
    {A B : Subgroup (MulAut W)} (hle : A ≤ B)
    (hq : commutatorAction₂ B W = ⊥) : commutatorAction₂ A W = ⊥ := by
  have hm : commutatorAction A W ≤ commutatorAction B W := by
    rw [commutatorAction_eq_closure,closure_le]
    rintro _ ⟨a,w,rfl⟩
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨(⟨a,hle a.property⟩ : B),w,rfl⟩
  apply le_antisymm _ bot_le
  apply (closure_le (K := (⊥ : Subgroup W))).mpr
  rintro _ ⟨a,w,hw,rfl⟩
  have he := (commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hq)
    (hm hw) (⟨a,hle a.property⟩ : B)
  change (a : MulAut W) w = w at he
  change w⁻¹ * (a : MulAut W) w ∈ (⊥ : Subgroup W)
  rw [he,inv_mul_cancel]
  exact one_mem _

theorem Data.innerModuleFrattiniImage_quadratic (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : D.fullModule = D.moduleSubgroup) :
    commutatorAction₂ (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H) = ⊥ :=
  quadratic_subgroup (h.innerModuleFrattiniImage_le hn) (h.moduleFrattiniImage_quadratic hfull)

theorem Data.collapsed_innerModuleQuotient_card_dvd (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    Nat.card (innerModuleQuotient D H) ∣ 4 := by
  have hd := (card_dvd_of_le (h.innerModuleFrattiniImage_le hn)).trans
    (h.collapsed_moduleFrattiniImage_card_dvd f hn hi hP hc)
  rwa [innerModuleFrattiniImage,card_map_of_injective (h.coreQuotientFrattiniAction_injective hn)] at hd

theorem Data.collapsed_innerModuleFrattiniImage_fixed_index (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (FixedPoints.subgroup (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H)).index ∣ 16 := by
  have hfixed : FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H) ≤
      FixedPoints.subgroup (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H) := by
    intro w hw a
    exact hw ⟨a,h.innerModuleFrattiniImage_le hn a.property⟩
  exact (index_dvd_of_le hfixed).trans
    (h.collapsed_moduleFrattiniImage_fixed_index f hi hP hc)

/-- The quotient actor's order is measured on the literal module intersection. -/
theorem innerModuleQuotient_card :
    Nat.card (innerModuleQuotient D H) =
      ((enlargedResidual T L H).pCoreIn 2).relIndex
        (D.fullModule ⊓ enlargedResidual T L H) := by
  let K := enlargedResidual T L H
  have he : (K.pCoreIn 2).subgroupOf K = pCore 2 K :=
    comap_map_eq_self_of_injective K.subtype_injective _
  rw [innerModuleQuotient,quotientImage,←relIndex_ker,QuotientGroup.ker_mk',←he,
    ←inf_subgroupOf_right D.fullModule K,relIndex_subgroupOf inf_le_right]

theorem Data.collapsed_innerModuleQuotient_centralizes_cubic (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : D.fullModule = D.moduleSubgroup)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    innerModuleQuotient D H ≤
      centralizer (quotientImage (enlargedResidual T L H) P : Set _) := by
  let a := h.coreQuotientFrattiniAction hn
  have he := h.quotientImage_frattini_map hn P
  rw [inf_eq_left.mpr (hi.complement_le.trans h.residual_le_enlargedResidual)] at he
  have hcub := h.collapsed_cubic_centralizes_moduleFrattiniImage hfull hn hi hc
  intro v hv
  rw [mem_centralizer_iff]
  intro p hp
  apply h.coreQuotientFrattiniAction_injective hn
  rw [map_mul,map_mul]
  have hp' := he ▸ mem_map_of_mem a hp
  exact (hcub hp' (a v) (h.innerModuleFrattiniImage_le hn (mem_map_of_mem a hv))).symm

/-- Four surviving inner actors satisfy the same index-square bound, with the
order now measured in the actual containing quotient. -/
theorem Data.collapsed_innerModuleQuotient_four_bound (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hfour : Nat.card (innerModuleQuotient D H) = 4) :
    (FixedPoints.subgroup (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H)).index ≤
      Nat.card (innerModuleQuotient D H) ^ 2 := by
  rw [hfour]
  exact Nat.le_of_dvd (by decide)
    (h.collapsed_innerModuleFrattiniImage_fixed_index f hn hi hP hc)

/-- Every element of the original Sylow, hence the original exchanger,
preserves this literal quotient actor. -/
theorem Data.innerModuleQuotient_invariant (_h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : D.fullModule = D.moduleSubgroup) (t : (T : Subgroup G)) :
    (innerModuleQuotient D H).map
      (quotientAction T L H ⟨t,stabilizer_normalized D hn t.property⟩).toMonoidHom =
        innerModuleQuotient D H := by
  apply pCoreNormalizerAction_preserves_image
  rw [hfull]
  exact D.join_normalizes_module ((show (T : Subgroup G) ≤ localJoin T L from le_sup_right) t.property)

/-- The actor lies in the actual quotient Sylow, with the original T marking. -/
theorem Data.innerModuleQuotient_le_sylow (_h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    innerModuleQuotient D H ≤ quotientImage (enlargedResidual T L H) (T : Subgroup G) := by
  apply map_mono
  apply subgroupOf_mono
  rw [hfull]
  exact D.module_le_core.trans ((join_core_le_stabilizer D).trans inf_le_left)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual source witness carries an actor in K/O₂(K) and its faithful
quadratic action on Q/Φ(Q). The exact original intersection controls whether
that actor is trivial. -/
theorem SourceCubicNormalizerEnlargement.exists_inner_module_action
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      Function.Injective (h.coreQuotientFrattiniAction hn) ∧
      IsElementaryAbelian 2 (innerModuleQuotient D H) ∧
      commutatorAction₂ (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H) = ⊥ ∧
      Nat.card (innerModuleQuotient D H) ∣ 4 ∧
      (FixedPoints.subgroup (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H)).index ∣ 16 ∧
      innerModuleQuotient D H ≤
        centralizer (quotientImage (enlargedResidual T L H) P : Set _) ∧
      (∀ t : (T : Subgroup G), (innerModuleQuotient D H).map
        (quotientAction T L H ⟨t,stabilizer_normalized D hn t.property⟩).toMonoidHom =
          innerModuleQuotient D H) ∧
      (h.innerModuleFrattiniImage hn = ⊥ ↔
        D.fullModule ⊓ enlargedResidual T L H ≤ (enlargedResidual T L H).pCoreIn 2) ∧
      (Nat.card (innerModuleQuotient D H) = 4 →
        (FixedPoints.subgroup (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H)).index ≤
          Nat.card (innerModuleQuotient D H) ^ 2) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  exact ⟨H,P,h,hn,hs.toLocalInput,h.coreQuotientFrattiniAction_injective hn,
    h.innerModuleQuotient_elementary hfull,h.innerModuleFrattiniImage_quadratic hn hfull,
    h.collapsed_innerModuleQuotient_card_dvd f hn hs.toLocalInput hP hcollapse,
    h.collapsed_innerModuleFrattiniImage_fixed_index f hn hs.toLocalInput hP hcollapse,
    h.collapsed_innerModuleQuotient_centralizes_cubic hn hfull hs.toLocalInput hcollapse,
    h.innerModuleQuotient_invariant hn hfull,h.innerModuleFrattiniImage_eq_bot_iff hn,
    h.collapsed_innerModuleQuotient_four_bound f hn hs.toLocalInput hP hcollapse⟩

/-- Both original source contracts retain the same actual quotient actor,
without assuming that the full module lies in K or that its image survives. -/
theorem sourceContracts_or_innerModuleAction (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, ∃ h : Data D H,
          ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
          IsElementaryAbelian 2 (innerModuleQuotient D H) ∧
          commutatorAction₂ (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H) = ⊥ ∧
          Nat.card (innerModuleQuotient D H) ∣ 4 ∧
          (FixedPoints.subgroup (h.innerModuleFrattiniImage hn) (CoreFrattiniSection T L H)).index ∣ 16 ∧
          (h.innerModuleFrattiniImage hn = ⊥ ↔
            D.fullModule ⊓ enlargedResidual T L H ≤ (enlargedResidual T L H).pCoreIn 2) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,h,hn,_,_,hel,hq,hcard,hidx,_,_,hk,_⟩ := hc.exists_inner_module_action
    exact Or.inr ⟨L,D,hc,H,h,hn,hel,hq,hcard,hidx,hk⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
