module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallSplitAction

/-!
# Detecting the containing action and locating the original module kernel

Retain the literal source groups E=<N_G(T₁),H>, K=<O²(H)^E>,
Q=O₂(K), and V=D.fullModule. The already proved K-normal closure of
Q∩O₂(L₀T) is Q. Transport through the same Frattini quotient shows that
the K-translates of its image generate Q/Φ(Q). Since V fixes that image,
an element of the V-action commuting with the whole containing-quotient
action fixes every translate and is the identity. Thus the two action
subgroups have trivial intersection with the indicated centralizer.

When the full module image is nontrivial, its proved order is four.
The original V has order sixty-four, while [V,P] has order sixteen and
lies in Q. Counting the kernel of this same action gives
V∩Q=[V,P], and identifies every original module element acting trivially.
Consequently the inner module image equals the full action image exactly
when V≤K; equivalently, its order is four exactly under that containment.
This makes the remaining quotient placement explicit without inferring it
from the earlier index bound or replacing V by its Frattini image.

Both actual source contracts have applications below. The trivial-image
case and exclusion of the remaining collapsed configuration are still
unproved. Their discharge and final assembly remain with
qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the sole external
premise, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P I : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The original common-kernel image generates the entire Frattini section
under the actual containing-component action. -/
theorem Data.collapsed_commonFrattiniImage_span (h : Data D H) (f : LiftData s hz)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (⨆ k : enlargedResidual T L H, (commonFrattiniImage T L H).map
      (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)).toMonoidHom) = ⊤ := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let N := Q ⊓ (localJoin T L).pCoreIn 2
  let π := QuotientGroup.mk' (frattini Q)
  let a : K →* MulAut Q := Q.normalizerMonoidHom.comp
    (inclusion (h.enlargedResidual_le_enlargement.trans (enlargement_normalizes_core T L H)))
  have hspan : (⨆ k : K, (N.subgroupOf Q).map (a k).toMonoidHom) = ⊤ := by
    apply map_injective Q.subtype_injective
    rw [Subgroup.map_iSup, ←MonoidHom.range_eq_map, range_subtype]
    have he (k : K) : ((N.subgroupOf Q).map (a k).toMonoidHom).map Q.subtype =
        N.map (MulAut.conj (k:G)).toMonoidHom := by
      rw [map_map]
      change (N.subgroupOf Q).map ((MulAut.conj (k:G)).toMonoidHom.comp Q.subtype) = _
      rw [←map_map,map_subgroupOf_eq_of_le inf_le_left]
    simp_rw [he]
    rw [←conjugateSpanBy_eq_iSup_conj]
    exact h.collapsed_kernel_normalClosure f hs hK hp ho hm hlarge hP hc
  have hmspan := congrArg (Subgroup.map π) hspan
  rw [Subgroup.map_iSup,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at hmspan
  have he (k : K) : ((N.subgroupOf Q).map (a k).toMonoidHom).map π =
      (commonFrattiniImage T L H).map
        (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)).toMonoidHom := by
    rw [map_map]
    change (N.subgroupOf Q).map (π.comp (a k).toMonoidHom) =
      ((N.subgroupOf Q).map π).map _
    rw [map_map]
    congr 1
    exact MonoidHom.ext (fun q => (coreFrattiniAction_mk (inclusion h.enlargedResidual_le_enlargement k) q).symm)
  simpa only [he] using hmspan

/-- No nonidentity original module image commutes with the entire faithful
containing-quotient action. This also applies to every subgroup of that image. -/
theorem Data.collapsed_moduleFrattiniImage_disjoint_centralizer (h : Data D H)
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    Disjoint (moduleFrattiniImage D H)
      (centralizer ((h.coreQuotientFrattiniAction hn).range : Set _)) := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro a ⟨ha,hac⟩
  obtain ⟨v,hv,rfl⟩ := ha
  apply mem_bot.mpr
  apply MulEquiv.ext
  intro w
  let F := (coreFrattiniAction T L H v).toMonoidHom.eqLocus (MonoidHom.id _)
  have hle : (⨆ k : enlargedResidual T L H, (commonFrattiniImage T L H).map
      (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)).toMonoidHom) ≤ F := by
    apply iSup_le
    intro k
    rintro _ ⟨u,hu,rfl⟩
    have he := hac _ (show coreFrattiniAction T L H
        (inclusion h.enlargedResidual_le_enlargement k) ∈
          (h.coreQuotientFrattiniAction hn).range from ⟨QuotientGroup.mk' _ k,rfl⟩)
    have hh := congrArg (fun b : MulAut (CoreFrattiniSection T L H) => b u) he
    change coreFrattiniAction T L H v
        (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) u) =
      coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) u
    change coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k)
        (coreFrattiniAction T L H v u) =
      coreFrattiniAction T L H v
        (coreFrattiniAction T L H (inclusion h.enlargedResidual_le_enlargement k) u) at hh
    rw [←hh,h.fullModule_fixes_commonFrattiniImage s.full_eq_local v hv u hu]
  rw [h.collapsed_commonFrattiniImage_span f hs hK hp ho hm hlarge hP hc] at hle
  exact hle (mem_top w)


/-- A surviving module action has exactly the original cubic moved subgroup
as its kernel on V. In particular V∩O₂(K) has order sixteen, not an
unspecified large intersection. -/
theorem Data.collapsed_nontrivial_module_kernel (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 = ⁅D.fullModule,P⁆ ∧
      ∀ v : enlargement T L H, (v:G) ∈ D.fullModule →
        (coreFrattiniAction T L H v = 1 ↔ (v:G) ∈ ⁅D.fullModule,P⁆) := by
  let E := enlargement T L H
  let a := coreFrattiniAction T L H
  let V := D.fullModule.subgroupOf E
  let U := V ⊓ a.ker
  let W := (⁅D.fullModule,P⁆ : Subgroup G).subgroupOf E
  have hVE := h.fullModule_le_enlargement s.full_eq_local
  obtain ⟨hWcard,hWle,_⟩ := h.collapsed_cubic_module f hi hP hc
  have hWE := hWle.trans (inf_le_left.trans hVE)
  have hVU : Nat.card V = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVE).toEquiv).trans s.full_card
  have hfour := (h.collapsed_nontrivial_moduleFrattiniImage f hn hi hP hc hne).1
  have hidx : U.relIndex V = 4 := by
    rw [inf_relIndex_left,relIndex_ker]
    exact hfour
  have hUcard : Nat.card U = 16 := by
    have he := relIndex_mul_relIndex (⊥ : Subgroup E) U V bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hidx,hVU] at he
    omega
  have hWU : W ≤ U := le_inf (subgroupOf_mono E (hWle.trans inf_le_left))
    ((subgroupOf_mono E (hWle.trans inf_le_right)).trans (h.core_le_frattiniAction_kernel hn))
  have hWeq : W = U := eq_of_le_of_card_ge hWU (by
    rw [hUcard,Nat.card_congr (subgroupOfEquivOfLe hWE).toEquiv,hWcard])
  have hker (v : E) (hv : (v:G) ∈ D.fullModule) :
      a v = 1 ↔ (v:G) ∈ ⁅D.fullModule,P⁆ := by
    constructor
    · intro he
      exact hWeq.ge ⟨hv,he⟩
    · intro hvW
      exact (hWeq.le hvW).2
  refine ⟨le_antisymm ?_ hWle,hker⟩
  intro v hv
  let v' : E := ⟨v,hVE hv.1⟩
  exact (hker v' hv.1).mp (h.core_le_frattiniAction_kernel hn hv.2)

/-- The kernel comparison gives the exact cardinality in the same ambient group. -/
theorem Data.collapsed_nontrivial_module_core_card (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Nat.card (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 : Subgroup G) = 16 := by
  rw [(h.collapsed_nontrivial_module_kernel f hn hi hP hc hne).1]
  exact (h.collapsed_cubic_module f hi hP hc).1

/-- In the surviving branch, equality with the inner actor requires the
literal full-module containment in K. Equality of faithful action images
cannot silently supply this placement. -/
theorem Data.collapsed_inner_image_eq_iff (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    h.innerModuleFrattiniImage hn = moduleFrattiniImage D H ↔
      D.fullModule ≤ enlargedResidual T L H := by
  constructor
  · intro he
    let E := enlargement T L H
    let a := coreFrattiniAction T L H
    have hVE := h.fullModule_le_enlargement s.full_eq_local
    have hk := (h.collapsed_nontrivial_module_kernel f hn hi hP hc hne).2
    intro v hv
    let v' : E := ⟨v,hVE hv⟩
    have hm : a v' ∈ h.innerModuleFrattiniImage hn :=
      he.symm ▸ mem_map_of_mem a hv
    rw [innerModuleFrattiniImage,innerModuleQuotient,h.quotientImage_frattini_map hn] at hm
    obtain ⟨u,hu,heuv⟩ := hm
    have hwV : ((u⁻¹*v':E):G) ∈ D.fullModule :=
      D.fullModule.mul_mem (D.fullModule.inv_mem hu.1) hv
    have hwker : a (u⁻¹*v') = 1 := by rw [map_mul,map_inv,heuv,inv_mul_cancel]
    have hwK : ((u⁻¹*v':E):G) ∈ enlargedResidual T L H :=
      (pCoreIn_le 2 _)
        ((h.collapsed_cubic_module f hi hP hc).2.1 ((hk (u⁻¹*v') hwV).mp hwker)).2
    have hh := (enlargedResidual T L H).mul_mem hu.2 hwK
    change (u:G)*((u:G)⁻¹*v) ∈ enlargedResidual T L H at hh
    simpa only [mul_inv_cancel_left] using hh
  · exact h.innerModuleFrattiniImage_eq_of_le hn

/-- A four-element inner image is equivalent to full placement, once the
original full action is nontrivial. -/
theorem Data.collapsed_inner_quotient_four_iff (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Nat.card (innerModuleQuotient D H) = 4 ↔ D.fullModule ≤ enlargedResidual T L H := by
  have hecard : Nat.card (h.innerModuleFrattiniImage hn) = Nat.card (innerModuleQuotient D H) :=
    card_map_of_injective (h.coreQuotientFrattiniAction_injective hn)
  have hfour := (h.collapsed_nontrivial_moduleFrattiniImage f hn hi hP hc hne).1
  rw [←h.collapsed_inner_image_eq_iff f hn hi hP hc hne]
  constructor
  · intro hh
    exact eq_of_le_of_card_ge (h.innerModuleFrattiniImage_le hn) (by rw [hecard,hh,hfour])
  · intro hh
    rw [←hecard,hh,hfour]

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics


namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Subgroup Theory.GroupTheory
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual source witness has a module action that detects the containing
quotient. A surviving image has its exact kernel on the original V; the
trivial image is retained with its genuine intersection consequence. -/
theorem SourceCubicNormalizerEnlargement.exists_detected_module_action
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, ∃ h : Data D H,
      ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      Disjoint (moduleFrattiniImage D H)
        (centralizer ((h.coreQuotientFrattiniAction hn).range : Set _)) ∧
      ((moduleFrattiniImage D H = ⊥ ∧
          D.fullModule ⊓ enlargedResidual T L H ≤ (enlargedResidual T L H).pCoreIn 2) ∨
        (Nat.card (moduleFrattiniImage D H) = 4 ∧
          (FixedPoints.subgroup (moduleFrattiniImage D H) (CoreFrattiniSection T L H)).index ≤
            Nat.card (moduleFrattiniImage D H) ^ 2 ∧
          D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 = ⁅D.fullModule,P⁆ ∧
          Nat.card (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 : Subgroup G) = 16 ∧
          (∀ v : enlargement T L H, (v:G) ∈ D.fullModule →
            (coreFrattiniAction T L H v = 1 ↔ (v:G) ∈ ⁅D.fullModule,P⁆)) ∧
          (Nat.card (innerModuleQuotient D H) = 4 ↔ D.fullModule ≤ enlargedResidual T L H))) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have hlarge : 11 ≤ p := by have := Nat.mod_le p 24; omega
  refine ⟨H,P,h,hn,hs.toLocalInput,
    h.collapsed_moduleFrattiniImage_disjoint_centralizer f hn hs hK hp ho hm hlarge hP hcollapse,?_⟩
  by_cases hz : moduleFrattiniImage D H = ⊥
  · refine Or.inl ⟨hz,(h.innerModuleFrattiniImage_eq_bot_iff hn).mp ?_⟩
    exact bot_unique ((h.innerModuleFrattiniImage_le hn).trans_eq hz)
  · obtain ⟨hfour,hbound⟩ := h.collapsed_nontrivial_moduleFrattiniImage f hn hs.toLocalInput hP hcollapse hz
    obtain ⟨hker,hv⟩ := h.collapsed_nontrivial_module_kernel f hn hs.toLocalInput hP hcollapse hz
    exact Or.inr ⟨hfour,hbound,hker,
      h.collapsed_nontrivial_module_core_card f hn hs.toLocalInput hP hcollapse hz,hv,
      h.collapsed_inner_quotient_four_iff f hn hs.toLocalInput hP hcollapse hz⟩

/-- Both literal source contracts retain the same original obstruction, with
no centralizing nonidentity actor and an exact surviving kernel. The final
collapsed-case exclusion remains the half-Sylow owner's obligation. -/
theorem sourceContracts_or_detectedModuleAction (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H P : Subgroup G, ∃ h : Data D H,
          ∃ hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G),
          Disjoint (moduleFrattiniImage D H)
            (centralizer ((h.coreQuotientFrattiniAction hn).range : Set _)) ∧
          ((moduleFrattiniImage D H = ⊥ ∧
              D.fullModule ⊓ enlargedResidual T L H ≤ (enlargedResidual T L H).pCoreIn 2) ∨
            (Nat.card (moduleFrattiniImage D H) = 4 ∧
              D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 = ⁅D.fullModule,P⁆ ∧
              Nat.card (D.fullModule ⊓ (enlargedResidual T L H).pCoreIn 2 : Subgroup G) = 16 ∧
              (Nat.card (innerModuleQuotient D H) = 4 ↔ D.fullModule ≤ enlargedResidual T L H))) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,P,h,hn,_,hdis,hcases⟩ := hc.exists_detected_module_action
    refine Or.inr ⟨L,D,hc,H,P,h,hn,hdis,?_⟩
    rcases hcases with hz | ⟨hfour,_,hker,hcard,_,hplace⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hfour,hker,hcard,hplace⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
