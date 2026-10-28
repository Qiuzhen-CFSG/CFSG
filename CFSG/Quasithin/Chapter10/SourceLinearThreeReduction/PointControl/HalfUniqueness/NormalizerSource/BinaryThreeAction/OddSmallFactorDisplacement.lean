module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallFaithfulSpanAction

/-!
# Displacement of the original natural summand

The first summand is the original [V,L], of order eight. In the surviving
branch its actual Frattini image has order two. The original kernel theorem
identifies its intersection with O₂(K), of order four. Mutual normalization
then places its actual displacement in the image of that intersection.
Source: Aschbacher--Smith 10.2.4--5, printed pp.747--748.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H P : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The image of the original first natural summand on the same Frattini section. -/
def firstModuleFrattiniImage (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (H : Subgroup G) :
    Subgroup (MulAut (CoreFrattiniSection T L H)) :=
  ((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf (enlargement T L H)).map (coreFrattiniAction T L H)

/-- In the nontrivial branch the original first summand has image of order two. -/
theorem Data.firstModuleFrattiniImage_card (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Nat.card (firstModuleFrattiniImage D H) = 2 := by
  have hsq := h.moduleFrattiniImage_card_square f hi hP
  have hfour := (h.collapsed_moduleFrattiniImage_bot_or_four f hn hi hP hc).resolve_left hne
  change Nat.card (moduleFrattiniImage D H) = Nat.card (firstModuleFrattiniImage D H)^2 at hsq
  rw [hfour] at hsq
  nlinarith

/-- The original first summand meets the containing core in exactly four elements. -/
theorem Data.firstModule_core_card (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Nat.card ((⁅D.fullModule,L⁆ : Subgroup G) ⊓ (enlargedResidual T L H).pCoreIn 2 : Subgroup G) = 4 := by
  let E := enlargement T L H
  let V := (⁅D.fullModule,L⁆ : Subgroup G)
  let Q := (enlargedResidual T L H).pCoreIn 2
  let a := coreFrattiniAction T L H
  let U := V.subgroupOf E ⊓ a.ker
  have hVE : V ≤ E := (selected_moved_le s).trans (h.fullModule_le_enlargement s.full_eq_local)
  have hcard : Nat.card (V.subgroupOf E) = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVE).toEquiv).trans (moved_card s hz)
  have hindex : U.relIndex (V.subgroupOf E) = 2 := by
    rw [inf_relIndex_left,relIndex_ker]
    exact h.firstModuleFrattiniImage_card f hn hi hP hc hne
  have hUcard : Nat.card U = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup E) U (V.subgroupOf E) bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,hindex,hcard] at hh
    omega
  obtain ⟨hVQ,hker⟩ := h.collapsed_nontrivial_module_kernel f hn hi hP hc hne
  have he : U.map E.subtype = V ⊓ Q := by
    ext v
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨hu.1,?_⟩
      have hh := (hker u (selected_moved_le s hu.1)).mp hu.2
      exact (hVQ.ge hh).2
    · intro hv
      exact ⟨⟨v,hVE hv.1⟩,⟨hv.1,h.core_le_frattiniAction_kernel hn hv.2⟩,rfl⟩
  rw [←he,card_map_of_injective E.subtype_injective]
  exact hUcard

private theorem Data.core_normalizes_firstModule (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    (enlargedResidual T L H).pCoreIn 2 ≤ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro q hq
  have hqT := (h.enlargedResidual_core_le_intersection hq).1.1
  have hqL := (h.enlargedResidual_core_le_intersection hq).1.2
  have hqV : q ∈ normalizer (D.fullModule : Set G) := by
    rw [hfull]
    exact D.join_normalizes_module (mem_sup_right hqT)
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp hqV,
    mem_normalizer_iff_map_conj_eq.mp hqL]

/-- Actual displacement by the original first summand lies in its own core image. -/
theorem Data.firstModuleFrattiniImage_displacement (h : Data D H)
    (hfull : D.fullModule = D.moduleSubgroup) :
    commutatorAction (firstModuleFrattiniImage D H) (CoreFrattiniSection T L H) ≤
      ((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf ((enlargedResidual T L H).pCoreIn 2)).map
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
  change (q:G)⁻¹ * ((v:G)*(q:G)*(v:G)⁻¹) ∈ (⁅D.fullModule,L⁆ : Subgroup G)
  have hh := le_normalizer_iff_commutator_le_right.mp (h.core_normalizes_firstModule hfull)
    (commutator_mem_commutator (Q.inv_mem q.property)
      (show (v:G) ∈ (⁅D.fullModule,L⁆ : Subgroup G) from hv))
  simpa only [commutatorElement_def,inv_inv,mul_assoc,coe_subtype] using hh

/-- The same actual first-summand displacement has cardinality at most four. -/
theorem Data.firstModuleFrattiniImage_displacement_card (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    Nat.card (commutatorAction (firstModuleFrattiniImage D H) (CoreFrattiniSection T L H)) ≤ 4 := by
  have hbound := card_le_of_le (h.firstModuleFrattiniImage_displacement s.full_eq_local)
  have hmap := ((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf
    ((enlargedResidual T L H).pCoreIn 2)).card_map_dvd (QuotientGroup.mk' (frattini _))
  have hcard : Nat.card ((⁅D.fullModule,L⁆ : Subgroup G).subgroupOf
      ((enlargedResidual T L H).pCoreIn 2)) = 4 := by
    rw [←inf_subgroupOf_right]
    rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact h.firstModule_core_card f hn hi hP hc hne
  exact hbound.trans (Nat.le_of_dvd (by rw [hcard]; decide) hmap |>.trans_eq hcard)

/-- On the actual invariant span, each actor from the original first summand
still has displacement of cardinality at most four, hence binary rank at most two. -/
theorem Data.firstModule_coreSpan_displacement_card (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥)
    (a : moduleFrattiniImage D H)
    (ha : (a : MulAut (CoreFrattiniSection T L H)) ∈ firstModuleFrattiniImage D H) :
    Nat.card (commutatorAction (zpowers (h.coreSpanModuleAction s.full_eq_local hn a))
      (h.moduleCoreSpan hn)) ≤ 4 := by
  let M := h.moduleCoreSpan hn
  let α := h.coreSpanModuleAction s.full_eq_local hn
  let C := commutatorAction (firstModuleFrattiniImage D H) (CoreFrattiniSection T L H)
  have hle : commutatorAction (zpowers (α a)) M ≤ C.comap M.subtype := by
    rw [commutatorAction_eq_closure,closure_le]
    rintro _ ⟨z,w,rfl⟩
    obtain ⟨n,hn'⟩ := z.property
    have hz : (z : MulAut M) = α (a^n) := by rw [map_zpow]; exact hn'.symm
    change (w : CoreFrattiniSection T L H)⁻¹ *
      ((z : MulAut M) w : CoreFrattiniSection T L H) ∈ C
    rw [hz,h.coreSpanModuleAction_apply]
    have ha' : ((a^n : moduleFrattiniImage D H) : MulAut (CoreFrattiniSection T L H)) ∈
        firstModuleFrattiniImage D H := (firstModuleFrattiniImage D H).zpow_mem ha n
    dsimp only [C]
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨⟨(a^n : moduleFrattiniImage D H),ha'⟩,
      (w : CoreFrattiniSection T L H),rfl⟩
  have hh := card_le_of_le (map_le_iff_le_comap.mpr hle)
  rw [card_map_of_injective M.subtype_injective] at hh
  exact hh.trans (h.firstModuleFrattiniImage_displacement_card f hn hi hP hc hne)

/-- The order-two image of the actual first summand supplies a nonidentity
original actor with the inherited displacement bound on the actual span. -/
theorem Data.exists_firstModule_small_actor (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (hne : moduleFrattiniImage D H ≠ ⊥) :
    ∃ a : moduleFrattiniImage D H, a ≠ 1 ∧
      (a : MulAut (CoreFrattiniSection T L H)) ∈ firstModuleFrattiniImage D H ∧
      Nat.card (commutatorAction (zpowers (h.coreSpanModuleAction s.full_eq_local hn a))
        (h.moduleCoreSpan hn)) ≤ 4 := by
  have htwo := h.firstModuleFrattiniImage_card f hn hi hP hc hne
  have hnb : firstModuleFrattiniImage D H ≠ ⊥ := by
    intro hh
    rw [hh,card_bot] at htwo
    norm_num at htwo
  obtain ⟨a,ha,hane⟩ := (firstModuleFrattiniImage D H).bot_or_exists_ne_one.resolve_left hnb
  have hle : firstModuleFrattiniImage D H ≤ moduleFrattiniImage D H :=
    map_mono (subgroupOf_mono _ (selected_moved_le s))
  let a' : moduleFrattiniImage D H := ⟨a,hle ha⟩
  exact ⟨a',fun hh => hane (congrArg Subtype.val hh),ha,
    h.firstModule_coreSpan_displacement_card f hn hi hP hc hne a' ha⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
