module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortPlane
public import Theory.SpecificGroups.Triality.EndpointFusion
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.UnitRepresentatives
public import Theory.SpecificGroups.ReeF4.SourceCompletion.ShortCentralizerGeometry.Extremality

/-!
# Ambient involution fusion and short-root extremality

Connected native fixed graphs transport conjugacies through the literal two
endpoint maps. The returning-central-class separation and native two-root
classification then prove that the original right endpoint preserves and
reflects all ambient involution fusion. Sylow conjugation extends this
comparison to the two original endpoints. The full native short-centralizer
comparison transfers local extremality to the original ambient group.

The same marked central and short involutions represent exactly the two
ambient involution classes, including when Mc has a cubic supplement.
These discharge F.4.35 and F.4.40 on the original data; the full ambient
short-centralizer containment in F.4.42, matching sixth-power equations,
ambient generation/recognition and original Borel contradiction remain open.
The earlier marked-realization premise is retained without alteration.

Source: Aschbacher--Smith F.4.30,35,40, printed pp.290,292,294,
and 14.2.18--19,14.3.15, printed pp.987,994. The literal component application
is TerminalSolvable/EightBorelExtremality.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open Theory.GroupTheory
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.EvenInvolutionGeometry
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

omit [Finite G] in
private theorem inverse_endpoints_compatible (r : MarkedTriality T M Mc H)
    (z : Carrier P) (hl : z ∈ parabolic P .arms) (hr : z ∈ parabolic P .central) :
    (r.left.symm ⟨z,hl⟩ : G) = (r.right.symm ⟨z,hr⟩ : G) := by
  let b : borel P := ⟨z,(parabolic_inf_binary P rfl) ▸ ⟨hl,hr⟩⟩
  have h₀ := r.symm.left_commutes b
  have h₁ := r.symm.right_commutes b
  exact (congrArg Subtype.val h₀).trans (congrArg Subtype.val h₁).symm

omit [Finite G] in
theorem marked_native_second_fusion (r : MarkedTriality T M Mc H)
    (x y : secondParabolic T M Mc H) (hx : orderOf (x : G) = 2)
    (hxy : IsConj (r.right x).val (r.right y).val) : IsConj (x : G) (y : G) := by
  have hm : orderOf (r.right x).val = 2 := by
    rw [Subgroup.orderOf_coe,r.right.orderOf_eq,←Subgroup.orderOf_coe,hx]
  have h := EndpointFusion.endpoint_fusion 1 Nat.zero_lt_one
    (H.subtype.comp r.left.symm.toMonoidHom)
    ((secondParabolic T M Mc H).subtype.comp r.right.symm.toMonoidHom)
    (inverse_endpoints_compatible r) (i := true) (j := true) (r.right x) (r.right y) hm hxy
  change IsConj (r.right.symm (r.right x) : G) (r.right.symm (r.right y) : G) at h
  simpa only [r.right.symm_apply_apply] using h

omit [Finite G] in
private theorem long_roots_conjugate {x y : Carrier P}
    (hx : IsLongRootInvolution 1 Nat.zero_lt_one x)
    (hy : IsLongRootInvolution 1 Nat.zero_lt_one y) : IsConj x y := by
  obtain ⟨a,ha,hax⟩ := hx
  obtain ⟨b,hb,hby⟩ := hy
  exact hax.symm.trans (((longRoot_conjugate_one 1 Nat.zero_lt_one a ha).symm.trans
    (longRoot_conjugate_one 1 Nat.zero_lt_one b hb)).trans hby)

omit [Finite G] in
private theorem short_roots_conjugate {x y : Carrier P}
    (hx : IsShortRootInvolution 1 Nat.zero_lt_one x)
    (hy : IsShortRootInvolution 1 Nat.zero_lt_one y) : IsConj x y := by
  obtain ⟨a,ha,hax⟩ := hx
  obtain ⟨b,hb,hby⟩ := hy
  exact hax.symm.trans (((shortRoot_conjugate_one 1 Nat.zero_lt_one a ha).symm.trans
    (shortRoot_conjugate_one 1 Nat.zero_lt_one b hb)).trans hby)

omit [Finite G] in
/-- The selected short involution lies in the original first core, with
both endpoint coordinates still equal to the pinned short root. -/
theorem markedShortRoot_core (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) :
    ∃ q : H.pCoreIn 2, (q : G) = (markedShortRoot r a : G) ∧
      (firstCoreEquiv r q).val = RadicalCoordinates.LeviCommutators.short P rfl 2 a := by
  let q := (firstCoreEquiv r).symm ⟨_,ArmsOrbit.short_two_mem a⟩
  have hq : (firstCoreEquiv r q).val = RadicalCoordinates.LeviCommutators.short P rfl 2 a :=
    congrArg Subtype.val ((firstCoreEquiv r).apply_symm_apply _)
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at h
    rwa [map_subgroupOf_eq_of_le hTH] at h
  have hTP : (T : Subgroup G) ≤ secondParabolic T M Mc H := le_sup_right.trans le_sup_left
  refine ⟨q,?_,hq⟩
  have he : r.right (⟨q,hTP (hQT q.property)⟩ : secondParabolic T M Mc H) =
      r.right (markedShortRoot r a) := by
    apply Subtype.ext
    rw [←marked_endpoint_value r ⟨pCoreIn_le 2 H q.property,hTP (hQT q.property)⟩,
      ←firstCoreEquiv_val r q,hq,markedShortRoot_image]
  exact congrArg Subtype.val (r.right.injective he)

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

/-- The right endpoint preserves and reflects all ambient involution fusion. -/
theorem source_second_fusion_iff (r : MarkedTriality T M Mc H)
    (x y : secondParabolic T M Mc H) (hx : orderOf (x : G) = 2)
    (hy : orderOf (y : G) = 2) :
    IsConj (x : G) (y : G) ↔ IsConj (r.right x).val (r.right y).val := by
  refine ⟨?_,marked_native_second_fusion r x y hx⟩
  intro hxy
  have hTP : (T : Subgroup G) ≤ secondParabolic T M Mc H := le_sup_right.trans le_sup_left
  obtain ⟨z,hzne,hz⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hz1 : (z : G) ≠ 1 := by
    intro he
    exact hzne (Subtype.ext he)
  let zP : secondParabolic T M Mc H := ⟨z,hTP (centralInvolutions_le_sylow T z.property)⟩
  have hzlong := source_second_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r
    zP z.property hz1 (IsConj.refl _)
  have hxl : IsLongRootInvolution 1 Nat.zero_lt_one (r.right x).val →
      IsLongRootInvolution 1 Nat.zero_lt_one (r.right y).val := by
    intro h
    have hzx := marked_native_second_fusion r x zP hx (long_roots_conjugate h hzlong)
    exact source_second_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r
      y z.property hz1 (hzx.symm.trans hxy)
  have hyl : IsLongRootInvolution 1 Nat.zero_lt_one (r.right y).val →
      IsLongRootInvolution 1 Nat.zero_lt_one (r.right x).val := by
    intro h
    have hzy := marked_native_second_fusion r y zP hy (long_roots_conjugate h hzlong)
    exact source_second_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r
      x z.property hz1 (hzy.symm.trans hxy.symm)
  by_cases hlx : IsLongRootInvolution 1 Nat.zero_lt_one (r.right x).val
  · exact long_roots_conjugate hlx (hxl hlx)
  · have hm (v : secondParabolic T M Mc H) (hv : orderOf (v : G) = 2) :
        orderOf (r.right v).val = 2 := by
      rw [Subgroup.orderOf_coe,r.right.orderOf_eq,←Subgroup.orderOf_coe,hv]
    have hsx := (involution_isLongRoot_or_isShortRoot 1 Nat.zero_lt_one _ (hm x hx)).resolve_left hlx
    have hsy := (involution_isLongRoot_or_isShortRoot 1 Nat.zero_lt_one _ (hm y hy)).resolve_left
      (fun h => hlx (hyl h))
    exact short_roots_conjugate hsx hsy

/-- F.4.40: the literal original Sylow intersection is Sylow in the full
ambient short-root centralizer. -/
theorem source_short_ambient_sylow (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    let t := (markedShortRoot r a : G)
    ∃ S : Sylow 2 (centralizer ({t} : Set G)),
      (S : Subgroup (centralizer ({t} : Set G))) =
        (T : Subgroup G).subgroupOf (centralizer ({t} : Set G)) := by
  let L := secondParabolic T M Mc H
  let f : L →* Carrier P := (parabolic P .central).subtype.comp r.right.toMonoidHom
  have hf : Function.Injective f := (parabolic P .central).subtype_injective.comp r.right.injective
  apply ReeF4.SourceCompletion.ShortCentralizerGeometry.sylow_centralizer_of_endpoint_fusion
    T L (le_sup_right.trans le_sup_left) f hf (markedShortRoot r a)
    (markedShortRoot_mem_sylow r hH.1.1.2 a) (markedShortRoot_order r a ha)
    (fun x y hx hy hxy => (source_second_fusion_iff hG hempty hM hu hmany hcard e hH r x y hx hy).mp hxy)
    ?_ (marked_short_local_sylow r hH.1.1.2 a ha)
  rw [show f (markedShortRoot r a) = RadicalCoordinates.LeviCommutators.short P rfl 2 a from
    markedShortRoot_image r a]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (markedShortCentralizerEquiv r a ha ⟨x,hx⟩).property
  · intro y hy
    obtain ⟨x,hx⟩ := (markedShortCentralizerEquiv r a ha).surjective ⟨y,hy⟩
    exact ⟨x.val,x.property,congrArg Subtype.val hx⟩

/-- Fusion between the two literal original endpoints is exactly native fusion. -/
theorem source_first_second_fusion_iff (r : MarkedTriality T M Mc H)
    (x : H) (y : secondParabolic T M Mc H) (hx : orderOf (x : G) = 2)
    (hy : orderOf (y : G) = 2) :
    IsConj (x : G) (y : G) ↔ IsConj (r.left x).val (r.right y).val := by
  have hp : IsPGroup 2 (zpowers (x : G)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨a,ha,hat⟩ := UniqueFixedCoset.p_element_conjugate_into_sylow T hH.1.1.2 x.property hp
  have hTP : (T : Subgroup G) ≤ secondParabolic T M Mc H := le_sup_right.trans le_sup_left
  let w : secondParabolic T M Mc H := ⟨a*(x:G)*a⁻¹,hTP hat⟩
  let wH : H := ⟨w,hH.1.1.2 hat⟩
  have hxw : IsConj (x : G) (w : G) := isConj_iff.mpr ⟨a,rfl⟩
  have hw2 : orderOf (w : G) = 2 := ((MulAut.conj a).orderOf_eq x).trans hx
  have hm : IsConj (r.left x).val (r.right w).val := by
    rw [←marked_endpoint_value r ⟨wH.property,w.property⟩]
    exact (((parabolic P .arms).subtype.comp r.left.toMonoidHom).map_isConj
      (isConj_iff.mpr ⟨(⟨a,ha⟩ : H),rfl⟩ : IsConj x wH))
  constructor
  · intro hxy
    exact hm.trans ((source_second_fusion_iff hG hempty hM hu hmany hcard e hH r w y hw2 hy).mp
      (hxw.symm.trans hxy))
  · intro hxy
    exact hxw.trans ((source_second_fusion_iff hG hempty hM hu hmany hcard e hH r w y hw2 hy).mpr
      (hm.symm.trans hxy))

omit [Finite G] hG hempty hM hu hmany hcard e hH in
private theorem marked_short_isShort (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    IsShortRootInvolution 1 Nat.zero_lt_one (r.right (markedShortRoot r a)).val := by
  rw [markedShortRoot_image]
  refine ⟨fieldFrobenius P a,fun hh => ha ((fieldFrobenius P).injective
    (hh.trans (map_zero _).symm)),?_⟩
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨ConcreteBruhat.weylRepresentative P rfl (.r 5),?_⟩
  exact (ArmsNormalization.rotation_short_two P rfl a).trans
    (foldedShort_zero_eq_shortRoot 1 Nat.zero_lt_one _)

/-- Every original ambient involution belongs to one of the two classes
represented on the same marked Sylow. -/
theorem source_involution_classes (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1)
    (x : G) (hx : orderOf x = 2) :
    IsConj z x ∨ IsConj (markedShortRoot r a : G) x := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hx,pow_one])
  obtain ⟨b,_,hb⟩ := UniqueFixedCoset.p_element_conjugate_into_sylow T
    (show (T : Subgroup G) ≤ ⊤ from le_top) (mem_top x) hp
  have hTP : (T : Subgroup G) ≤ secondParabolic T M Mc H := le_sup_right.trans le_sup_left
  let y : secondParabolic T M Mc H := ⟨b*x*b⁻¹,hTP hb⟩
  have hy2 : orderOf (y : G) = 2 := ((MulAut.conj b).orderOf_eq x).trans hx
  have hym : orderOf (r.right y).val = 2 := by
    rw [Subgroup.orderOf_coe,r.right.orderOf_eq,←Subgroup.orderOf_coe,hy2]
  have hxy : IsConj x (y : G) := isConj_iff.mpr ⟨b,rfl⟩
  rcases involution_isLongRoot_or_isShortRoot 1 Nat.zero_lt_one _ hym with hl | hs
  · let zP : secondParabolic T M Mc H := ⟨z,hTP (centralInvolutions_le_sylow T hz)⟩
    have hzl := source_second_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r
      zP hz hz1 (IsConj.refl _)
    exact Or.inl ((marked_native_second_fusion r y zP hy2
      (long_roots_conjugate hl hzl)).symm.trans hxy.symm)
  · exact Or.inr ((marked_native_second_fusion r y (markedShortRoot r a) hy2
      (short_roots_conjugate hs (marked_short_isShort r a ha))).symm.trans hxy.symm)

/-- The two represented ambient involution classes are distinct, including
the original cubic partner case. -/
theorem source_short_not_conj_center (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    ¬ IsConj z (markedShortRoot r a : G) := by
  intro hc
  obtain ⟨q,hq,hqm⟩ := markedShortRoot_core r hH.1.1.2 a
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have he : MulAut.conj g z = (q : G) := hg.trans hq.symm
  obtain ⟨b,hb⟩ := source_core_fusion_fixed hG hempty hM hu hmany hcard e hH r
    g hz hz1 (he.symm ▸ q.property)
  apply source_short_not_fixed hG hempty hM hu hmany hcard e hH r q a ha hqm b
  simpa only [he] using hb

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
