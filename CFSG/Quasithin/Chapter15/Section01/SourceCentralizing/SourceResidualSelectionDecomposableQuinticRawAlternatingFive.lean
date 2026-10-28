module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawThompson
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.AlternatingFiveAction.Thompson
public import Theory.GroupTheory.PResidual.CentralizingSupplement

/-!
# The original quintic component is not an exceptional alternating-five block

The literal two-residual of the Thompson normalizer in C_M(Z₁) has the
same moved subgroup as O²(C_M(Z₁)), by Thompson Frattini factorization.
It normalizes the actual component and J(S). The full alternating-five
block theorem would make this two-perfect residual centralize the
component, forcing its moved subgroup to centralize the component too.
This contradicts the original selected-component movement.

No prime-actor lift, generation of M by the marked centralizer, or
generation-dependent component record is used.

Source: Aschbacher--Smith 15.1.21(ii), printed p.1098.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The actual Thompson-normalizer residual retains the entire original
marked moving subgroup, without any marked generation hypothesis. -/
theorem PreparedChosenModule.raw_marked_thompson_residual_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G))) :
    let C := M ⊓ centralizer (Z1 : Set G)
    let N := C ⊓ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
    ⁅V,(pResidual 2 N).map N.subtype⁆ = ⁅V,(pResidual 2 C).map C.subtype⁆ := by
  let := h.elementary
  let H := M ⊓ centralizer (Z1 : Set G)
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have hVH : V ≤ H := le_inf h.le_selected
    (V.le_centralizer.trans (centralizer_le (hZ.trans inf_le_left)))
  have hHV : H ≤ normalizer (V : Set G) := inf_le_left.trans h.normalized
  let : (V.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHV
  obtain ⟨P,hP⟩ := hSyl.restrict
    (le_inf (inf_le_left.trans hM.1.2) inf_le_right) inf_le_right
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ hZ).1
  change elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
  have hmapJ : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJS]
  have hJP : elementaryAbelianMaxJ (P : Subgroup H) ≤
      centralizer (V.subgroupOf H : Set H) := by
    intro j hj v hv
    apply Subtype.ext
    exact (hJ (hmapJ ▸ mem_map_of_mem H.subtype hj)) v (h.le_local hv)
  let N := normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H)
  have hgen : N ⊔ centralizer (V.subgroupOf H : Set H) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n,hn,c,hc,rfl⟩ := ChapterB.thompson_normalizer_factorization
      (V.subgroupOf H) P hJP x
    exact mul_mem_sup hn hc
  have hN : N.map H.subtype =
      H ⊓ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ H := by
      rw [←hmapJ]
      exact map_subtype_le _
    have he : elementaryAbelianMaxJ (P : Subgroup H) =
        (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [hmapJ,map_subgroupOf_eq_of_le hJT]
    dsimp only [N]
    rw [he,←subgroupOf_normalizer_eq hJT,subgroupOf_map_subtype,inf_comm]
  have he := congrArg (map H.subtype)
    (commutator_embedded_pResidual_eq_of_centralizing_sup 2 (V.subgroupOf H) N hgen)
  simp only [map_commutator,map_subgroupOf_eq_of_le hVH,map_embedded_pResidual] at he
  rw [hN] at he
  exact he

/-- The same raw outside component cannot be an exceptional A₅ block.
The actor is the literal two-residual, with no prime-order lift. -/
theorem PreparedChosenModule.raw_component_not_alternating_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (houtMZ : ¬ L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬ L ≤ M)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hn : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      R ⊔ ⁅V,R⁆ ≤ normalizer (L : Set G))
    (hmove : let C := M ⊓ centralizer (Z1 : Set G); let R := (pResidual 2 C).map C.subtype
      ⁅L,⁅V,R⁆⁆ ≠ ⊥) : ¬ ChapterC.IsAlternatingBlock L 5 := by
  intro hb
  let := h.elementary
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let C := M ⊓ centralizer (Z1 : Set G)
  let N := C ⊓ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let R := (pResidual 2 C).map C.subtype
  let Y := (pResidual 2 N).map N.subtype
  let W := ⁅V,R⁆
  have hYperfect : IsPPerfect 2 Y := isPPerfect_embedded_pResidual 2 _
  have hYR : Y ≤ R := embedded_pResidual_mono 2 inf_le_left
  have hYL : Y ≤ normalizer (L : Set G) := hYR.trans (le_sup_left.trans hn)
  have hYJ : Y ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
    have he := (h.caseI_marked_thompson_control hG T hM hJ hZ).1
    change elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) at he
    rw [he]
    exact (map_subtype_le _).trans inf_le_right
  have hLY := (h.raw_component_thompson hG T hM hJ hu hZ hL hq hb.2.1.fitting
    houtMZ houtM).2.1
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hL.2
  have hc : Y ≤ centralizer (L : Set G) := hb.thompson_actor_centralizes L S Y
    (T.isPGroup'.to_le inf_le_left) P (hP ▸ inf_le_left) hLY hYperfect hYL hYJ
  have hWY : ⁅W,Y⁆ = W := by
    have he := h.raw_marked_thompson_residual_commutator hG T hM hJ hZ hSyl
    change ⁅V,Y⁆ = W at he
    rw [←he]
    exact commutator_isPPerfect_idempotent Y V hYperfect
      (IsElementaryAbelian.isPGroup 2 V)
      (hYR.trans (((map_subtype_le _).trans inf_le_left).trans h.normalized))
  have hWN : W ≤ normalizer (L : Set G) := le_sup_right.trans hn
  have hWC : ⁅Y,W⁆ ≤ centralizer (L : Set G) := by
    apply commutator_le.mpr
    intro y hy w hw
    exact commutator_mem_centralizer_of_normalizes L (hc hy) (hWN hw)
  rw [commutator_comm,hWY] at hWC
  apply hmove
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hWC

/-- The actual order-four-partner quintic source constructs the same raw
outside component with its exceptional A₅ block excluded. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_not_alternating_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 4 →
      let Z1 := thompsonPlane T V (c.ambientFactor d s.first).space
      let G1 := centralizer (Z1 : Set G)
      let S := (T : Subgroup G) ⊓ G1
      let C := M ⊓ G1
      let R := (pResidual 2 C).map C.subtype
      let W := ⁅V,R⁆
      ∃ L : Subgroup G, L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ G1 ⊓ Mc ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        ¬ ChapterC.IsAlternatingBlock L 5 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨L,hZ,_,_,_,_,hSyl,_,_,_,_,_,_,_,_,_,_,_,hLc,hout,hquasi,
      hloc,hSL,hLM,hn,hm,_⟩ := h.decomposable_five_partner_four_raw_component
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  exact ⟨L,hLc,hout,hquasi,hloc,hSL,hLM,hn,hm,
    h.raw_component_not_alternating_five hG T hM hJ hu hZ ⟨hLc.1,hloc⟩
      hquasi hout hLM hSyl hn hm⟩

end CFSG.Quasithin.Chapter15.Section01
