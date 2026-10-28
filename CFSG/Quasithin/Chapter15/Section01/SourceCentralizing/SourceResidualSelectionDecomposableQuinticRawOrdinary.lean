module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawComponent
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115.Transport
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Original ordinary model actions on the actual quintic component

The raw outside component retains its literal Sylow subgroup and original
1.1.5 hypotheses. They classify every original central involution on that
same component when it is ordinary. Its center is its two-core, and the
original central seed acts faithfully on it. No whole-M
generation assertion or CaseIComponentData surrogate is introduced.

Source: Aschbacher--Smith 1.1.5 and 15.1.20(3), printed pp.1095--1097.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

private theorem raw_ordinary_center {H L : Subgroup G} (hLH : L ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hodd : pPrimeCore 2 H = ⊥) :
    center L = pCore 2 L ∧ IsPGroup 2 (center L) := by
  let e : L.subgroupOf H ≃* L := subgroupOfEquivOfLe hLH
  let := hL.2
  let := IsQuasisimple.of_mulEquiv e
  have hoddL : pPrimeCore 2 L = ⊥ := by
    have hh := pPrimeCore_map_iso 2 e
    rw [Subgroup.IsSubnormal.pPrimeCore_eq_bot hodd _ hL.1,Subgroup.map_bot] at hh
    exact hh.symm
  have he := IsQuasisimple.center_eq_pCore hoddL
  exact ⟨he,by rw [he]; exact pCore_isPGroup⟩

private theorem raw_ordinary_marked_actions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {H Mc L : Subgroup G} (hLH : L ≤ H) (hout : ¬L ≤ H ⊓ Mc)
    (P : Sylow 2 H)
    (h115 : ∀ z ∈ centralInvolutions T, z ≠ 1 → Chapter1.Lemma115Hypotheses H P Mc z)
    (hL : IsComponent H (L.subgroupOf H)) :
    centralInvolutions T ≤ normalizer (L : Set G) ∧
      centralInvolutions T ⊓ centralizer (L : Set G) = ⊥ ∧
      ∀ z ∈ centralInvolutions T, z ≠ 1 →
        ⁅L,zpowers z⁆ = L ∧ ∃ α : MulAut L,
          (∀ x : L, (α x : G) = z*x*z⁻¹) ∧ ModelAction115 L α := by
  have ha (z : G) (hz : z ∈ centralInvolutions T) (hne : z ≠ 1) :
      ⁅L,zpowers z⁆ = L ∧ HasModelAction115 (L.subgroupOf H) z := by
    have hh := Chapter1.lemma_1_1_5_three_knownSimple hG H P Mc z
      (h115 z hz hne) (L.subgroupOf H) hL
    rw [map_subgroupOf_eq_of_le hLH] at hh
    exact ⟨hh.1.symm,hh.2.2⟩
  have hn : centralInvolutions T ≤ normalizer (L : Set G) := by
    intro z hz
    by_cases he : z = 1
    · exact he ▸ (normalizer (L : Set G)).one_mem
    obtain ⟨α,hα,_⟩ := (ha z hz he).2
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      let x' : L.subgroupOf H := ⟨⟨x,hLH hx⟩,hx⟩
      change z*x*z⁻¹ ∈ L
      rw [←hα x']
      exact (α x').property
    · intro x hx
      let x' : L.subgroupOf H := ⟨⟨x,hLH hx⟩,hx⟩
      obtain ⟨y,hy⟩ := α.surjective x'
      refine ⟨y,y.property,?_⟩
      change z*(y : G)*z⁻¹ = x
      rw [←hα y,hy]
  refine ⟨hn,?_,?_⟩
  · apply bot_unique
    intro z hz
    by_contra he
    have hzne : z ≠ 1 := fun hh => he (mem_bot.mpr hh)
    have hc := commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hz.2)
    rw [commutator_comm,(ha z hz.1 hzne).1] at hc
    exact hout (hc ▸ bot_le)
  · intro z hz hzne
    obtain ⟨α,hα,hm⟩ := (ha z hz hzne).2
    let e : L ≃* L.subgroupOf H := (subgroupOfEquivOfLe hLH).symm
    exact ⟨(ha z hz hzne).1,MulAut.congr e.symm α,fun x => hα (e x),hm.of_mulEquiv e⟩

/-- The same actual quintic component has the complete original marked
ordinary actions whenever its component branch is ordinary. -/
theorem PreparedChosenModule.decomposable_five_partner_four_raw_ordinary_marking
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
      let R := (pResidual 2 (M ⊓ G1 : Subgroup G)).map (M ⊓ G1).subtype
      let W := ⁅V,R⁆
      ∃ L : Subgroup G,
        L ∈ Chapter1.cComponentsIn G1 ∧ ¬ L ≤ G1 ⊓ Mc ∧
        IsQuasisimple (L ⧸ pCore 2 L) ∧ L ∈ Chapter1.L G S ∧
        Chapter1.IsSylowIn 2 (S ⊓ L) L ∧ ¬ L ≤ M ∧
        R ⊔ W ≤ normalizer (L : Set G) ∧ ⁅L,W⁆ ≠ ⊥ ∧
        (IsComponent G1 (L.subgroupOf G1) →
          center L = pCore 2 L ∧ IsPGroup 2 (center L) ∧
          centralInvolutions T ≤ normalizer (L : Set G) ∧
          centralInvolutions T ⊓ centralizer (L : Set G) = ⊥ ∧
          ∀ z ∈ centralInvolutions T, z ≠ 1 →
            ⁅L,zpowers z⁆ = L ∧ ∃ α : MulAut L,
              (∀ x : L, (α x : G) = z*x*z⁻¹) ∧ ModelAction115 L α) ∧
        (IsComponent G1 (L.subgroupOf G1) ∨ generalizedFitting L = pCore 2 L) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨L,_,_,_,_,hodd,_,_,_,_,_,_,_,_,_,_,_,⟨P,_,h115⟩,
      hLc,hout,hqL,hloc,hSyl,houtM,hnL,hmove,hcases⟩ :=
    h.decomposable_five_partner_four_raw_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  refine ⟨L,hLc,hout,hqL,hloc,hSyl,houtM,hnL,hmove,?_,hcases⟩
  intro ho
  obtain ⟨hc,hc2⟩ := raw_ordinary_center hLc.1 ho hodd
  obtain ⟨hn,hfaith,ha⟩ := raw_ordinary_marked_actions hG T hLc.1 hout P h115 ho
  exact ⟨hc,hc2,hn,hfaith,ha⟩

end CFSG.Quasithin.Chapter15.Section01
