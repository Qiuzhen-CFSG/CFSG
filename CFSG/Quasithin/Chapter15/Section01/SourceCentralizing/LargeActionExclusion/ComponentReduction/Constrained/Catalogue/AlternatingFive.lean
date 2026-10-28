module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.NormalizerAction
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Alternatives
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFivePlaneCentralizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneNormalization
/-!
# The A₅ Borel in the original constrained catalogue

For every K in the fixed local family L(G₁,S), the original central-involution
seed lies in O₂(⟨K,S⟩). If K is an A₅ block, its Sylow normalizer centralizes
the seed. The singleton maximal-local condition puts this centralizer inside
M_Z ∩ K, and the proper-overgroup theorem for the actual A₅ quotient identifies
both subgroups with the literal Sylow normalizer.

Together with the original FF-module Thompson movement, this supplies every
clause of the A₅ rank-one alternative. It applies before exchanged selection,
including at prime five, and later on both exchanged-plane sizes. The natural
L₂-even blocks retain their separate module type and Borel obligation. The
remaining catalogue and quotient assembly stay with their existing owners.

Source: Aschbacher--Smith 15.1.20(2a), printed pp.1094--1095; C.1.13(c),
printed pp.124--125, for the A₅ block centralizer calculation.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The A₅ row on every eligible original local-family member, with both
its centralizer and Borel identified inside the fixed ambient group. -/
theorem localFamily_alternatingFive_borel (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hb : IsAlternatingBlock K 5) :
    d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
      d.MZ ⊓ K = (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype := by
  let H := K ⊔ d.S
  let K0 := K.subgroupOf H
  let Z := (centralInvolutions T).subgroupOf H
  let J := (d.MZ.subgroupOf H).subgroupOf K0
  let e : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  have hb0 := RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hb
  have hB : IsBlock K0 := ⟨inferInstance,hb0.2.1,hK.2.1.subnormal⟩
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  let P0 : Sylow 2 K0 := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hZS : centralInvolutions T ≤ d.S := le_inf (centralInvolutions_le_sylow T)
    ((centralInvolutions_le_centralizer_sylow T).trans
      (centralizer_le (d.marked_le_sylow h hTM)))
  have hZQ : Z ≤ pCore 2 H := le_normalClosure.trans
    (d.localFamily_catalogueModule_reduced_general h hTM hK hq hb.2.1.fitting).le_pCore
  have hZP : Z ≤ centralizer ((P0 : Subgroup K0).map K0.subtype : Set H) := by
    rintro z hz x ⟨y,⟨a,ha,rfl⟩,rfl⟩
    exact Subtype.ext (centralInvolutions_le_centralizer_sylow T hz a
      (d.S_le_T ((hP ▸ mem_map_of_mem K.subtype ha).1)))
  have hJ : J ≠ ⊤ := by
    intro he
    apply hout
    intro k hk
    exact (he.ge (show (⟨⟨k,mem_sup_left hk⟩,hk⟩ : K0) ∈ ⊤ from mem_top _))
  have hCJ : (centralizer (Z : Set H)).comap K0.subtype ≤ J := by
    intro k hk
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    exact ⟨hK.1 k.property,hMc.2 (by
      intro z hz
      exact congrArg Subtype.val (hk ⟨z,mem_sup_right (hZS hz)⟩ hz))⟩
  obtain ⟨hc,hborel,_⟩ := hb0.centralizer_borel_of_sylow_fixed K0 hB P0 Z hZQ hZP J hJ hCJ
  have heP : (P0 : Subgroup K0).map e.toMonoidHom = (d.S ⊓ K).subgroupOf K := by
    have hep : (P0 : Subgroup K0).map e.toMonoidHom = (P : Subgroup K) := by
      change ((P : Subgroup K).map e.symm.toMonoidHom).map e.toMonoidHom = _
      rw [map_map]
      have hei : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K := by ext x; simp
      rw [hei,map_id]
    apply map_injective K.subtype_injective
    rw [hep,hP,map_subgroupOf_eq_of_le inf_le_right]
  constructor
  · ext x
    constructor
    · intro hx
      have hxJ : (⟨⟨x,mem_sup_left hx.2⟩,hx.2⟩ : K0) ∈ J := hx.1
      have hxc := hc.symm ▸ hxJ
      refine ⟨hx.2,?_⟩
      intro z hz
      exact congrArg Subtype.val (hxc ⟨z,mem_sup_right (hZS hz)⟩ hz)
    · intro hx
      have hxc : (⟨⟨x,mem_sup_left hx.1⟩,hx.1⟩ : K0) ∈
          (centralizer (Z : Set H)).comap K0.subtype := by
        intro z hz
        exact Subtype.ext (hx.2 z hz)
      have hxJ : (⟨⟨x,mem_sup_left hx.1⟩,hx.1⟩ : K0) ∈ J := hc ▸ hxc
      exact ⟨hxJ,hx.1⟩
  · have hm := congrArg (fun A : Subgroup K0 => (A.map e.toMonoidHom).map K.subtype) hborel
    have hjm : (J.map e.toMonoidHom).map K.subtype = d.MZ ⊓ K := by
      ext x
      constructor
      · rintro ⟨_,⟨y,hy,rfl⟩,rfl⟩; exact ⟨hy,y.property⟩
      · intro hx; exact ⟨⟨x,hx.2⟩,⟨⟨⟨x,mem_sup_left hx.2⟩,hx.2⟩,hx.1,rfl⟩,rfl⟩
    have hn : (normalizer (P0 : Set K0)).map e.toMonoidHom =
        normalizer (((P0 : Subgroup K0).map e.toMonoidHom) : Set K) :=
      map_equiv_normalizer_eq (P0 : Subgroup K0) e
    rw [hjm,hn] at hm
    simpa only [heP] using hm

/-- The A₅ branch supplies the complete rank-one contract, including the
literal Borel and the original Thompson commutator. -/
private theorem alternatingFive_rankOne (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hl : d.L ∈ Chapter1.L G d.S)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hb : IsAlternatingBlock d.L 5) : d.ConstrainedRankOneAlternative := by
  have hk : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,hl⟩
  exact ⟨Or.inr hb,
    (d.localFamily_alternatingFive_borel h hM.1.2 hu hk hq d.L_not_le_MZ hb).2,
    (d.localFamily_normalizerAction hG hempty hM hJ hu h hk hq
      d.L_not_le_MZ hb.2.1.fitting).movement.symm⟩

/-- Original 15.1.20(2a) for the A₅ block, before exchanged selection.
Its Borel identification is proved from the central-involution seed. -/
theorem PreExclusionSource.constrained_rankOne_of_alternatingFive
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hb : IsAlternatingBlock d.L 5) : d.ConstrainedRankOneAlternative :=
  d.alternatingFive_rankOne hG hempty hM hJ hu h s.local_component s.quasisimple hb

/-- The later exchanged application retains both source plane sizes. -/
theorem ExchangedSource.constrained_rankOne_of_alternatingFive
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hb : IsAlternatingBlock d.L 5) : d.ConstrainedRankOneAlternative :=
  d.alternatingFive_rankOne hG hempty hM hJ hu h s.local_component s.quasisimple hb

/-- The A₅ block in the full-Sylow branch now carries all of its source
rank-one clauses. Only the natural L₂-even block still needs Borel recognition. -/
theorem PreExclusionSource.constrained_rankOne_or_l2_or_star
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedRankOneAlternative ∨ (∃ n : ℕ, IsL2EvenBlock d.L n) ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_star_catalogue_or_rankOne (h := h) hG hf with (hl | ha) | hs
  · exact Or.inr (Or.inl hl)
  · exact Or.inl (s.constrained_rankOne_of_alternatingFive (h := h) hG hempty hM hJ hu ha)
  · exact Or.inr (Or.inr hs)

/-- The same strengthened catalogue reduction after exchanged selection,
with the literal Q₁-normalizer and core-to-star comparison unchanged. -/
theorem ExchangedSource.constrained_rankOne_or_l2_or_star
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedRankOneAlternative ∨ (∃ n : ℕ, IsL2EvenBlock d.L n) ∨
      ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
        StarModels.Model (starImage d.L d.Q1 d.L) ∧
          (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
          (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
            Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) := by
  rcases s.constrained_star_catalogue_or_rankOne hG h hf with (hl | ha) | hs
  · exact Or.inr (Or.inl hl)
  · exact Or.inl (s.constrained_rankOne_of_alternatingFive hG hempty hM hJ hu h ha)
  · exact Or.inr (Or.inr hs)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
