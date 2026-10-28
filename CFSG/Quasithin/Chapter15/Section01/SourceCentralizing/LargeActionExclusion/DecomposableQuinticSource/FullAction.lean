module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.Core
public import Theory.GroupAction.ComplementaryFourWreathEmbedding
public import Theory.GroupTheory.WreathTwoThreeCore

/-!
# The full partner acts on the original pair of Thompson planes

When the partner local module is E, source ordering makes its actual action
permute the original two Thompson four-groups. This assertion uses the
literal partner equality, with no residual-fifteen premise.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem threeCore_divisor_of_wreath_embedding
    {D : Type*} [Group D] [Finite D]
    (φ : D →* WreathTwoResidual.Actor) (hφ : Function.Injective φ) :
    IsElementaryAbelian 3 (pCore 3 D) ∧ Nat.card (pCore 3 D) ∣ 9 ∧
      IsPGroup 2 (D ⧸ pCore 3 D) := by
  let C := pCore 3 WreathTwoResidual.Actor
  let q := QuotientGroup.mk' C
  let f := q.comp φ
  have htwo : IsPGroup 2 (WreathTwoResidual.Actor ⧸ C) :=
    WreathTwoResidual.threeCore_quotient_two
  have hle (S : Subgroup D) (hS : IsPGroup 3 S) : S ≤ C.comap φ := by
    have hd : Disjoint (S.map f) (⊤ : Subgroup (WreathTwoResidual.Actor ⧸ C)) :=
      IsPGroup.disjoint_of_coprime (hS.map f) (htwo.to_subgroup ⊤) (by decide)
    have hz : S.map f=⊥ := by simpa using hd
    have hk := (map_eq_bot_iff S).mp hz
    simpa only [f,←MonoidHom.comap_ker,q,QuotientGroup.ker_mk'] using hk
  have hcore : pCore 3 D=C.comap φ := by
    apply le_antisymm (hle _ pCore_isPGroup)
    exact le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective φ hφ⟩
  let : IsElementaryAbelian 3 C := WreathTwoResidual.threeCore_elementary
  have he : IsElementaryAbelian 3 (pCore 3 D) := by
    rw [hcore]
    exact IsElementaryAbelian.comap_of_injective φ hφ C
  refine ⟨he,?_,?_⟩
  · rw [hcore,←WreathTwoResidual.threeCore_card]
    exact C.card_comap_dvd_of_injective φ hφ
  · have hk : pCore 3 D=f.ker := by
      rw [hcore,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact ((htwo.to_subgroup f.range).of_equiv
      (QuotientGroup.quotientKerEquivRange f).symm).of_equiv
        (QuotientGroup.quotientMulEquivOfEq hk).symm

/-- Source ordering makes the whole partner permute the actual Thompson planes. -/
theorem PreparedChosenModule.decomposable_five_full_partner_plane_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (_hfull : V = localModule T M) :
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
      localModule T Mc = thompsonFixed T V →
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let E := thompsonFixed T V
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      ∃ _hn : Mc ≤ normalizer (E : Set G),
        ∀ m ∈ Mc,
          (Z₁.map (MulAut.conj m).toMonoidHom = Z₁ ∧
            Z₂.map (MulAut.conj m).toMonoidHom = Z₂) ∨
          (Z₁.map (MulAut.conj m).toMonoidHom = Z₂ ∧
            Z₂.map (MulAut.conj m).toMonoidHom = Z₁) := by
  let := h.elementary
  intro U c d _hd s π _hp hs _hdec _hq _hfive hUcEq Z₁ E Z₂
  have hMcE : Mc ≤ normalizer (E : Set G) := by
    rw [show E = localModule T Mc from hUcEq.symm]
    exact le_normalizer_conjugateSpanBy _ _
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  refine ⟨hMcE,?_⟩
  intro m hm
  obtain ⟨a,ha,b,hb,rfl⟩ :=
    source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc hMc m hm
  have hbE : b ∈ centralizer (E : Set G) := by
    rw [show E = localModule T Mc from hUcEq.symm]
    exact hb.2
  have heq (Z : Subgroup G) (hZE : Z ≤ E) :
      Z.map (MulAut.conj (a*b)).toMonoidHom = Z.map (MulAut.conj a).toMonoidHom := by
    apply le_antisymm
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨z,hz,?_⟩
      have hc : b*z*b⁻¹=z := by rw [←hbE z (hZE hz),mul_inv_cancel_right]
      change a*z*a⁻¹=(a*b)*z*(a*b)⁻¹
      rw [mul_inv_rev]
      calc
        _ = a*(b*z*b⁻¹)*a⁻¹ := by rw [hc]
        _ = _ := by group
    · rintro _ ⟨z,hz,rfl⟩
      refine ⟨z,hz,?_⟩
      have hc : b*z*b⁻¹=z := by rw [←hbE z (hZE hz),mul_inv_cancel_right]
      change (a*b)*z*(a*b)⁻¹=a*z*a⁻¹
      rw [mul_inv_rev]
      calc
        _ = a*(b*z*b⁻¹)*a⁻¹ := by group
        _ = _ := by rw [hc]
  rw [heq Z₁ inf_le_right,heq Z₂ inf_le_right]
  let α : internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict ⟨a,ha.2⟩
  have hamap : E.map (MulAut.conj a).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp (hMcE ha.1)
  have hmap (i:d.Index) :
      (thompsonPlane T V (c.ambientFactor d i).space).map (MulAut.conj a).toMonoidHom =
      thompsonPlane T V (c.ambientFactor d (π α i)).space := by
    change ((plane _ _)⊓E).map _=(plane _ _)⊓E
    rw [map_inf _ _ _ (MulAut.conj a).injective,
      hamap,
      plane_conjugate h.normalized _ ⟨a,ha.2⟩]
    exact congrArg (fun P=>plane V P⊓E) (hs α i)
  have hpermi : (π α s.first=s.first ∧ π α s.second=s.second) ∨
      (π α s.first=s.second ∧ π α s.second=s.first) := by
    rcases s.covers (π α s.first) with hi|hi
    · left
      refine ⟨hi,?_⟩
      rcases s.covers (π α s.second) with hj|hj
      · exact (s.distinct ((π α).injective (hi.trans hj.symm))).elim
      · exact hj
    · right
      refine ⟨hi,?_⟩
      rcases s.covers (π α s.second) with hj|hj
      · exact hj
      · exact (s.distinct ((π α).injective (hi.trans hj.symm))).elim
  rcases hpermi with hh|hh
  · exact Or.inl ⟨(hmap s.first).trans (by rw [hh.1]),
      (hmap s.second).trans (by rw [hh.2])⟩
  · exact Or.inr ⟨(hmap s.first).trans (by rw [hh.1]),
      (hmap s.second).trans (by rw [hh.2])⟩

/-- The full partner has an elementary three-core of order dividing nine,
with a two-group quotient. The remaining cubic alternative is explicit. -/
theorem PreparedChosenModule.decomposable_five_full_partner_three_core
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
      localModule T Mc = thompsonFixed T V →
      let E := thompsonFixed T V
      ∃ hn : Mc ≤ normalizer (E : Set G),
        IsElementaryAbelian 3 (pCore 3 (internalActionImage Mc E hn)) ∧
        Nat.card (pCore 3 (internalActionImage Mc E hn)) ∣ 9 ∧
        IsPGroup 2 ((internalActionImage Mc E hn) ⧸
          pCore 3 (internalActionImage Mc E hn)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hUcEq E
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  obtain ⟨hn,hperm⟩ := h.decomposable_five_full_partner_plane_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hUcEq
  let D := internalActionImage Mc E hn
  let f : Mc →* D := (actionHom Mc E hn).rangeRestrict
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  let P := Z₁.subgroupOf E
  let Q := Z₂.subgroupOf E
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  have hZ₁E : Z₁ ≤ E := inf_le_right
  have hZ₂E : Z₂ ≤ E := inf_le_right
  have hPQ : IsCompl P Q := by
    constructor
    · apply disjoint_def.mpr
      intro x hx hy
      apply Subtype.ext
      exact mem_bot.mp (s.thompson_disjoint ▸ (show (x:G)∈Z₁⊓Z₂ from ⟨hx,hy⟩))
    · apply codisjoint_iff.mpr
      apply map_injective E.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hZ₁E,map_subgroupOf_eq_of_le hZ₂E,
        ←MonoidHom.range_eq_map,range_subtype]
      exact s.thompson_split.symm
  have hPc : Nat.card P=4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZ₁E).toEquiv).trans (s.thompson_card s.first)
  have hQc : Nat.card Q=4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZ₂E).toEquiv).trans (s.thompson_card s.second)
  have hfaith : fixingSubgroup D (Set.univ : Set E)=⊥ := by
    apply bot_unique
    intro g hg
    apply mem_bot.mpr
    apply Subtype.ext
    ext e
    exact congrArg Subtype.val ((mem_fixingSubgroup_iff D).mp hg e (Set.mem_univ e))
  have hact : ∀g:D,
      (P.map (MulDistribMulAction.toMulAut D E g).toMonoidHom=P ∧
        Q.map (MulDistribMulAction.toMulAut D E g).toMonoidHom=Q) ∨
      (P.map (MulDistribMulAction.toMulAut D E g).toMonoidHom=Q ∧
        Q.map (MulDistribMulAction.toMulAut D E g).toMonoidHom=P) := by
    intro g
    obtain ⟨m,rfl⟩ := (actionHom Mc E hn).rangeRestrict_surjective g
    have hm (X Y:Subgroup G) (hXE:X≤E) (hYE:Y≤E)
        (hXY:X.map (MulAut.conj (m:G)).toMonoidHom=Y) :
        (X.subgroupOf E).map (MulDistribMulAction.toMulAut D E (f m)).toMonoidHom=
          Y.subgroupOf E := by
      apply map_injective E.subtype_injective
      rw [map_map,map_subgroupOf_eq_of_le hYE]
      change (X.subgroupOf E).map
        ((MulAut.conj (m:G)).toMonoidHom.comp E.subtype)=Y
      rw [←map_map,map_subgroupOf_eq_of_le hXE,hXY]
    rcases hperm m m.property with hh|hh
    · exact Or.inl ⟨hm Z₁ Z₁ hZ₁E hZ₁E hh.1,hm Z₂ Z₂ hZ₂E hZ₂E hh.2⟩
    · exact Or.inr ⟨hm Z₁ Z₂ hZ₁E hZ₂E hh.1,hm Z₂ Z₁ hZ₂E hZ₁E hh.2⟩
  obtain ⟨φ,hφ⟩ := ComplementaryFourWreathAction.exists_injective_wreath_of_complementary_four
    P Q hPQ hPc hQc hfaith hact
  exact ⟨hn,threeCore_divisor_of_wreath_embedding φ hφ⟩


end CFSG.Quasithin.Chapter15.Section01
