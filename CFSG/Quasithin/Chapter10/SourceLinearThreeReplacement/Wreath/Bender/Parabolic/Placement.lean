module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Hall
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.LinearThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Cartan
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Complete.Source
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.WreathTwoCoreQuotient

/-!
# The original H-star overlap and centralizer seed

The actual faithful odd Hall subgroup lies in L₀ and is a three-group.
Its nontriviality follows from the source Cartan construction and n(H)=2.
Since H centralizes the diagonal involution, that Hall subgroup and T lie
in C_{L₀T}(z). The latter has maximal Sylow subgroup T, forcing it into H.
Hall complementarity then identifies H∩M with that same diagonal parabolic.
Its existing quotient and residual calculation give the literal S₃-wreath
overlap, X≤H and X≠1, without an extra center-centralization premise.

Source: Aschbacher--Smith 10.2.3(ii), 10.2.4, and 10.3.3,
printed pp.745,747,756. Hall faithfulness remains the permitted premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender.Parabolic
open Chapter3.Section02 ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Overgroups.Closure Overgroups.Closure.Parabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- A genuine Hall actor supplied by E.2.2, with its original embedding.
Its nontriviality uses the survivor's generation parameter two; no
centralization of the full center of the Sylow group is assumed. -/
theorem exists_hall_actor (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hf : HallFaithful D H) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      IsMulCommutative B ∧
      (B.map H.subtype : Set G) * (T : Set G) =
        (T : Set G) * (B.map H.subtype : Set G) ∧
      IsPGroup 3 B ∧ B.map H.subtype ≤ localOrbit T L ∧
      ¬ B.map H.subtype ≤ (T : Subgroup G) := by
  have hlarge : 1 < ChapterE.generationParameter H := by rw [s.generation H hH]; decide
  obtain ⟨hP,f,_,hb,c,he,hperm,_⟩ :=
    source_hstar_cartan_data_of_generation_gt_one D hH hlarge
  have hBM : c.witness.abelianGroup ≤ D.maximalLocal.subgroupOf H := he ▸ c.hall_le
  have hHall : IsHallSubgroup oddPrimes
      (c.witness.abelianGroup.subgroupOf (D.maximalLocal.subgroupOf H)) := he ▸ c.hall
  have hfaith := hf _ hBM hHall c.witness.abelian hperm
  have h3 := MovingHall.linear_three_hall_isThreeGroup D (survivor_nonnormal s)
    hH hBM hHall hfaith s.quotient
  refine ⟨c.witness.abelianGroup,hBM,hHall,c.witness.abelian,hperm,h3,
    MovingHall.linear_three_hall_le_orbit D (survivor_nonnormal s) hBM c.witness.odd hfaith s.quotient,?_⟩
  intro hBT
  have h2 : IsPGroup 2 c.witness.abelianGroup :=
    (T.isPGroup'.to_le hBT).of_equiv
      (c.witness.abelianGroup.equivMapOfInjective H.subtype H.subtype_injective).symm
  have hbot : c.witness.abelianGroup = ⊥ := by
    simpa only [disjoint_self] using IsPGroup.disjoint_of_ne 2 3 (by decide)
      c.witness.abelianGroup c.witness.abelianGroup h2 h3
  have hcard := Nat.card_le_card_of_injective (inclusion c.witness.cyclic_le)
    (inclusion_injective c.witness.cyclic_le)
  rw [c.witness.card,hbot,Nat.card_unique] at hcard
  rw [s.generation H hH] at hb
  have hfour : 4 ≤ 2 ^ f := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) hb
  omega

/-- Hall and Sylow together generate the literal overlap. -/
theorem overlap_eq_hall_sup_sylow (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H))) :
    H ⊓ D.maximalLocal = B.map H.subtype ⊔ (T : Subgroup G) := by
  let M := D.maximalLocal.subgroupOf H
  let S := (T.subtype hTH).subtype
    (show (T : Subgroup G).subgroupOf H ≤ M from
      fun _ hx => le_normalizer_componentOrbit L T hx)
  have hg := (Subgroup.OddHall.sylow_complement_of_hall S hHall).sup_eq_top
  have hm := congrArg (map (H.subtype.comp M.subtype)) hg
  have hs : (S : Subgroup M).map (H.subtype.comp M.subtype) = (T : Subgroup G) := by
    rw [← map_map]
    change ((((T : Subgroup G).subgroupOf H).subgroupOf M).map M.subtype).map H.subtype = _
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G).subgroupOf H ≤ M from
      fun _ hx => le_normalizer_componentOrbit L T hx),map_subgroupOf_eq_of_le hTH]
  have hb : (B.subgroupOf M).map (H.subtype.comp M.subtype) = B.map H.subtype := by
    rw [← map_map,map_subgroupOf_eq_of_le hBM]
  have ht : (⊤ : Subgroup M).map (H.subtype.comp M.subtype) = H ⊓ D.maximalLocal := by
    rw [← map_map, ← MonoidHom.range_eq_map,range_subtype,subgroupOf_map_subtype,inf_comm]
  rw [Subgroup.map_sup,hs,hb,ht] at hm
  simpa only [sup_comm] using hm.symm


/-- The original diagonal parabolic lies in H, since its Sylow subgroup
is maximal and H contains a nontrivial odd actor in the parabolic. -/
theorem diagonalParabolic_le_hstar
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHC : H ≤ centralizer ({d.first*d.second} : Set G)) (hf : HallFaithful D H) :
    diagonalParabolic T L (d.first*d.second) ≤ H := by
  obtain ⟨B,_,_,_,_,_,hBR,hBT⟩ := exists_hall_actor D s hH hf
  obtain ⟨_,⟨ep⟩⟩ := Natural.diagonalRecognition T hmany L D s d
  obtain ⟨es⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let P := diagonalParabolic T L (d.first*d.second)
  have hTP : (T : Subgroup G) ≤ P := sylow_le_diagonalParabolic d.central
  have hmax := WreathTwoResidual.sylow_isCoatom_of_core_quotient (T.subtype hTP)
    (ep.trans (RegularWreathProduct.congr es.symm (MulEquiv.refl _)))
  have hBP : B.map H.subtype ≤ P :=
    le_inf (hBR.trans le_sup_left) ((map_subtype_le B).trans hHC)
  have hle : (T : Subgroup G).subgroupOf P ≤ H.subgroupOf P := fun _ hx => hH.1.1.2 hx
  rcases hmax.le_iff.mp hle with he | he
  · exact subgroupOf_eq_top.mp he
  · apply False.elim
    apply hBT
    intro b hb
    have hh : (⟨b,hBP hb⟩ : P) ∈ H.subgroupOf P := map_subtype_le B hb
    rw [he] at hh
    exact hh

/-- The overlap is the literal diagonal parabolic, not just an isomorphic group. -/
theorem overlap_eq_diagonalParabolic
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHC : H ≤ centralizer ({d.first*d.second} : Set G)) (hf : HallFaithful D H) :
    H ⊓ D.maximalLocal = diagonalParabolic T L (d.first*d.second) := by
  obtain ⟨B,hBM,hHall,_,_,_,hBR,_⟩ := exists_hall_actor D s hH hf
  apply le_antisymm
  · apply le_inf ?_ (inf_le_left.trans hHC)
    rw [overlap_eq_hall_sup_sylow D hH.1.1.2 B hBM hHall]
    exact sup_le (hBR.trans le_sup_left) le_sup_right
  · exact le_inf (diagonalParabolic_le_hstar hmany D s d hH hHC hf)
      ((diagonalParabolic_le_join _).trans
        (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)))

/-- The literal seed lies in H and is nontrivial. -/
theorem seed_placement
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHC : H ≤ centralizer ({d.first*d.second} : Set G)) (hf : HallFaithful D H) :
    centralizerSeed T L (d.first*d.second) ≤ H ∧
      centralizerSeed T L (d.first*d.second) ≠ ⊥ := by
  refine ⟨?_,?_⟩
  · exact (le_sup_left.trans (seed_join_eq_diagonalParabolic d.central).le).trans
      (diagonalParabolic_le_hstar hmany D s d hH hHC hf)
  · obtain ⟨r⟩ := Overgroups.Closure.Parabolic.parabolicSeed T hmany L D s d
    exact r.residual ▸ r.xi.ne_bot

/-- The two-core quotient of the actual maximal overlap is S₃ wr C₂. -/
theorem maximal_twoCore_quotient
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHC : H ≤ centralizer ({d.first*d.second} : Set G)) (hf : HallFaithful D H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    Nonempty ((minimalParabolicMax (T.subtype hH.1.1.2) hP ⧸
      pCore 2 (minimalParabolicMax (T.subtype hH.1.1.2) hP)) ≃*
        WreathTwoResidual.Actor) := by
  rw [source_hstar_parabolicMax_eq_overlap D hH]
  obtain ⟨_,⟨e⟩⟩ := Natural.diagonalRecognition T hmany L D s d
  have he : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  let a : D.maximalLocal.subgroupOf H ≃* diagonalParabolic T L (d.first*d.second) :=
    ((MulEquiv.subgroupCongr he.symm).trans
      (subgroupOfEquivOfLe (show H ⊓ D.maximalLocal ≤ H from inf_le_left))).trans
      (MulEquiv.subgroupCongr (overlap_eq_diagonalParabolic hmany D s d hH hHC hf))
  obtain ⟨es⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (e.trans (RegularWreathProduct.congr es.symm (MulEquiv.refl _)))⟩

/-- Prime support on the original maximal subgroup, used to exclude PSU₃(4). -/
theorem maximal_isSixGroup
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHC : H ≤ centralizer ({d.first*d.second} : Set G)) (hf : HallFaithful D H)
    (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    IsPGroup 6 (minimalParabolicMax (T.subtype hH.1.1.2) hP) := by
  rw [source_hstar_parabolicMax_eq_overlap D hH]
  have hp := CentralHall.LinearThree.source_proper_overgroup_six D s.quotient
    (survivor_nonnormal s) (diagonalParabolic T L (d.first*d.second))
    (sylow_le_diagonalParabolic d.central) (diagonalParabolic_lt_join d)
  have hh : IsPGroup 6 (H ⊓ D.maximalLocal : Subgroup G) :=
    (overlap_eq_diagonalParabolic hmany D s d hH hHC hf).symm ▸ hp
  have he : (H ⊓ D.maximalLocal).subgroupOf H = D.maximalLocal.subgroupOf H := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  exact he ▸ hh.comap_subtype

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender.Parabolic
