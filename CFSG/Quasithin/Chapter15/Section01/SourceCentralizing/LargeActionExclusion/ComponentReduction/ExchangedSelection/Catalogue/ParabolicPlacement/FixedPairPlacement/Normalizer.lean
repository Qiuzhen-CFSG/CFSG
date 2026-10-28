module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.ResidualRestriction
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalPair

/-!
# Same-pair placement in the literal normalizer parabolic

For H = P N_S(L), the source symmetric-three or wreath quotient makes H
minimal parabolic. Its two-residual is precisely the embedded O²(P).
Thus a moving A₃ block would express O²(P) as a product of actual A₃
blocks, contrary to the defining source condition.

When Baum(S) normalizes L, transport the one universal pair on Baum(T)
to the Sylow N_S(L) of H. Its first central seed grows and its second
member has the identical ambient image. The resulting centralizer or
normalizer alternative puts every P in M_L or M intersect L. No
normalization of L by the full S, or extra characteristic-subgroup
escape hypothesis, is imposed.

Source: Aschbacher--Smith 15.1.22(*), printed pp.1098--1099, using
C.1.19 and the fixed-pair solvable minimal-parabolic argument of C.1.26.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem minimal_of_small_core_quotient
    (R : Sylow 2 G)
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty ((G ⧸ pCore 2 G) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    IsMinimalParabolicOver R ⊤ := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    have hi := SymmetricThreeTwoCore.sylow_index_three e R
    have hmax : IsCoatom (R : Subgroup G) := by
      refine ⟨?_,?_⟩
      · intro h
        simp [h] at hi
      · intro U hU
        have hd : U.index ∣ 3 := (Subgroup.index_dvd_of_le hU.le).trans (dvd_of_eq hi)
        rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
        · exact Subgroup.index_eq_one.mp h
        · have hmul := Subgroup.relIndex_mul_index hU.le
          rw [hi,h] at hmul
          exact (hU.not_ge (Subgroup.relIndex_eq_one.mp (by omega))).elim
    apply isMinimalParabolicOver_of_sylow_isCoatom R hmax
    intro hn
    let := hn
    exact hmax.ne_top ((SymmetricThreeTwoCore.sylow_self_normalizing e R).symm.trans
      (normalizer_eq_top (H := (R : Subgroup G))))
  · obtain ⟨e⟩ := he
    obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    let ew := e.trans (RegularWreathProduct.congr eSL.symm
      (MulEquiv.refl (Multiplicative (ZMod 2))))
    exact isMinimalParabolicOver_of_sylow_isCoatom R
      (WreathTwoResidual.sylow_isCoatom_of_core_quotient R ew)
      (WreathTwoResidual.sylow_not_normal_of_core_quotient R ew)


theorem IsSourceParabolic.normalizer_sylow
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hL : d.L ∈ Chapter1.L G d.S) :
    Chapter1.IsSylowIn 2 d.sylowNormalizer (P ⊔ d.sylowNormalizer) :=
  (Chapter1.Section02.Adequate.local_normalizer_isSylow hL).restrict le_sup_right
    (sup_le (hP.le_component.trans le_sup_left) le_sup_right)

theorem IsSourceParabolic.normalizer_structure
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (R : Sylow 2 (P ⊔ d.sylowNormalizer : Subgroup G)) :
    ParabolicClosureStructure (P ⊔ d.sylowNormalizer) R := by
  refine ⟨minimal_of_small_core_quotient R hP.quotient,?_,?_⟩
  · exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 P d.sylowNormalizer
        ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hP.fitting)
        ((T.isPGroup'.to_le d.S_le_T).to_le inf_le_left) hP.normalized)
  · let := hP.closure_solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show P ⊔ d.sylowNormalizer ≤ d.parabolicClosure P from
        sup_le le_sup_left (inf_le_left.trans le_sup_right))) (inclusion_injective _)

theorem IsSourceParabolic.normalizer_residual
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hL : d.L ∈ Chapter1.L G d.S) :
    (pResidual 2 (P ⊔ d.sylowNormalizer : Subgroup G)).map
      (P ⊔ d.sylowNormalizer).subtype = (pResidual 2 P).map P.subtype := by
  let E := (pResidual 2 P).map P.subtype
  have hES : d.sylowNormalizer ≤ normalizer (E : Set G) :=
    hP.normalized.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hSP : d.S ⊓ P ≤ d.sylowNormalizer :=
    le_inf inf_le_left (inf_le_right.trans (hP.le_component.trans d.L.le_normalizer))
  have hgen : E ⊔ d.sylowNormalizer = P ⊔ d.sylowNormalizer := by
    have hs := hP.residual_sup_sylow_intersection hL
    rw [←twoResidual_eq_primeToResidual_three hP.twoThree] at hs
    change E ⊔ (d.S ⊓ P) = P at hs
    calc
      E ⊔ d.sylowNormalizer = (E ⊔ (d.S ⊓ P)) ⊔ d.sylowNormalizer := by
        rw [sup_assoc,sup_eq_right.mpr hSP]
      _ = P ⊔ d.sylowNormalizer := congrArg (· ⊔ d.sylowNormalizer) hs
  rw [←hgen]
  exact embedded_pResidual_join_pGroup E d.sylowNormalizer
    ((isPPerfect_pResidual 2).of_surjective
      ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).toMonoidHom
      ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).surjective)
    ((T.isPGroup'.to_le d.S_le_T).to_le inf_le_left) hES

theorem PreExclusionSource.normalizer_no_moving_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (R : Sylow 2 (P ⊔ d.sylowNormalizer : Subgroup G)) :
    ¬ HasMovingAThreeBlock (P ⊔ d.sylowNormalizer) R := by
  rintro ⟨A,hb,ha,_⟩
  let H := P ⊔ d.sylowNormalizer
  have hi := hP.normalizer_structure R
  have hr : primeRank 3 H ≤ 2 :=
    (primeRank_mono 3 (show H ≤ d.parabolicClosure P from
      sup_le le_sup_left (inf_le_left.trans le_sup_right))).trans
      ((hP.closure_sqtk hG h).stronglyQuasithin 3 Nat.prime_three (by decide))
  have he := alternatingThree_orbit_eq_residual hi.fitting hr R hi.minimal A hb ha
  have hm := (cubic_orbit_models hi.fitting hr R A hb ha).2
  rw [he] at hm
  let f : P →* H := inclusion le_sup_left
  have hmap : (pResidual 2 P).map f = pResidual 2 H := by
    apply map_injective H.subtype_injective
    rw [map_map,hP.normalizer_residual s.local_component]
    rfl
  let e : pResidual 2 P ≃* pResidual 2 H :=
    ((pResidual 2 P).equivMapOfInjective f (inclusion_injective _)).trans
      (MulEquiv.subgroupCongr hmap)
  have hmP : pResidual 2 P = ⊥ ∨ Nonempty (pResidual 2 P ≃* AlternatingFourPair.A) ∨
      Nonempty (pResidual 2 P ≃* AlternatingFourPair.Model) := by
    right
    rcases hm with hm | hm
    · obtain ⟨a⟩ := hm
      exact Or.inl ⟨e.trans a⟩
    · obtain ⟨a⟩ := hm
      exact Or.inr ⟨e.trans a⟩
  obtain ⟨a⟩ := ha.equiv_alternatingFour
  exact hP.not_aThree_product (alternatingThree_factors_in_subnormal (pResidual 2 P)
    (inferInstance : (pResidual 2 P).Normal).isSubnormal
    (ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv a ha) hmP)


/-- Restrict the same universal pair to any subgroup between Baum(T) and T.
The central seed grows, while the second characteristic subgroup is unchanged. -/
theorem external_pair_seed_control
    (H : Subgroup G) (R : Sylow 2 H)
    (hBR : baumann (T : Subgroup G) ≤ (R : Subgroup H).map H.subtype)
    (hRT : (R : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u}) :
    ∃ E : CharacteristicPair (baumann (R : Subgroup H)), E.Universal.{u,u} ∧
      FixedPair.firstSeed T D ≤ (FixedPair.firstSeed R E).map H.subtype ∧
      (E.second.map (baumann (R : Subgroup H)).subtype).map H.subtype =
        D.second.map (baumann (T : Subgroup G)).subtype := by
  obtain ⟨E,hE,hfirst,hsecond,_,_⟩ :=
    ChapterC.RankOne.FiveBlockSource.external_pair_transport (T : Subgroup G) H R hBR hRT D hD
  refine ⟨E,hE,?_,hsecond⟩
  intro x hx
  have hxR : x ∈ (R : Subgroup H).map H.subtype := hBR ((map_subtype_le D.first) hx.2)
  obtain ⟨y,hy,rfl⟩ := hxR
  refine mem_map_of_mem H.subtype ⟨?_,?_⟩
  · obtain ⟨_,h2,hc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hx.1
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hy,Subtype.ext h2,fun r hr => Subtype.ext (hc r (hRT (mem_map_of_mem H.subtype hr)))⟩
  · have hxD := hx.2
    rw [←hfirst] at hxD
    obtain ⟨z,hz,hzy⟩ := hxD
    exact H.subtype_injective hzy ▸ hz

/-- The literal normalizer parabolic satisfies the same-pair alternative.
All its minimality, solvability and residual-block hypotheses are proved above. -/
theorem PreExclusionSource.normalizer_pair_alternative
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (R : Sylow 2 (P ⊔ d.sylowNormalizer : Subgroup G))
    (E : CharacteristicPair (baumann (R : Subgroup (P ⊔ d.sylowNormalizer : Subgroup G))))
    (hE : E.Universal.{u,u}) :
    FixedPair.firstSeed R E ≤ center (P ⊔ d.sylowNormalizer : Subgroup G) ∨
      (E.second.map (baumann (R : Subgroup (P ⊔ d.sylowNormalizer : Subgroup G))).subtype).Normal := by
  by_cases hc : FixedPair.firstSeed R E ≤ center (P ⊔ d.sylowNormalizer : Subgroup G)
  · exact Or.inl hc
  by_cases hn : (E.second.map
      (baumann (R : Subgroup (P ⊔ d.sylowNormalizer : Subgroup G))).subtype).Normal
  · exact Or.inr hn
  have hi := hP.normalizer_structure R
  let := hi.solvable
  have hr : primeRank 3 (P ⊔ d.sylowNormalizer : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (show P ⊔ d.sylowNormalizer ≤ d.parabolicClosure P from
      sup_le le_sup_left (inf_le_left.trans le_sup_right))).trans
      ((hP.closure_sqtk hG h).stronglyQuasithin 3 Nat.prime_three (by decide))
  exact (s.normalizer_no_moving_block (h := h) hG hP R
    (FixedPairSolvable.NormalBaumann.minimal_parabolic_moving_alternatingThree_of_fixed_pair_escape
      R hi.minimal hi.fitting E hE (fixed_pair_control_ne_top R hi.minimal E hc hn)
      hr inferInstance)).elim

/-- Placement from Baumann normalization, allowing S to move L. One universal
pair is chosen before P, and its two literal images control all parabolics. -/
theorem PreExclusionSource.parabolic_placement_of_baumann_normalizes
    {d : CaseIComponentData T M Mc V} {p : ℕ}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (s : d.PreExclusionSource h.normalized p)
    (hnB : baumann d.S ≤ normalizer (d.L : Set G)) :
    ∀ P ∈ d.sourceParabolics, P ≤ M ⊓ d.L ∨ P ≤ d.ML := by
  obtain ⟨D,hD,_⟩ := FixedPair.exists_uniform_pair.{u,u}
    T (MainForward.sylow_ne_bot hG T)
  have hB := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).2.1
  intro P hP
  change d.IsSourceParabolic P at hP
  let H := P ⊔ d.sylowNormalizer
  obtain ⟨R,hR⟩ := hP.normalizer_sylow s.local_component
  have hBR : baumann (T : Subgroup G) ≤ (R : Subgroup H).map H.subtype := by
    rw [hR,←hB]
    exact le_inf inf_le_left hnB
  have hRT : (R : Subgroup H).map H.subtype ≤ (T : Subgroup G) := by
    rw [hR]
    exact inf_le_left.trans d.S_le_T
  obtain ⟨E,hE,hfirst,hsecond⟩ := external_pair_seed_control H R hBR hRT D hD
  rcases s.normalizer_pair_alternative (h := h) hG hP R E hE with hc | hn
  · right
    apply le_inf (le_inf (hP.le_component.trans d.L_component.1) ?_) hP.le_component
    have hHC : H ≤ centralizer (FixedPair.firstSeed T D : Set G) := by
      intro x hx z hz
      obtain ⟨a,ha,rfl⟩ := hfirst hz
      exact (congrArg H.subtype ((mem_center_iff.mp (hc ha)) ⟨x,hx⟩)).symm
    exact (show P ≤ H from le_sup_left).trans (hHC.trans
      (UniformControl.firstSeed_centralizer_le_partner T D hu))
  · left
    refine le_inf ?_ hP.le_component
    let := hn
    have hHN := (E.second.map (baumann (R : Subgroup H)).subtype).le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hsecond] at hHN
    exact (show P ≤ H from le_sup_left).trans
      (hHN.trans (d.pair_second_normalizer_le D hG hM hJ h))

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
