module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.Parabolic
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.RadicalFactor
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.SourceCases.Sylow
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Geometry.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.LocalActions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Planes
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.FixedSpaces.Extension.Contradiction
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.SpecificGroups.PSL3Two.Cardinality

/-!
# The residual reduction in the original PSL₃(2) branch

The actual component quotient gives three-rank one and inner residual action.
The original 15.3.12 therefore supplies both residual three-parts and the
rank-two quotient of Y₊. The proper Sylow overgroup gives the marked parabolic;
its residual yields the radical factorization used in the extension argument.
That argument proves [V,Y_L] nontrivial, after which the source residual
geometry forces the first choice, S-normalization and exchanged planes.

Only the earlier 15.3.16 elementary-span and Thompson-commutator assertions,
and C.2.7 radical saturation, remain explicit here. Their producers belong to
the characteristic-two source assembly.

Source: Aschbacher–Smith, 15.3.23, printed pp.1128–1129.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
open ComponentIntersection ComponentIntersection.InnerSplitting OutsideStructure
open ChapterA.Section05To06 RankTwo
variable {G : Type*} [Group G] [Finite G]

theorem component_three_rank {I : Subgroup G} (d : LocalData G)
    (c : ComponentWitness d I) (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL) :
    primeRank 3 c.L = 1 := by
  apply le_antisymm ?_ c.rank_pos
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 c.L) pCore_isPGroup, primeRank_congr 3 e]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  have hd : Nat.card E ∣ 3 * 56 := by
    simpa only [Matrix.PSL3Two.card_SL] using E.card_subgroup_dvd_card
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hp : Nat.Coprime (Nat.card E) 56 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 56).pow_left n
  exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

omit [Finite G] in
theorem inner_on_component_quotient {Y L : Subgroup G}
    (hn : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    InducesInnerOnTwoCoreQuotient Y L := by
  let a := (sectionAction L).comp (inclusion hn)
  let f := (QuotientGroup.mk' (MulAut.innerSubgroup (L ⧸ pCore 2 L))).comp a
  have ho : IsPGroup 2 (MulAut.Outer (L ⧸ pCore 2 L)) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr e).symm
  have hf : f = 1 := hp.hom_eq_one_of_isPGroup ho f
  intro y hy
  have ha : a ⟨y, hy⟩ ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L) :=
    (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hf ⟨y, hy⟩)
  obtain ⟨q, hq⟩ := ha
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  refine ⟨l, l.property, ?_⟩
  apply (sectionAction_eq_one_iff L
    ((inclusion L.le_normalizer l)⁻¹ * inclusion hn ⟨y, hy⟩)).mp
  rw [map_mul, map_inv, sectionAction_on_component]
  exact inv_mul_eq_one.mpr hq

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (d : LocalData G)
  (hempty : MainForward.faithfulLocalComponents d.T = ∅)
  (hM : IsOrderingMaximal d.T d.M)
  (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
  (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
  (hne : d.Mc ≠ d.M)
  (hBaum : normalizer (ChapterB.baumann (d.T : Subgroup G) : Set G) ≤ d.M)
  {I : Subgroup G} (hI : I ∈ d.Hplus) (c : ComponentWitness d I)
  (hrank : primeRank 3 d.Yplus = 2)

omit [Finite G] in
theorem residual_normalizes_component : d.Yplus ≤ normalizer (c.L : Set G) := by
  exact le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge

include hG hempty hM hu hmany hne hBaum hI hrank

theorem residual_split (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL) :
    d.Yplus = YL d c.L ⊔ YC d c.L ∧
      Nat.card (d.Yplus ⧸ pCore 2 d.Yplus) = 9 ∧
      Nonempty ((d.Yplus ⧸ pCore 2 d.Yplus) ≃* ElementaryNine) ∧
      3 ^ (Nat.card (YL d c.L)).factorization 3 = 3 ∧
      3 ^ (Nat.card (YC d c.L)).factorization 3 = 3 := by
  have hn := residual_normalizes_component d c
  have hi := inner_on_component_quotient hn (yplus_perfect_of_choice d.choice) e
  obtain ⟨hprod, _, h9, _, he9, hL, hC⟩ :=
    source_lemma_15_3_12_2_three_parts hG d hempty hM hu hmany hne hBaum hI
      (component_le c) (Extension.SourceCases.component_in_overgroup d c)
      hrank (component_three_rank d c e) hi
  refine ⟨le_antisymm ?_ (sup_le
    ((intersectionResidual_le _ _).trans inf_le_left)
    ((centralizerResidual_le _ _).trans inf_le_left)), h9, he9, hL, hC⟩
  intro y hy
  change y ∈ (d.Yplus : Set G) at hy
  rw [hprod] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  exact (YL d c.L ⊔ YC d c.L).mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem noncentral_action
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hfactor : d.R = (c.L ⊔ d.R).pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2) :
    ⁅d.V, YL d c.L⁆ ≠ ⊥ := by
  let := helem
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  have htwo := rank_two_case_of_three_rank_two d I h11.local_structure hrank
  have hR := htwo.2.2.2.2.1
  obtain ⟨hYL, hRL, hprod⟩ := source_lemma_15_3_12_1 hG d hempty hM hu hmany hne
    hBaum hI (component_le c) (Extension.SourceCases.component_in_overgroup d c)
    hrank c.rank_pos
  have hcore : c.L.pCoreIn 2 ≤ d.R := by
    intro x hx
    exact hprod ⟨x, hx, 1, ((YL d c.L).pCoreIn 2).one_mem, mul_one x⟩
  have hn := residual_normalizes_component d c
  have hN := overgroup_normalizes_span d h11.theta_eq.symm
    (hR.le.trans inf_le_right) hRL hn
  let := actionKernel_normal d hN
  have hC : centralizer (d.V : Set G) ≤ d.M := by
    have he := InitialSource.UniformControl.source_local_eq_normalizer hG d.T hM.1
    exact (Subgroup.centralizer_le_normalizer _).trans he.ge
  obtain ⟨_, ⟨m, _, ⟨q⟩⟩, ⟨l, hlR, ht, hlne⟩, hcases⟩ :=
    Extension.LocalActions.local_actions d c hN e hR hcore hC hJR hfactor
  obtain ⟨hgen, _, he9, _, _⟩ := residual_split hG d hempty hM hu hmany hne hBaum hI c hrank e
  obtain ⟨hi, _, _, _, _, _, h7⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  have h7' : d.Y ⊓ centralizer (d.V : Set G) ≤ d.Y.pCoreIn 2 ∨
      Nat.card (d.Y ⧸ pCore 2 d.Y) = 27 := by
    rcases h7 with h | h
    · exact Or.inl h.1.ge
    · exact Or.inr ((Nat.card_congr h.1.some.toEquiv).trans HeisenbergPrime.card)
  exact Extension.nontrivial_of_module_and_plane_actions d c.L hN e c.outside
    hR hcore q l hlR ht hlne hn hcases
    (Extension.centralizing_plane_actions d c.L hYL he9 h7' hi hgen)

theorem residual_geometry
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hfactor : d.R = (c.L ⊔ d.R).pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2)
    (hpar : ∃ (P : Subgroup Matrix.PSL3Two.SL) (g : Matrix.PSL3Two.SL),
      (P = Matrix.PSL3Two.pointParabolicSL ∨ P = Matrix.PSL3Two.lineParabolicSL) ∧
      ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = P.conjBy g) :
    ⁅d.V, YL d c.L⁆ ≠ ⊥ ∧ ResidualSourceData d c.L e ∧ ResidualGeometry d c.L := by
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  have htwo := rank_two_case_of_three_rank_two d I h11.local_structure hrank
  obtain ⟨hgen, h9, _, hL3, hC3⟩ :=
    residual_split hG d hempty hM hu hmany hne hBaum hI c hrank e
  have hn := residual_normalizes_component d c
  obtain ⟨_, _, hprod⟩ := source_lemma_15_3_12_1 hG d hempty hM hu hmany hne
    hBaum hI (component_le c) (Extension.SourceCases.component_in_overgroup d c)
    hrank c.rank_pos
  have hcore : c.L.pCoreIn 2 ≤ d.R := by
    intro x hx
    exact hprod ⟨x, hx, 1, ((YL d c.L).pCoreIn 2).one_mem, mul_one x⟩
  have hi := (source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action
    hM hu hmany hne).1
  have hs : ResidualSourceData d c.L e :=
    ⟨hi, h9, htwo.2.1, hn, hL3, hC3, hgen, hcore, htwo.2.2.2.2.1, hpar⟩
  have hnc := noncentral_action hG d hempty hM hu hmany hne hBaum hI c hrank e
    helem hJR hfactor
  exact ⟨hnc, hs, residual_geometry_of_source d hI c e hs
    (hG.evenCharacteristic d.T) hnc⟩

/-- The complete residual reduction from the original preliminary hypotheses.
The only extra inputs are source 15.3.16's elementary span and Thompson
commutator, and the proved C.2.7 saturation inequality. -/
theorem residual_geometry_of_original
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.PSL3Two.SL)
    (helem : IsElementaryAbelian 2 (d.componentSpan c.L))
    (hJR : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hsat : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R) :
    ⁅d.V, YL d c.L⁆ ≠ ⊥ ∧ ResidualSourceData d c.L e ∧ ResidualGeometry d c.L := by
  have h11 := source_lemma_15_3_11 hG d hempty hM hu hmany hne hBaum I hI
  obtain ⟨hYL, hRL, hprod⟩ := source_lemma_15_3_12_1 hG d hempty hM hu hmany hne
    hBaum hI (component_le c) (Extension.SourceCases.component_in_overgroup d c)
    hrank c.rank_pos
  have hcores : c.L.pCoreIn 2 ⊔ (YL d c.L).pCoreIn 2 ≤ d.R := by
    apply sup_le
    · intro x hx
      exact hprod ⟨x, hx, 1, ((YL d c.L).pCoreIn 2).one_mem, mul_one x⟩
    · intro x hx
      exact hprod ⟨1, (c.L.pCoreIn 2).one_mem, x, hx, one_mul x⟩
  obtain ⟨P, hP⟩ := h11.sylow
  obtain ⟨e', M, hstd, _, hmark⟩ :=
    exists_standard_component_residual_marking d c P hP hYL e
  have hfactor := radical_factor d c.L hRL hcores hsat e' M hstd hmark
  exact residual_geometry hG d hempty hM hu hmany hne hBaum hI c hrank e
    helem hJR hfactor (component_parabolic_of_sylow d c P hP hYL e)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource
