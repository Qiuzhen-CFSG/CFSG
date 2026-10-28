module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.NaturalBlocks
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Normal.CubicKernel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2ThompsonBorel
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFivePlaneCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.CubicNormalizer

/-!
# Natural and alternating-five block placement in the nonsingular normal branch

The original movement identity makes J(Q) normalize the escaping block.
For a natural block, its Borel therefore normalizes J(Q), so uniqueness for
LT places that Borel in M. The odd-actor fixed-point argument then puts the
whole natural block in M. For an alternating-five block, its Borel fixes
W inside the two-core of the section centralizer. Its cubic element would
belong to the actual three-prime kernel C_M(W), an impossibility.

Thus an escaping chi-zero block is an actual alternating-three block,
with all relative subnormality and common-normal hypotheses retained.
The cubic exclusion, component and parabolic branches remain with
qt-d-double-natural-centralizers; qt-d-1222-double-natural owns final assembly.
Source: Aschbacher--Smith, 12.1.1, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter4 ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem block_sylow_below {Y Q K : Subgroup G}
    (P : Sylow 2 Y) (hP : (P : Subgroup Y).map Y.subtype = Q)
    (hKY : K ≤ Y) (hK : (K.subgroupOf Y).IsSubnormal) :
    ∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype ≤ Q := by
  obtain ⟨R,hR⟩ := P.exists_subgroupOf_eq_of_subnormal (K.subgroupOf Y) hK
  let e := subgroupOfEquivOfLe hKY
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro x ⟨k,⟨r,hr,rfl⟩,rfl⟩
  rw [hR] at hr
  exact hP ▸ mem_map_of_mem Y.subtype hr

/-- The original Thompson movement places the natural block's Borel in M. -/
theorem doubleNatural_normal_natural_borel_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ →
        ∀ k, IsL2EvenBlock K k → ∃ P : Sylow 2 K,
          (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hn K hKY hK hmove k hnat
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨R,hR⟩ := D.doubleNatural_adapted_normal_sectionCentralizer_sylow h B S w hw hn
  obtain ⟨P,hP⟩ := block_sylow_below R hR hKY hK.subnormal
  have hJN : elementaryAbelianMaxJ Q ≤ normalizer (K : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.symm.le
  have hJne : elementaryAbelianMaxJ Q ≠ ⊥ :=
    elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _)
      h.maximal_faithful.1.1.2.2
  refine ⟨P,(hnat.borel_normalizes_thompson K Q (isPGroup_pCoreIn 2 _) P hP hJN).trans ?_⟩
  exact (normalizer_maxJ_le_characteristicNormalizerClosure Q Q
    (sSup_le fun _ hA => hA.1) le_rfl hJne).trans
      (D.doubleNatural_core_characteristicNormalizerClosure h)

/-- The normal-residual branch contains every Thompson-moved natural block in M. -/
theorem doubleNatural_normal_natural_block_le
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ →
        ∀ k, IsL2EvenBlock K k → K ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn K hKY hK hmove k hnat
  obtain ⟨P,hP⟩ := D.doubleNatural_normal_natural_borel_placement h B S w hw hn
    K hKY hK hmove k hnat
  exact D.doubleNatural_normal_natural_block_le_of_borel h B S w hw hc hn
    K hKY hK k hnat P hP

/-- The A₅ block's Borel fixes W, contradicting the actual three-prime kernel. -/
theorem doubleNatural_normal_no_alternatingFive_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ∀ K : Subgroup G,
        K ≤ sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w) →
        IsBlock (K.subgroupOf
          (sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w))) →
        ¬ IsAlternatingBlock K 5 := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn K hKY hK ha
  let Y := sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)
  let W := componentOrbit V (T : Subgroup G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let X := K.subgroupOf Y
  obtain ⟨P,hP⟩ := D.doubleNatural_adapted_normal_sectionCentralizer_sylow h B S w hw hn
  obtain ⟨R,hR⟩ := P.exists_subgroupOf_eq_of_subnormal X hK.subnormal
  have hQW : Q ≤ centralizer (W : Set G) := by
    dsimp only [Q]
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact inf_le_right
  have hWQ : W ≤ Q := by
    dsimp only [Q]
    rw [←D.doubledOrbit_sylow_centralizer h]
    exact le_inf (D.doubledOrbit_E322 h).le_sylow
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hWY : W ≤ Y := hWQ.trans (hP.symm.le.trans (map_subtype_le _))
  have hWP : W.subgroupOf Y ≤ centralizer (P : Set Y) := by
    intro z hz p hp
    exact Subtype.ext (hQW (hP.le (mem_map_of_mem Y.subtype hp)) z hz).symm
  have hWcore : W.subgroupOf Y ≤ pCore 2 Y := by
    have hf := doubleNatural_normal_sectionCentralizer_characteristic B w hc hn
    have hh := centralizer_generalizedFitting_le Y
    rw [hf] at hh
    exact hWP.trans ((centralizer_le (pCore_isPGroup.le_sylow_of_normal P)).trans hh)
  have hWR : W.subgroupOf Y ≤
      centralizer ((R : Subgroup X).map X.subtype : Set Y) := by
    apply hWP.trans (centralizer_le ?_)
    rintro x ⟨r,hr,rfl⟩
    rw [hR] at hr
    exact hr
  have haX : IsAlternatingBlock X 5 := ha.of_mulEquiv (subgroupOfEquivOfLe hKY).symm
  have hBW := (haX.sylowNormalizer_centralizes_core_fixed X hK R).trans
    (centralizer_le (le_inf hWcore hWR))
  obtain ⟨a,haB,ha3⟩ := haX.exists_sylow_normalizer_cubic R
  have haW : (a : Y) ∈ centralizer (W.subgroupOf Y : Set Y) :=
    hBW (mem_map_of_mem X.subtype haB)
  let c : G := ((a : Y) : G)
  have hcW : c ∈ centralizer (W : Set G) := by
    intro z hz
    exact congrArg Subtype.val (haW ⟨z,hWY hz⟩ hz)
  have hcM : c ∈ normalizer (L : Set G) := by
    rw [←D.doubledOrbit_normalizer_eq h B.orbit_eq]
    exact Subgroup.centralizer_le_normalizer _ hcW
  let C := normalizer (L : Set G) ⊓ centralizer (W : Set G)
  let cC : C := ⟨c,hcM,hcW⟩
  have hc3 : orderOf cC = 3 := by
    rw [←orderOf_injective C.subtype C.subtype_injective cC]
    exact (orderOf_injective Y.subtype Y.subtype_injective (a : Y)).trans
      ((orderOf_injective X.subtype X.subtype_injective a).trans ha3)
  have hd : 3 ∣ Nat.card C := hc3 ▸ orderOf_dvd_natCard cC
  exact (Nat.prime_three.coprime_iff_not_dvd.mp
    (D.doubleNatural_orbitCentralizer_three_prime h B)) hd

/-- The outside block of the normal-residual branch must be an actual A₃ block. -/
theorem doubleNatural_adapted_normal_outside_alternatingThree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      generalizedFitting (B.pointCentralizer w) = pCore 2 (B.pointCentralizer w) →
      ((B.pointResidual w).subgroupOf (B.pointCentralizer w)).Normal →
      ¬ B.pointCentralizer w ≤ normalizer (L : Set G) →
      let Y := sectionCentralizerIn (B.pointCentralizer w) (B.pointResidual w)
      ∃ K : Subgroup G, K ≤ Y ∧ IsBlock (K.subgroupOf Y) ∧
        IsBlock (K.subgroupOf (B.pointCentralizer w)) ∧ IsAlternatingBlock K 3 ∧
        ¬ K ≤ normalizer (L : Set G) ∧
        K = ⁅K,elementaryAbelianMaxJ ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ ∧
        ∀ N : Subgroup G, N ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
          (N.subgroupOf ((L ⊔ (T : Subgroup G)) ⊔ (K ⊔ B.pointSylow w))).Normal → N = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hc hn hout
  obtain ⟨K,hKY,hK,hKH,hKM,hmove,hno⟩ :=
    D.doubleNatural_adapted_normal_outside_chiZero h B S w hw hc hn hout
  let e := subgroupOfEquivOfLe hKY
  have ht : IsChiZeroBlock K := Section05.BlockAnalysis.chiZero_equiv e hK.2
  have ha : IsAlternatingBlock K 3 := by
    rcases ht with ⟨k,hk⟩ | hk | hk
    · exact (hKM (D.doubleNatural_normal_natural_block_le h B S w hw hc hn
        K hKY hK.1 hmove k hk)).elim
    · exact hk
    · exact (D.doubleNatural_normal_no_alternatingFive_block h B S w hw hc hn
        K hKY hK.1 hk).elim
  exact ⟨K,hKY,hK.1,hKH.1,ha,hKM,hmove,hno⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
