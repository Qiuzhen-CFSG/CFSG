module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticHallParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticSixParameters
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerReduction
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.Action

/-!
# The actual odd normalizers for the paired symplectic rows

The original pair coordinates give dimensions 8n and 8. An odd actor
fixing the whole orbit has a perfect fixed residual R covering L modulo
O₂(L), with W = [W,R] and W <= O₂(R). Since |W| > 8, A.1.26/28 makes W
centralize the odd core of N_G(A); E.6.1 places that core in N_G(L).

If the residual has a unique maximal overgroup, the escaping normalizer
has trivial two-core. Generalized-Fitting detection then selects an
outside component K with [K,W] = K, preserving the full central cover,
quasithinness and known-simple quotient. Otherwise the original maximal
pushing-up pair contains W in its two-core. The final applications attach
these literal configurations to the Hall actor already produced for each
symplectic row. Their exclusion and the actual Cartan upper bounds remain
necessary for 7.3.4; no upper weak-closure bound is asserted here.

Source: Aschbacher--Smith 4.4.5--10 and 7.3.4,
printed pp.620--621,699, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter4 Chapter4.Section04
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Both marked seed axes give the dimension of the entire original symplectic orbit. -/
theorem sourceOrbit_symplectic_dimension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
    Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 8 * F.degree := by
  obtain ⟨_,_,_,_,_,e,_⟩ := D.sourceOrbit_symplectic_pair_coordinates h hd F hmodel
  exact e.finrank_eq.trans (SymplecticConjugatePair.finrank_space F.card_eq)

/-- The two genuine derived binary summands give dimension eight. -/
theorem sourceOrbit_six_dimension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 8 := by
  obtain ⟨_,_,_,_,_,e,_⟩ := D.sourceOrbit_six_pair_coordinates h hd hmodel
  exact e.finrank_eq.trans
    (SymplecticConjugatePair.finrank_space (F := ZMod 2) (n := 1) (by norm_num))

private theorem sourceOrbit_card_gt_eight_of_rank
    (hsize : 4 ≤ Module.finrank (ZMod 2) (Additive D.sourceOrbit)) :
    8 < Nat.card D.sourceOrbit := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
  rw [Nat.card_congr Additive.toMul,Nat.card_zmod] at hc
  rw [hc]
  exact lt_of_lt_of_le (by decide : 8 < 2^4)
    (Nat.pow_le_pow_right (by decide) hsize)

omit D [Finite G] [Group G] in
private theorem perfect_twoPerfect {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] :
    IsPPerfect 2 X := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (X ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (X ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

private theorem sourceOrbit_whole_oddNormalizer_oddCore_of_large
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hsize : 8 < Nat.card D.sourceOrbit)
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      normalizer (L : Set G) := by
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let R := oddActorResidual L A
  have hRN : R ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hWN : W ≤ N := (le_centralizer_iff.mp hAC).trans
    (Subgroup.centralizer_le_normalizer _)
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hm : W = ⁅W,R⁆ := by
    simpa only [←D.sourceOrbit_eq] using (D.doubledOrbit_oddActorResidual_cover h A hA ho).2.1
  let : Group.IsPerfect R := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (R.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hRN).symm.toMonoidHom) (subgroupOfEquivOfLe hRN).symm.surjective
  have hmN : W.subgroupOf N = ⁅W.subgroupOf N,R.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,map_subgroupOf_eq_of_le hRN]
    exact hm
  have hsizeN : 8 < Nat.card (W.subgroupOf N) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hWN).toEquiv]
  let : IsElementaryAbelian 2 (W.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  have hh := ChapterA.large_elementary_commutator_centralizes_oddCore
    (h.simpleQTKE.quasithin.subgroup N) (R.subgroupOf N) (W.subgroupOf N)
      perfect_twoPerfect hsizeN hmN
  have hcomm : ⁅W,(pPrimeCore 2 N).map N.subtype⁆ = ⊥ := by
    simpa only [map_commutator,map_subgroupOf_eq_of_le hWN,Subgroup.map_bot] using
      congrArg (Subgroup.map N.subtype) hh
  exact ⟨hcomm,(le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)).trans
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le⟩

/-- The whole nonbinary orbit centralizes the actual odd normalizer odd core, placing it in N_G(L). -/
theorem sourceOrbit_symplectic_oddNormalizer_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2))))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      normalizer (L : Set G) := by
  apply D.sourceOrbit_whole_oddNormalizer_oddCore_of_large h hd _ A hAC ho
  apply D.sourceOrbit_card_gt_eight_of_rank
  rw [D.sourceOrbit_symplectic_dimension h hd F hmodel]
  omega

/-- The whole A₆ orbit centralizes the actual odd normalizer odd core, placing it in N_G(L). -/
theorem sourceOrbit_six_oddNormalizer_oddCore
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) :
    ⁅D.sourceOrbit,(pPrimeCore 2 (normalizer (A : Set G))).map
      (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
    (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
      normalizer (L : Set G) := by
  apply D.sourceOrbit_whole_oddNormalizer_oddCore_of_large h hd _ A hAC ho
  apply D.sourceOrbit_card_gt_eight_of_rank
  rw [D.sourceOrbit_six_dimension h hd hmodel]
  decide

private theorem sourceOrbit_whole_oddNormalizer_component_of_large
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hsize : 8 < Nat.card D.sourceOrbit)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) := by
  let W := D.sourceOrbit
  let N := normalizer (A : Set G)
  let Y := (normalizer (L : Set G)).subgroupOf N
  have hWN : W ≤ N := (le_centralizer_iff.mp hAC).trans
    (Subgroup.centralizer_le_normalizer _)
  have hA : A ≤ normalizer (L : Set G) ⊓
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
    rw [←D.sourceOrbit_eq]
    exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hcore : pCore 2 N = ⊥ := (oddNormalizer_reduction_of_cover_uniqueness D A hu hout).2
  have hvY : W.subgroupOf N ≤ Y.pCoreIn 2 := by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hWN,map_pCoreIn_of_injective 2 Y N.subtype N.subtype_injective]
    have hh := D.doubledOrbit_oddNormalizer_intersection_core h A hA ho
    simpa only [Y,subgroupOf_map_subtype,N,←D.sourceOrbit_eq] using hh
  have hvne : W.subgroupOf N ≠ ⊥ := by
    intro hb
    have hh := congrArg (Subgroup.map N.subtype) hb
    rw [map_subgroupOf_eq_of_le hWN,Subgroup.map_bot] at hh
    exact D.sourceOrbit_weakClosure_setup.nontrivial hh
  have hvodd : ⁅W.subgroupOf N,pPrimeCore 2 N⁆ = ⊥ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWN,Subgroup.map_bot]
    exact (D.sourceOrbit_whole_oddNormalizer_oddCore_of_large h hd hsize A hAC ho).1
  have hp : IsPGroup 2 (W.subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 W).comap_subtype
  obtain ⟨K,hK,hm,houtK⟩ := exists_component_moved_outside_of_centralizes_oddCore
    (W.subgroupOf N) Y hp hvne hcore hvodd hvY
  have hout' : ¬ K.map N.subtype ≤ normalizer (L : Set G) :=
    fun he => houtK (map_le_iff_le_comap.mp he)
  have hKcore : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,hcore,MonoidHom.comap_bot]
    exact K.subtype.ker_eq_bot K.subtype_injective
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK h.simpleQTKE A hne
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨_,hRK,_⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) K hK
  have hWR : W ≤ oddActorResidual L A := by
    have hh := (D.doubledOrbit_oddActorResidual_cover h A hA ho).2.2.1.trans (pCoreIn_le 2 _)
    simpa only [←D.sourceOrbit_eq] using hh
  have hWK := (comap_mono (f := N.subtype) hWR).trans hRK
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hWK hm,hout',hKcore,hqt.subgroup K,
    hkg.simple_quotient K (center K),hRK,hWK⟩


private theorem sourceOrbit_whole_oddLocal_obstruction_of_large
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hsize : 8 < Nat.card D.sourceOrbit)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hAC : A ≤ centralizer (D.sourceOrbit : Set G)) (ho : Odd (Nat.card A))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    (∃ J P : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G)))) := by
  by_cases hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))
  · exact Or.inr (D.sourceOrbit_whole_oddNormalizer_component_of_large
      h hd hsize A hne hAC ho hu hout)
  · apply Or.inl
    have hA : A ≤ normalizer (L : Set G) ⊓
        centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
      rw [←D.sourceOrbit_eq]
      exact le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
    simpa only [←D.sourceOrbit_eq] using D.doubledOrbit_oddNormalizer_pushingUp h A hA ho hu


open ChapterE ChapterE.Section06.FixedPointBounds in
/-- The nonbinary original Hall actor supplies a maximal pushing-up pair or an outside component fully moved by W. -/
theorem sourceOrbit_symplectic_cartan_or_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
    F.degree < nPrime (normalizerPCoreQuotientAction L).range ∨
      ∃ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      F.degree < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
    ((∃ J P : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))) := by
  rcases D.sourceOrbit_symplectic_cartan_or_odd_escape h hd hmany hnon F hn hmodel with hc | hx
  · exact Or.inl hc
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout⟩ := hx
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  refine Or.inr ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,?_⟩
  apply D.sourceOrbit_whole_oddLocal_obstruction_of_large h hd _ A hne hAC hodd hout
  apply D.sourceOrbit_card_gt_eight_of_rank
  rw [D.sourceOrbit_symplectic_dimension h hd F hmodel]
  omega

open ChapterE ChapterE.Section06.FixedPointBounds in
/-- The binary derived original Hall actor supplies the same literal local configurations. -/
theorem sourceOrbit_six_cartan_or_oddLocal_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    1 < nPrime (normalizerPCoreQuotientAction L).range ∨
      ∃ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      1 < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
    ((∃ J P : Subgroup G,
      J ∈ muStar (normalizer (L : Set G)) L
        (coveringOvergroup (normalizer (L : Set G)) L (oddActorResidual L A)) ∧
      PushLE L (oddActorResidual L A) J ∧
      IsMaximalTwoLocal P ∧ J ≤ P ∧ ¬ P ≤ normalizer (L : Set G) ∧
      IsSQTK KnownSimple.IsKnownSimple P ∧ D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L) ∨
    (∃ K : Subgroup (normalizer (A : Set G)),
      IsComponent (normalizer (A : Set G)) K ∧
      ⁅K,D.sourceOrbit.subgroupOf (normalizer (A : Set G))⁆ = K ∧
      ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))) ∧
      D.sourceOrbit.subgroupOf (normalizer (A : Set G)) ≤
        normalizer (K : Set (normalizer (A : Set G))))) := by
  rcases D.sourceOrbit_six_cartan_or_odd_escape h hd hmany hnon hmodel with hc | hx
  · exact Or.inl hc
  obtain ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout⟩ := hx
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hn]
    exact ho.pow
  refine Or.inr ⟨H,hH,hgen,p,A,hp,ho,hne,he,hAH,hAL,hAC,hAT,hout,?_⟩
  apply D.sourceOrbit_whole_oddLocal_obstruction_of_large h hd _ A hne hAC hodd hout
  apply D.sourceOrbit_card_gt_eight_of_rank
  rw [D.sourceOrbit_six_dimension h hd hmodel]
  decide

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
