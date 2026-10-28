module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.Reduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.QuotientModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Linear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Triality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Ree
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.Reduction
public import CFSG.Quasithin.MainConverse.RankOneLocal
public import CFSG.Quasithin.MainConverse.SuzukiEven
public import CFSG.Quasithin.MainConverse.ExceptionalLocal.G2Small.BinaryCover
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeObstruction
public import Theory.GroupTheory.Fitting.Subgroup
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.InnerGeometry
public import Theory.SpecificGroups.Tits.ConverseLocalCores.First
public import Theory.SpecificGroups.Tits.ConverseLocalCores.Second
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage
public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Bruhat
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.StandardOvergroups
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Sylow
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Bruhat
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.StandardOvergroups

/-!
# Self-centralizing cores across the quotient action catalogue

The complete 1.1.5(3)(a)--(c) catalogue transports to the actual component
L/Z(L) in the centralizer quotient, including the central covers. For the
binary linear groups, Bruhat factorization puts every proper Borel overgroup
inside a subspace stabilizer. The rank-one, alternating-six and Tits branches
use their actual Sylow overgroup geometry. Self-centralizing two-cores pass
to intermediate Sylow overgroups, so these arguments include the Borel itself.
The established PSL₃, triality (also at two) and Ree calculations cover the
other branches; only the larger-field PSp₄ and G₂ producers remain explicit.

The small derived G₂ branch is excluded directly from the local setup,
without assuming parabolic recognition: its actual local intersection has
order divisible by nine and a nontrivial two-core, whereas the two concrete
restricted G₂(2) parabolics have no factor of nine. The binary PSL₃ branch
uses the already established independent setup obstruction. Every model
comparison uses the equivalence supplied by the catalogue or an established
concrete exceptional isomorphism.

Finally, restriction of the specified quotient Sylow subgroup and the
intrinsic/ambient Borel identity give precisely the core premise consumed by
`quotientParabolic_of_borel_join_and_cores`. The source-theorem owner must still
discharge the two split-family producers and Borel-join properness.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41 and
the first paragraph of the final proof of 15.3.35, printed pp.1138--1139;
1.1.5(3)(a)--(c), pp.501--502; and A.2.3--4, p.33. The G₂ calculations use
the existing licensed ATLAS octonion port; see `LICENSES/ATLAS.txt`.
-/

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.RankTwo
open CFSG.Quasithin.ClassificationModels
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
open CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open BinaryLinear.OuterCyclic
open Theory.SpecificGroups.SymmetricSix
open BinaryLinear.FiveFlagGeometry.SylowOvergroups
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.Recognition

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

omit [Finite G] in
private theorem core_of_catalogue_covers
    (D T : Subgroup (CentralizerQuotient L))
    (hc : BorelOvergroupCores D)
    (hP : ∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = T ⊓ D) :
    ∀ Q : Subgroup (CentralizerQuotient L),
      sylowBorel D T ≤ Q → Q < D →
      T ≤ normalizer (Q : Set (CentralizerQuotient L)) →
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
  obtain ⟨P, hP⟩ := hP
  have hp : ParabolicCores D T :=
    parabolicCores_of_borelOvergroupCores D T P hP hc
  intro Q hQ hQD hN
  apply hp Q
  · simpa only [Recognition.sylowBorel_eq_borel] using hQ
  · exact hQD
  · exact hN

private theorem rank_one_borelOvergroupCores
    (D : Type*) [Group D] [Finite D] [IsSimpleGroup D]
    (hna : ¬ IsMulCommutative D)
    (he : IsEvenCharacteristic D)
    (hf : ∀ T : Sylow 2 D, RankOneSylowFacts T) : BorelOvergroupCores D := by
  intro T Q hBQ hQ
  have hTne : (T : Subgroup D) ≠ ⊥ := by
    intro hzero
    change (T : Subgroup D) = ⊥ at hzero
    have hproper := (hf T).proper
    have htop : normalizer ((T : Subgroup D) : Set D) = ⊤ := by
      rw [hzero, normalizer_eq_top]
    exact hproper.ne (htop ▸ rfl)
  have hmax : IsMaximalTwoLocal (normalizer (T : Set D)) := by
    refine ⟨⟨T, hTne, T.isPGroup', rfl⟩, ?_⟩
    intro U hU hNU
    exact (hf T).unique_maximal U
      ((T : Subgroup D).le_normalizer.trans hNU)
      (lt_top_iff_ne_top.mpr (twoLocal_ne_top_of_nonabelian_simple hna hU))
  have hc : centralizer (pCore 2 (normalizer (T : Set D)) :
      Set (normalizer (T : Set D))) ≤ pCore 2 (normalizer (T : Set D)) :=
    he T (normalizer (T : Set D)) hmax (T : Subgroup D).le_normalizer
  have hTQ : (T : Subgroup D) ≤ Q :=
    (T : Subgroup D).le_normalizer.trans hBQ
  have hQD : Q ≤ normalizer (T : Set D) :=
    (hf T).unique_maximal Q hTQ hQ
  have hEq : Q = normalizer (T : Set D) := le_antisymm hQD hBQ
  rw [hEq]
  exact hc

private theorem binary_four_borelOvergroupCores :
    BorelOvergroupCores
      (BinaryLinear.GL (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.Vector 4)) := by
  letI : Finite (BinaryLinear.GL
      (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.Vector 4)) :=
    Finite.of_injective (fun g : BinaryLinear.GL
      (CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.Vector 4) =>
      (g : _ → _)) DFunLike.coe_injective
  apply borelOvergroupCores_of_standard Four.standardSylow
  intro Q hBQ hQ
  have hB : Four.standardBorel ≤ Q := by
    simpa only [Four.standardSylow_coe] using
      (Four.standardSylow.le_normalizer.trans hBQ)
  obtain ⟨cuts, hcuts⟩ := Four.standard_overgroups_of_bruhat
    Four.hasBruhatDecomposition Q hB
  have hne : cuts.Nonempty := by
    by_contra h
    have hzero : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hcuts, hzero] at hQ
    simp [cutStabilizer] at hQ
  obtain ⟨i, hi⟩ := hne
  let W := cutSpace Four.standardBasis i
  have hQP : Q ≤ BinaryLinear.parabolic W := by
    rw [hcuts]
    intro x hx v
    exact (mem_cutStabilizer Four.standardBasis cuts x).mp hx i hi v
  have hTQ : (Four.standardSylow : Subgroup _) ≤ Q :=
    Four.standardSylow.le_normalizer.trans hBQ
  have hW0 : W ≠ ⊥ := by
    intro hzero
    have hb := (basis_mem_cutSpace Four.standardBasis i 0).mpr
      (Nat.zero_le _)
    have hbW : Four.standardBasis 0 ∈ W := by
      change Four.standardBasis 0 ∈ cutSpace Four.standardBasis i
      exact hb
    rw [hzero, Submodule.mem_bot] at hbW
    exact (LinearIndependent.ne_zero 0 Four.standardBasis.linearIndependent) hbW
  have hWt : W ≠ ⊤ := by
    intro htop
    let j : Fin 4 := ⟨i.val + 1, by omega⟩
    have hbW : Four.standardBasis j ∈ W := by
      rw [htop]
      exact Submodule.mem_top
    have hbcut : Four.standardBasis j ∈ cutSpace Four.standardBasis i := by
      simpa only [W] using hbW
    have hb := (basis_mem_cutSpace Four.standardBasis i j).mp hbcut
    change i.val + 1 ≤ i.val at hb
    omega
  exact core_of_sylow_overgroup_le Four.standardSylow Q (BinaryLinear.parabolic W)
    hTQ hQP (BinaryLinear.centralizer_parabolic_twoCore_le hW0 hWt)

private theorem binary_five_borelOvergroupCores :
    BorelOvergroupCores (BinaryLinear.OuterCyclic.LinearGroup 5) := by
  letI : Finite (BinaryLinear.OuterCyclic.LinearGroup 5) :=
    Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup 5 =>
      (g : _ → _)) DFunLike.coe_injective
  apply borelOvergroupCores_of_standard
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow
  intro Q hBQ hQ
  have hB : BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardBorel ≤ Q := by
    simpa only [BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow_coe] using
      (BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow.le_normalizer.trans hBQ)
  obtain ⟨cuts, hcuts⟩ :=
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.standard_overgroups_of_bruhat
      BinaryLinear.FiveFlagGeometry.SylowOvergroups.hasBruhatDecomposition Q hB
  have hne : cuts.Nonempty := by
    by_contra h
    have hzero : cuts = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hcuts, hzero, BinaryLinear.FiveFlagGeometry.flagStabilizer_empty] at hQ
    exact (lt_irrefl _ hQ)
  obtain ⟨i, hi⟩ := hne
  let W := BinaryLinear.FiveFlagGeometry.flagSpace
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardBasis i
  have hQP : Q ≤ BinaryLinear.parabolic W := by
    rw [hcuts]
    intro x hx v
    exact (BinaryLinear.FiveFlagGeometry.mem_flagStabilizer_iff
      BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardBasis cuts x).mp hx i hi v
  have hTQ : (BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow : Subgroup _) ≤ Q :=
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow.le_normalizer.trans hBQ
  exact core_of_sylow_overgroup_le
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow Q
    (BinaryLinear.parabolic W) hTQ hQP
    (BinaryLinear.centralizer_parabolic_twoCore_le
      (BinaryLinear.FiveFlagGeometry.flagSpace_ne_bot _ _)
      (BinaryLinear.FiveFlagGeometry.flagSpace_ne_top _ _))

private theorem small_binary_borelOvergroupCores {D : Type*} [Group D] [Finite D]
    (h : SmallBinaryModel D) : BorelOvergroupCores D := by
  obtain ⟨n, hn, ⟨e⟩⟩ := BinaryRecognition.smallBinaryModel_linear h
  rcases hn with rfl | rfl
  · exact borelOvergroupCores_of_mulEquiv e binary_four_borelOvergroupCores
  · exact borelOvergroupCores_of_mulEquiv e binary_five_borelOvergroupCores

private theorem rank_one_model_borelOvergroupCores {D : Type*} [Group D] [Finite D]
    [IsSimpleGroup D] (hna : ¬ IsMulCommutative D)
    (h : IsBenderModel D) : BorelOvergroupCores D := by
  rcases h with ⟨f, hf, hm0⟩ | ⟨f, hf, hm0⟩ | ⟨m, hm0, iso⟩
  · have hm := hm0
    obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hm
    have he : IsEvenCharacteristic D := MainConverse.psl2_evenCharacteristic
      hna hf hm0
    have hf : ∀ T : Sylow 2 D, RankOneSylowFacts T := by
      intro T
      apply rankOneSylowFacts_of_equiv T e
      exact rankOneSylowFacts_psl2 F _ (by omega) hcard _
    exact rank_one_borelOvergroupCores D hna he hf

  · have hm := hm0
    obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
    have he : IsEvenCharacteristic D := MainConverse.psu3_evenCharacteristic
      hna hf hm0
    have hf : ∀ T : Sylow 2 D, RankOneSylowFacts T := by
      intro T
      apply rankOneSylowFacts_of_equiv T e
      exact rankOneSylowFacts_psu3 J _ (by omega) hcard hconj _
    exact rank_one_borelOvergroupCores D hna he hf
  · obtain ⟨e⟩ := iso
    have he : IsEvenCharacteristic D :=
      MainConverse.suzuki_evenCharacteristic_of_iso hm0 e
    have hf : ∀ T : Sylow 2 D, RankOneSylowFacts T := by
      intro T
      apply rankOneSylowFacts_of_equiv T e
      exact suzuki_rankOneSylowFacts m _
    exact rank_one_borelOvergroupCores D hna he hf

private theorem centralizer_pCore_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (hc : centralizer (pCore 2 A : Set A) ≤ pCore 2 A) :
    centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
  (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hc

private theorem a6_borelOvergroupCores :
    BorelOvergroupCores (alternatingGroup (Fin 6)) := by
  apply borelOvergroupCores_of_standard a6BorelSylow
  intro Q hBQ hQ
  have hTQ : (a6BorelSylow : Subgroup A6) ≤ Q :=
    a6BorelSylow.le_normalizer.trans hBQ
  obtain htop | ⟨H, hH, hQH⟩ := IsCoatomic.eq_top_or_exists_le_coatom Q
  · exact ((ne_of_lt hQ) htop).elim
  obtain ⟨g, _, hclass⟩ := a6_coatoms_over_sylow a6BorelSylow
  rcases (hclass H).mp ⟨hH, hTQ.trans hQH⟩ with rfl | rfl
  · have hc0 : centralizer (pCore 2 a6DuadStabilizer : Set a6DuadStabilizer) ≤
        pCore 2 a6DuadStabilizer := (le_of_eq a6DuadCore_centralizer)
    exact core_of_sylow_overgroup_le a6BorelSylow Q
      ((MulAut.conj g).mapSubgroup a6DuadStabilizer) hTQ hQH
      (centralizer_pCore_of_mulEquiv ((MulAut.conj g).subgroupMap a6DuadStabilizer) hc0)
  · have hcD : centralizer (pCore 2 a6DuadStabilizer : Set a6DuadStabilizer) ≤
        pCore 2 a6DuadStabilizer := le_of_eq a6DuadCore_centralizer
    let e : a6SynthemeStabilizer ≃* a6DuadStabilizer :=
      ResidualPairRecognition.ComponentLocals.edgeEquiv.symm.trans a6DuadModelEquiv
    have hcS : centralizer (pCore 2 a6SynthemeStabilizer : Set a6SynthemeStabilizer) ≤
        pCore 2 a6SynthemeStabilizer :=
      centralizer_pCore_of_mulEquiv e.symm hcD
    exact core_of_sylow_overgroup_le a6BorelSylow Q
      ((MulAut.conj g).mapSubgroup a6SynthemeStabilizer) hTQ hQH
      (centralizer_pCore_of_mulEquiv ((MulAut.conj g).subgroupMap a6SynthemeStabilizer) hcS)

private theorem tits_atlas_borelOvergroupCores :
    BorelOvergroupCores Tits.Atlas1600Group := by
  apply borelOvergroupCores_of_standard Tits.atlas1600SylowTwo
  intro Q hBQ hQ
  have hS : Tits.atlas1600SylowTwoSubgroup ≤ Q := by
    simpa only [Tits.atlas1600SylowTwo_coe] using
      (Tits.atlas1600SylowTwo.le_normalizer.trans hBQ)
  obtain hfirst | hsecond := Tits.ConverseLocalCoverage.le_first_or_second Q
    (ne_of_lt hQ) hS
  · exact core_of_sylow_overgroup_le Tits.atlas1600SylowTwo Q
      Tits.ExceptionalParabolics.first
      (Tits.atlas1600SylowTwo.le_normalizer.trans hBQ) hfirst
      (Tits.ConverseLocalCores.first_core_self_centralizing)
  · exact core_of_sylow_overgroup_le Tits.atlas1600SylowTwo Q
      Tits.ExceptionalParabolics.second
      (Tits.atlas1600SylowTwo.le_normalizer.trans hBQ) hsecond
      (Tits.ConverseLocalCores.second_core_self_centralizing)

private theorem tits_borelOvergroupCores {D : Type*} [Group D] [Finite D]
    (e : D ≃* Tits.ParrottGroup) : BorelOvergroupCores D :=
  borelOvergroupCores_of_mulEquiv (e.trans Tits.parrottFiniteImageEquiv)
    tits_atlas_borelOvergroupCores

private theorem normal_core_ne_bot {X : Type*} [Group X] [Finite X]
    (hfit : generalizedFitting X = pCore 2 X)
    (H : Subgroup X) [H.Normal] (Y : Subgroup H) [Y.Normal]
    [Group.IsSolvable Y] (hne : Y ≠ ⊥) : pCore 2 H ≠ ⊥ := by
  have hmap : (fittingSubgroup H).map H.subtype ≤ pCore 2 X := by
    rw [← hfit]
    apply le_trans _ (fitting_le_generalizedFitting X)
    exact le_sSup ⟨fittingSubgroupOf_normal H inferInstance,
      fittingSubgroupOf_isNilpotent H⟩
  have hp : IsPGroup 2 (fittingSubgroup H) :=
    (pCore_isPGroup.to_le hmap).of_equiv
      ((fittingSubgroup H).equivMapOfInjective H.subtype H.subtype_injective).symm
  have hfcore : fittingSubgroup H ≤ pCore 2 H := le_sSup ⟨inferInstance, hp⟩
  have hYF : (fittingSubgroup Y).map Y.subtype ≤ fittingSubgroup H :=
    le_sSup ⟨fittingSubgroupOf_normal Y inferInstance,
      fittingSubgroupOf_isNilpotent Y⟩
  intro he
  have hzero : fittingSubgroup Y = ⊥ := by
    apply ((fittingSubgroup Y).map_eq_bot_iff_of_injective Y.subtype_injective).mp
    exact le_bot_iff.mp (he ▸ hYF.trans hfcore)
  exact hne (Y.card_eq_one.mp
    ((fitting_eq_bot_iff_card_eq_one_of_solvable Y).mp hzero))

private theorem local_core_witness {X : Type*} [Group X] [Finite X]
    (D N Y T : Subgroup X) [D.Normal]
    (c : LocalConfiguration D N Y T) (hgen : D ⊔ T = ⊤) :
    9 ∣ Nat.card (N.subgroupOf D) ∧ pCore 2 (N.subgroupOf D) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := c.sylow
  have ht : IsPGroup 2 T := hP ▸ P.isPGroup'
  have h36 := BinaryRecognition.InnerGeometry.shadow_card_dvd c.shadow
  have hYne : Y ≠ ⊥ := by
    intro he
    rw [he, bot_sup_eq] at h36
    obtain ⟨k, hk⟩ := ht.exists_card_eq
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by decide : 3 ∣ 36).trans h36
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)
  let E := N ⊓ D
  let H := D.subgroupOf N
  let eH : H ≃* E :=
    (MulEquiv.subgroupCongr (inf_subgroupOf_left D N).symm).trans
      (subgroupOfEquivOfLe (show E ≤ N from inf_le_left))
  let eD : E ≃* N.subgroupOf D :=
    (subgroupOfEquivOfLe (show E ≤ D from inf_le_right)).symm.trans
      (MulEquiv.subgroupCongr (inf_subgroupOf_right N D))
  let J := (Y.subgroupOf E).map eH.symm.toMonoidHom
  let : (Y.subgroupOf E).Normal := c.yplus_normal
  let : J.Normal := Subgroup.Normal.map inferInstance _ eH.symm.surjective
  let : Group.IsSolvable (Y ⊔ T : Subgroup X) :=
    BinaryRecognition.InnerGeometry.shadow_join_solvable c.shadow
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show Y ≤ Y ⊔ T from le_sup_left)) (inclusion_injective _)
  let : Group.IsSolvable (Y.subgroupOf E) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe c.yplus_le).toMonoidHom)
      (subgroupOfEquivOfLe c.yplus_le).injective
  let : Group.IsSolvable J := Group.isSolvable_of_surjective
    (eH.symm.toMonoidHom.subgroupMap_surjective (Y.subgroupOf E))
  have hJ : J ≠ ⊥ := by
    intro he
    have heY : Y.subgroupOf E = ⊥ :=
      ((Y.subgroupOf E).map_eq_bot_iff_of_injective eH.symm.injective).mp he
    apply hYne
    have hemap := congrArg (Subgroup.map E.subtype) heY
    rwa [map_subgroupOf_eq_of_le c.yplus_le, Subgroup.map_bot] at hemap
  have hcore : pCore 2 H ≠ ⊥ := normal_core_ne_bot c.characteristicTwo H J hJ
  have h9N : 9 ∣ Nat.card N := (by decide : 9 ∣ 36).trans
    (h36.trans (card_dvd_of_le (sup_le (c.yplus_le.trans inf_le_left) c.sylow_le)))
  obtain ⟨k, hk⟩ := (isPGroup_quotient_of_sup_eq_top D T ht hgen).exists_card_eq
  have hi : D.index = 2 ^ k := hk
  have hcop : Nat.Coprime 9 H.index :=
    ((by decide : Nat.Coprime 9 2).pow_right k).of_dvd_right
      (hi ▸ D.relIndex_dvd_index_of_normal N)
  have h9H : 9 ∣ Nat.card H := hcop.dvd_mul_left.mp (H.index_mul_card.symm ▸ h9N)
  let a := eH.trans eD
  constructor
  · rwa [← Nat.card_congr a.toEquiv]
  · intro he
    apply hcore
    apply ((pCore 2 H).map_eq_bot_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    rw [pCore_map_iso, he]

private theorem g2_no_nine_core
    (H : Subgroup Atlas.G2.BinaryParabolicPair.DerivedModel)
    (hcore : pCore 2 H ≠ ⊥) : ¬ 9 ∣ Nat.card H := by
  let R := (pCore 2 H).map H.subtype
  have hR : R ≠ ⊥ := fun he => hcore
    (((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp he)
  have hHN : H ≤ normalizer (R : Set _) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 H).le_normalizer_map H.subtype
  obtain ⟨g, hg | hg⟩ :=
    Atlas.G2.BinaryParabolicPair.binary_normalizer_conjugate_le R hR
      (pCore_isPGroup.map H.subtype)
  · intro hd
    apply Atlas.G2.BinaryParabolicPair.ThreeObstruction.derived_first_nine_not_dvd
    have hle := (map_mono (f := (MulAut.conj g).toMonoidHom) hHN).trans hg
    have hc := card_dvd_of_le hle
    rw [card_map_of_injective (MulAut.conj g).injective] at hc
    exact hd.trans hc
  · intro hd
    apply Atlas.G2.BinaryParabolicPair.ThreeObstruction.derived_second_nine_not_dvd
    have hle := (map_mono (f := (MulAut.conj g).toMonoidHom) hHN).trans hg
    have hc := card_dvd_of_le hle
    rw [card_map_of_injective (MulAut.conj g).injective] at hc
    exact hd.trans hc

private theorem nine_core_obstruction_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (H : Subgroup A) (h9 : 9 ∣ Nat.card H)
    (hc : pCore 2 H ≠ ⊥)
    (hB : ∀ K : Subgroup B, pCore 2 K ≠ ⊥ → ¬ 9 ∣ Nat.card K) : False := by
  have h9H : 9 ∣ Nat.card (H.map e.toMonoidHom) := by
    rwa [card_map_of_injective e.injective]
  have hcH : pCore 2 (H.map e.toMonoidHom) ≠ ⊥ := by
    intro he
    apply hc
    apply ((pCore 2 H).map_eq_bot_iff_of_injective
      (f := (e.subgroupMap H).toMonoidHom) (e.subgroupMap H).injective).mp
    exact (pCore_map_iso 2 (e.subgroupMap H)).trans he
  exact hB (H.map e.toMonoidHom) hcH h9H

private theorem not_g2_derived (d : Setup L MI Yplus S)
    (e : centralizerQuotientComponent L ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let N := MI.map q
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨h9, hc⟩ := local_core_witness D N (Yplus.map q) (S.map q)
    d.quotient_local d.quotient_generated
  exact nine_core_obstruction_of_equiv e (N.subgroupOf D) h9 hc g2_no_nine_core

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.Recognition

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open Recognition

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

/-- Every proper invariant Borel overgroup in the actual centralizer quotient
has self-centralizing intrinsic two-core. Only the larger-field symplectic
and split G₂ producers remain explicit; all other action-catalogue branches
are discharged on their actual model carriers. -/
theorem quotient_parabolic_cores_of_split_core_producers
    (d : Setup L MI Yplus S) {z : G} {α : MulAut L}
    (a : SourceAction L S z α)
    (hsp : ∀ n : ℕ, 1 < n →
      ClassicalGroup.IsPSp (centralizerQuotientComponent L) 2 (2 ^ n) →
      BorelOvergroupCores (centralizerQuotientComponent L))
    (hg2 : ∀ n : ℕ, 1 < n →
      ClassificationModels.IsG2At (centralizerQuotientComponent L) (2 ^ n) →
      BorelOvergroupCores (centralizerQuotientComponent L)) :
    ∀ Q : Subgroup (CentralizerQuotient L),
      sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L)) ≤ Q →
      Q < centralizerQuotientComponent L →
      S.map (centralizerQuotientMap L) ≤ normalizer (Q : Set (CentralizerQuotient L)) →
      centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q := by
  let := d.quasisimple
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : IsSimpleGroup D := centralizerQuotientComponent_simple L
  let : IsQuasisimple D := IsQuasisimple.of_surjective (q.subgroupMap L)
    (q.subgroupMap_surjective L)
  have hna : ¬ IsMulCommutative D := Group.IsPerfect.not_isMulCommutative D
  apply core_of_catalogue_covers D (S.map q) _ d.quotient_component_sylow
  rcases component_model_cases L a.alternatives with hsmall | hlarge | hex
  · exact small_binary_borelOvergroupCores hsmall
  · cases hlarge with
    | linear n hn hm => exact linearThree_borelOvergroupCores hn hm
    | symplectic n hn hm => exact hsp n hn hm
    | g2 n hn hm => exact hg2 n hn hm
    | triality n _ hm => exact triality_borelOvergroupCores hm
    | ree m hm model =>
      obtain ⟨r, ⟨e⟩⟩ := model
      exact borelOvergroupCores_of_mulEquiv (e.trans r.modelEquiv)
        (ree_borelOvergroupCores m hm)
  · cases hex with
    | rank_one hm => exact rank_one_model_borelOvergroupCores hna hm
    | linear_three_two hm => exact (d.not_linear_three_two hm).elim
    | triality_two hm =>
      exact triality_borelOvergroupCores (n := 1) (by simpa only [pow_one] using hm)
    | symplectic_derived hm =>
      obtain ⟨e⟩ := hm
      exact borelOvergroupCores_of_mulEquiv
        (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
        a6_borelOvergroupCores
    | g2_derived hm =>
      obtain ⟨e⟩ := hm
      exact (not_g2_derived d e).elim
    | tits hm =>
      obtain ⟨e⟩ := hm
      exact tits_borelOvergroupCores e
    | alternating_six hm =>
      obtain ⟨e⟩ := hm
      exact borelOvergroupCores_of_mulEquiv e a6_borelOvergroupCores

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
