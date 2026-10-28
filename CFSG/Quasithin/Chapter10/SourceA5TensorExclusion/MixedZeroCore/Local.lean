module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponent
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCore
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Borel
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
public import Theory.Alternating.FiveSylowCubicBorel
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The literal mixed pair in the zero-core tensor branch

Write K = O²(H), and suppose the source construction supplies U = Dσ T₂.
Rank-one Sylow uniqueness places K intersect M in the actual K-Borel;
its prescribed cubic B then gives N_K(T intersect K) = (T intersect K)B.
The S₃ quotient identifies the other Borel with T intersect U.

The pair (K,U,T) consequently has common Borel BT, parabolics H and AT,
and generated group H join A. Both characteristic-two clauses follow
from the original Sylow-overgroup intervals in H and L₀T. This verifies
all of corrected F.1.1, including relative normality and the exact core,
without assuming a rank-two recognition conclusion.

The construction of U and the mixed F.1.12 order bound are separate inputs.
The definitions below state only those two local contracts; they do not
assert that either input has been proved.

Source: Aschbacher–Smith, original 9.3.1, printed p.732, and F.1.1,
printed pp.259–260 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
namespace MixedZeroCore
variable {G : Type*} [Group G] [Finite G]

private theorem rankOne_of_a5 {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : ChapterF.Source.IsRankOneModel X := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact .linear 2 (by decide) ⟨GaloisField 2 2, inferInstance, inferInstance,
    by simpa using hc, ⟨e.trans f.symm⟩⟩

private theorem rankOne_of_s3 {X : Type*} [Group X]
    (e : X ≃* Equiv.Perm (Fin 3)) : ChapterF.Source.IsRankOneModel X := by
  apply ChapterF.Source.IsRankOneModel.linear 1 (by decide)
  refine ⟨ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
  exact ⟨e.trans (SLTwoPermThree.sl2Two_equiv_perm_three.some.symm.trans
    (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))⟩

/-- The local output of the source construction U = Dσ T₂. -/
@[expose] def CubicFactor (T : Sylow 2 G) (A B U : Subgroup G) : Prop :=
  U ≤ A ⊔ (T : Subgroup G) ∧
  (T : Subgroup G) ≤ normalizer (U : Set G) ∧
  B ≤ normalizer (U : Set G) ∧ A ≤ B ⊔ U ∧
  Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))

/-- The mixed specialization of F.1.12 needed by the original tensor source.
The original common subgroup is also Sylow in the generated group. -/
@[expose] def MixedSizeInput (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (K U S : Subgroup G),
    ChapterF.Source.HypothesisF11 ![K,U] S →
    IsQuasithin (ChapterF.Source.generated ![K,U] S) →
    Chapter1.IsSylowIn 2 S (ChapterF.Source.generated ![K,U] S) →
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
    Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) →
    ChapterF.Source.borel U S ≤ normalizer (S : Set G) → Nat.card S ≤ 256

private theorem sylow_intersection (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  exact ⟨P, by rw [hP, subgroupOf_map_subtype]⟩

end MixedZeroCore

namespace SourceA5TensorModel
open MixedZeroCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- Every subgroup of the residual lying in the original maximal local lies in its literal Borel. -/
theorem old_residual_cubic_le_borel
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (B : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBM : B ≤ D.maximalLocal) :
    B ≤ ChapterF.Source.borel ((pResidual 2 H).map H.subtype) (T : Subgroup G) := by
  let K := (pResidual 2 H).map H.subtype
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H)
  obtain ⟨P,hP⟩ := MixedZeroCore.sylow_intersection T K hTK
  have hP' : (P : Subgroup K) = ((T : Subgroup G) ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le inf_le_right]
  have hproper : D.maximalLocal.subgroupOf K < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    exact source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH
      (subgroupOf_eq_top.mp he)
  have hPN : D.maximalLocal.subgroupOf K ≤ normalizer (P : Set K) :=
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient
      (MixedZeroCore.rankOne_of_a5 eK) P).unique_maximal _
        (by intro x hx; exact le_normalizer_componentOrbit L T ((hP ▸ mem_map_of_mem K.subtype hx).1))
        hproper
  have hn : (normalizer (P : Set K)).map K.subtype = ChapterF.Source.borel K (T : Subgroup G) := by
    change (normalizer ((P : Subgroup K) : Set K)).map K.subtype = _
    rw [hP', ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ K ≤ K from inf_le_right),
      subgroupOf_map_subtype]
    exact inf_comm _ _
  intro b hb
  rw [← hn]
  exact mem_map.mpr ⟨⟨b,hBK hb⟩,hPN (hBM hb),rfl⟩

/-- The source Borel is exactly the residual Sylow part times the prescribed cubic. -/
theorem old_residual_borel_eq_cubic_sup
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (B : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBM : B ≤ D.maximalLocal) (hB3 : Nat.card B = 3) :
    ChapterF.Source.borel ((pResidual 2 H).map H.subtype) (T : Subgroup G) =
      ((T : Subgroup G) ⊓ (pResidual 2 H).map H.subtype) ⊔ B := by
  let K := (pResidual 2 H).map H.subtype
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H)
  obtain ⟨P,hP⟩ := MixedZeroCore.sylow_intersection T K hTK
  have hP' : (P : Subgroup K) = ((T : Subgroup G) ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le inf_le_right]
  have hB := old_residual_cubic_le_borel hH eK B hBK hBM
  have hBN : B.subgroupOf K ≤ normalizer (P : Set K) := by
    change B.subgroupOf K ≤ normalizer ((P : Subgroup K) : Set K)
    rw [hP', ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ K ≤ K from inf_le_right)]
    exact fun _ hx => (hB hx).2
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    ext x
    change eK (QuotientGroup.mk' (pCore 2 K) x) = 1 ↔ x ∈ pCore 2 K
    rw [eK.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have he := Theory.AlternatingFive.sylow_normalizer_eq_sup_cubic_of_two_kernel
    q (eK.surjective.comp (QuotientGroup.mk'_surjective _))
    (hk ▸ pCore_isPGroup) P (B.subgroupOf K)
    ((Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).trans hB3) hBN
  have hm := congrArg (map K.subtype) he
  rw [Subgroup.map_sup, hP, map_subgroupOf_eq_of_le hBK] at hm
  have hn : (normalizer (P : Set K)).map K.subtype = ChapterF.Source.borel K (T : Subgroup G) := by
    change (normalizer ((P : Subgroup K) : Set K)).map K.subtype = _
    rw [hP', ← subgroupOf_normalizer_eq (show (T : Subgroup G) ⊓ K ≤ K from inf_le_right),
      subgroupOf_map_subtype]
    exact inf_comm _ _
  exact hn.symm.trans hm

/-- The mixed pair generates precisely the original Cartan overgroup. -/
theorem mixed_cubic_factor_generated
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (A B U : Subgroup G) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hU : CubicFactor T A B U) :
    ChapterF.Source.generated ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) = H ⊔ A := by
  let K := (pResidual 2 H).map H.subtype
  change (K ⊔ U) ⊔ (T : Subgroup G) = H ⊔ A
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hKH : K ≤ H := map_subtype_le _
  have hHgen : K ⊔ (T : Subgroup G) = H := source_hstar_residual_sup_sylow hH
  apply le_antisymm
  · exact sup_le (sup_le (hKH.trans le_sup_left)
      (hU.1.trans (sup_le le_sup_right (hTH.trans le_sup_left))))
      (hTH.trans le_sup_left)
  · refine sup_le ?_ ?_
    · rw [← hHgen]
      exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    · exact hU.2.2.2.1.trans (sup_le (hBK.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left))

/-- Construct every F.1.1 clause on the original residual, cubic factor and T.
The only extra local input is the construction of Dσ T₂. -/
theorem mixed_cubic_factor_rank_two
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    ChapterF.Source.HypothesisF11 ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) ∧
    IsQuasithin (ChapterF.Source.generated ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ∧
    Chapter1.IsSylowIn 2 (T : Subgroup G)
      (ChapterF.Source.generated ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ∧
    ChapterF.Source.borel U (T : Subgroup G) = (T : Subgroup G) ⊓ U ∧
    ChapterF.Source.commonBorel ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) =
      B ⊔ (T : Subgroup G) ∧
    ChapterF.Source.parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 0 = H ∧
    ChapterF.Source.parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 1 =
      A ⊔ (T : Subgroup G) := by
  let K := (pResidual 2 H).map H.subtype
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H)
  obtain ⟨P,hP⟩ := MixedZeroCore.sylow_intersection T K hTK
  obtain ⟨R,hR⟩ := MixedZeroCore.sylow_intersection T U hU.2.1
  obtain ⟨eU⟩ := hU.2.2.2.2
  have hUB : ChapterF.Source.borel U (T : Subgroup G) = (T : Subgroup G) ⊓ U := by
    simpa only [ChapterF.Source.borel, inf_assoc, inf_idem] using
      ChapterF.Source.borel_eq_of_cubic_local_sylow U ((T : Subgroup G) ⊓ U) ⟨R,hR⟩ eU
  have hAL : A ≤ localOrbit T L := hAB.trans ((map_subtype_le _).trans inf_le_left)
  have hBM : B ≤ D.maximalLocal := hBA.trans (hAL.trans (localOrbit T L).le_normalizer)
  have hKB := old_residual_borel_eq_cubic_sup hH eK B hBK hBM hB3
  have hleft : ChapterF.Source.parabolic ![K,U] (T : Subgroup G) 0 = H := by
    change K ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel U (T : Subgroup G) = H
    rw [hUB, sup_eq_left.mpr (inf_le_left.trans le_sup_right)]
    exact source_hstar_residual_sup_sylow hH
  have hright : ChapterF.Source.parabolic ![K,U] (T : Subgroup G) 1 =
      A ⊔ (T : Subgroup G) := by
    change U ⊔ (T : Subgroup G) ⊔ ChapterF.Source.borel K (T : Subgroup G) = _
    rw [hKB]
    apply le_antisymm
    · exact sup_le (sup_le hU.1 le_sup_right)
        (sup_le (inf_le_left.trans le_sup_right) (hBA.trans le_sup_left))
    · exact sup_le (hU.2.2.2.1.trans
        (sup_le (le_sup_right.trans le_sup_right) (le_sup_left.trans le_sup_left)))
        (le_sup_right.trans le_sup_left)
  have hchar : ∀ i : Fin 2,
      generalizedFitting (ChapterF.Source.parabolic ![K,U] (T : Subgroup G) i) =
        pCore 2 (ChapterF.Source.parabolic ![K,U] (T : Subgroup G) i) := by
    intro i
    fin_cases i
    · exact generalizedFitting_eq_pCore_of_sylow_overgroup T _ H
        (le_sup_right.trans le_sup_left) hleft.le
        (Chapter1.mem_He_iff.mp
          (Chapter1.lemma_1_1_4_6 T (D.simpleQTKE.evenCharacteristic T) hH.1.1))
    · exact generalizedFitting_eq_pCore_of_sylow_overgroup T _ (localJoin T L)
        (le_sup_right.trans le_sup_left)
        (hright.le.trans (sup_le (hAL.trans le_sup_left) le_sup_right))
        (Chapter1.mem_He_iff.mp (localJoin_mem_He D))
  have hF : ChapterF.Source.HypothesisF11 ![K,U] (T : Subgroup G) := by
    refine ⟨inferInstance,T.isPGroup',?_,?_,?_,?_,?_,hchar⟩
    · intro i
      fin_cases i
      · exact hTK
      · exact hU.2.1
    · intro i
      fin_cases i
      · exact ⟨P,hP⟩
      · exact ⟨R,hR⟩
    · intro i
      fin_cases i
      · exact MixedZeroCore.rankOne_of_a5 eK
      · exact MixedZeroCore.rankOne_of_s3 eU
    · intro i
      fin_cases i
      · change ChapterF.Source.borel U (T : Subgroup G) ≤ normalizer (K : Set G)
        exact (hUB ▸ inf_le_left).trans hTK
      · change ChapterF.Source.borel K (T : Subgroup G) ≤ normalizer (U : Set G)
        rw [hKB]
        exact sup_le (inf_le_left.trans hU.2.1) hU.2.2.1
    · rw [mixed_cubic_factor_generated hH A B U hBK hU]
      exact hzero
  refine ⟨hF,D.simpleQTKE.quasithin.subgroup _,?_,hUB,?_,hleft,hright⟩
  · have ht : (T : Subgroup G) ≤ ChapterF.Source.generated ![K,U] (T : Subgroup G) := le_sup_right
    exact ⟨T.subtype ht,map_subgroupOf_eq_of_le ht⟩
  · change (ChapterF.Source.borel K (T : Subgroup G) ⊔
      ChapterF.Source.borel U (T : Subgroup G)) ⊔ (T : Subgroup G) = B ⊔ (T : Subgroup G)
    rw [hKB,hUB]
    apply le_antisymm
    · exact sup_le (sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left)
        (inf_le_left.trans le_sup_right)) le_sup_right
    · exact sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left)) le_sup_right

end SourceA5TensorModel
end CFSG.Quasithin.Chapter10
