module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Normalizer
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ChosenStars.Signalizers.Lift

/-!
# Canonical stars and maximal-local radical centralization

The all-prime normalizer bound first controls N_G(R), where
R = O₂(Ξ_p(L)T). An escaping characteristic normalizer has a relatively
normal (S)L₃(p) component containing the actual defining plane.
The completed two-signalizer calculation gives R = O₂(KR), forcing
K ≤ N_G(R) ≤ N_G(L), contrary to canonical-radical rigidity.
This proves the full characteristic-normalizer bound and hence starred
membership. The primary-radical argument then centralizes the literal
reduced subgroup, retaining its ambient inclusion map.

All local callbacks, including the multiple-prime case, are discharged.
The original simple QTKE and maximal-component hypotheses suffice; no
stronger Chapter 13 ambient hypothesis is used.
Source: Aschbacher--Smith, 1.3.8, pp.512--514, and 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers Chapter1.RadicalActions
open Chapter1.RadicalNormalizers.Embedding Chapter1.XiEmbedding Chapter1.RadicalExclusions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every nontrivial characteristic normalizer of the canonical two-core is
controlled by the original maximal local normalizer. -/
theorem characteristicNormalizerClosure_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    (radicalCore p L T).characteristicNormalizerClosure ≤ normalizer (L : Set G) := by
  classical
  let h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have h38 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ → ∀ B : Subgroup A,
      B.IsCComponent → B.Normal ∨ IsQuasisimple B :=
    fun _ _ _ hA hO _ hB => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hA hO hB
  have hQ := uniqueness_local_quotient_sqtk hG hL.1.2.2
  have hr := residual_normalizer_data_of_source h36 h38 hL hQ hn hp hd
  obtain ⟨hp3,hshape⟩ := XiP_oddQuotient_of_A36 h36 hL.1 hQ hn hp hd
  have hX := (Chapter13.Section01.XiP_mem_XiPlus_source hG T hL.1 hn hp hd).1
  obtain ⟨_,hM,_⟩ := Chapter13.Section01.RadicalConjugateRigidity.maximal_radical_structure
    hG T hL hn hp hd
  have hRM := radicalCore_normalizer_le hG T hL hn hp hd
  apply (characteristicNormalizerClosure_le_iff _ _).mpr
  intro C hchar hne
  let := hchar
  by_contra he
  obtain ⟨K,hK,hYK,hKn,hTK⟩ := exists_normal_component_source hG T hL hn hp hd C hne
  have hTN := (t_le_normalizer_radicalCore p L T).trans
    (normalizer_le_normalizer_characteristic_image _ C)
  let P : Sylow p (XiP p L) := default
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  obtain ⟨⟨eP⟩,hm⟩ := escaping_component_shape hG T hL hn hp hd
    (characteristic_normalizer_isTwoLocal p L T C hne) hTN hK hKn (hr.X_le_Y.trans hYK) he P
  have hcard : Nat.card P₀ = p ^ 2 := by
    rw [Nat.card_congr eP.toEquiv]
    change Nat.card (Fin 2 → ZMod p) = p ^ 2
    rw [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
  have hRcore : radicalCore p L T ≤ (K ⊔ radicalCore p L T).pCoreIn 2 :=
    radical_le_join_core_of_linearThree hp3 K (radicalCore p L T) _ P₀ hK hKn
      ((radicalCore p L T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ C))
      (radicalCore_isTwoGroup p L T) ((map_subtype_le _).trans (hr.X_le_Y.trans hYK))
      (P.isPGroup'.map _) hcard
      ((map_subtype_le _).trans (le_sup_left.trans (join_le_normalizer_radicalCore p L T))) hm
  have heq : radicalCore p L T = (K ⊔ radicalCore p L T).pCoreIn 2 :=
    le_antisymm hRcore (twoCore_join_le_radicalCore p L K T hTK (hr.X_le_Y.trans hYK))
  have hKR : K ≤ normalizer (radicalCore p L T : Set G) := by
    rw [heq]
    exact le_sup_left.trans ((K ⊔ radicalCore p L T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hnot := (escaping_component_rigidity hG h36 hp3 L T hX hshape C hne K
    hK hKn hTK hr.X_le_Y hYK hM.symm he).1
  exact hnot (normal_subgroupOf_of_le_normalizer
    ((hKR.trans hRM).trans (normalizer_le_normalizer_XiP p L)))

/-- Canonical radicals are starred in the original ambient hypotheses,
with arbitrary odd-prime Fitting support. -/
theorem XiP_mem_XiStar
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    XiP p L ∈ XiStar G (T : Subgroup G) :=
  XiP_mem_XiStar_of_characteristic_control hG T hL hn hp hd
    (characteristicNormalizerClosure_le hG T hL hn hp hd)

/-- The entire family of canonical starred radicals, without local callbacks. -/
theorem canonicalRadicalsStarred
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) : CanonicalRadicalsStarred T L :=
  fun _ _ hp hd => XiP_mem_XiStar hG T hL hn hp hd

/-- The maximal-local specialization of source 3.2.14 in every normal overgroup,
retaining its ambient inclusion map and with canonical stars discharged. -/
theorem maximal_solvableRadical_centralizes_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (J : Subgroup G) (hLJ : L ≤ J) (hJn : J ≤ normalizer (L : Set G)) :
    (solvableRadical L).map L.subtype ≤
      centralizer ((reducedTwoSubgroup J).map J.subtype : Set G) :=
  maximal_solvableRadical_centralizes_reduced_of_stars hG T hmany hL hn
    (canonicalRadicalsStarred hG T hL hn) J hLJ hJn

/-- The literal JT specialization consumed by the original 11.4.2 comparison. -/
theorem maximal_solvableRadical_centralizes_sylowJoin
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {J : Subgroup G} (hJ : J ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient J)) :
    (solvableRadical J).map J.subtype ≤
      centralizer ((reducedTwoSubgroup (J ⊔ (T : Subgroup G) : Subgroup G)).map
        (J ⊔ (T : Subgroup G)).subtype : Set G) :=
  maximal_solvableRadical_centralizes_sylowJoin_of_stars hG T hmany hJ hn
    (canonicalRadicalsStarred hG T hJ hn)
end CFSG.Quasithin.Chapter3.RadicalCentralization.ChosenStars
