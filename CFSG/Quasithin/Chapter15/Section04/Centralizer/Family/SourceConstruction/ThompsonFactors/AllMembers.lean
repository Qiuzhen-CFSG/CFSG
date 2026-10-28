module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.AllMembers.Factors
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonFactors.MovedRank
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ThompsonSource

/-!
# Classification of every original Y-family member in a solvable local

Each member equals its commutator with J(T), so its actual star image lies
in the global Thompson image. Two-perfectness and the normal cubic/Sylow
supplement force it into the alternating cubic product. The source
centralizer kernel is O₂(M); thus the image is nontrivial. Its original
T-invariance selects a coordinate cubic or the full product, and proves
normality in the same quotient.

Transport through the marked M/O₂(M) comparison proves relative normality
of the original member. Its intrinsic quotient and literal moved group
then give every field of ModuleStructure.Input, with no normality, quotient
shape or moved-rank premise. The B.2.16 application remains the original
earlier source theorem, and noncentrality is supplied by 15.4.11(3).

Source: Aschbacher–Smith 15.4.12, printed pp.1160–1161.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource ModuleStructure
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Every actual source member has a normal coordinate-product image under the literal star map. -/
theorem member_star_classification (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))]
    (d : Exceptional (T.subtype hTM)) (hc : d.count = 1 ∨ d.count = 2)
    (X : Subgroup G) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    ∃ I : Finset (Fin d.count), (I.card = 1 ∨ I.card = 2) ∧
      (X.subgroupOf M).map
        (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))) = cubicProduct d I ∧
      ((X.subgroupOf M).map
        (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM)))).Normal := by
  let S := T.subtype hTM
  let q := starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S)
  let A := X.subgroupOf M
  have hp : IsPPerfect 2 A := (YFamily.perfect hX).of_surjective
    (subgroupOfEquivOfLe hXM).symm.toMonoidHom (subgroupOfEquivOfLe hXM).symm.surjective
  have hJ : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective _ M.subtype_injective]
    change elementaryAbelianMaxJ ((T.subtype hTM : Subgroup M).map M.subtype) = _
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]
  have hj : A = ⁅A,elementaryAbelianMaxJ (S : Subgroup M)⁆ := by
    apply map_injective M.subtype_injective
    rw [map_commutator,hJ]
    change (X.subgroupOf M).map M.subtype = ⁅(X.subgroupOf M).map M.subtype,_⁆
    rw [map_subgroupOf_eq_of_le hXM]
    exact hX.2
  have hle := perfect_commutator_image_le_cubicProduct d hc A hp hj
  have hnA : (S : Subgroup M) ≤ normalizer (A : Set M) := by
    apply le_normalizer_iff.mpr
    intro s hs a ha
    change (s : G)*(a : G)*(s : G)⁻¹ ∈ X
    exact le_normalizer_iff.mp (YFamily.invariant hX) s hs a ha
  have hn : sylowStar (S := S) ≤ normalizer (A.map q : Set (Star (S := S))) :=
    (map_mono hnA).trans (le_normalizer_map q)
  have hker : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk'
      (centralizer (Chapter1.RadicalNormalizers.ThompsonSource.closure S : Set M))).ker
    rw [QuotientGroup.ker_mk']
    change IsPGroup 2 (centralizer
      (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM) : Set M))
    rw [ThompsonSource.star_kernel T M hTM hC]
    exact pCore_isPGroup
  have hne : A.map q ≠ ⊥ := by
    intro he
    have hAK : A ≤ q.ker := by
      intro a ha
      exact mem_bot.mp (he ▸ mem_map_of_mem q ha)
    have hA2 := hker.to_le hAK
    have hbot : (⊥ : Subgroup A) = ⊤ := hp _ inferInstance
      (hA2.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective _))
    have hA : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      exact congrArg Subtype.val (mem_bot.mp
        (show (⟨a,ha⟩ : A) ∈ (⊥ : Subgroup A) from hbot.symm ▸ mem_top _))
    apply YFamily.ne_bot hX
    rw [← map_subgroupOf_eq_of_le hXM]
    change A.map M.subtype = ⊥
    rw [hA,Subgroup.map_bot]
  exact normalized_cubic_subgroup d hc (A.map q) hle hne hn

/-- The same classification and normality use the fixed original M/O₂(M) quotient. -/
theorem member_image_classification (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))]
    (d : Exceptional (T.subtype hTM)) (hc : d.count = 1 ∨ d.count = 2)
    (X : Subgroup G) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    ∃ I : Finset (Fin d.count), (I.card = 1 ∨ I.card = 2) ∧
      image M X = (cubicProduct d I).map (ThompsonSource.coreQuotientEquiv T M hTM hC).toMonoidHom ∧
      (image M X).Normal := by
  obtain ⟨I,hI,he,hn⟩ := member_star_classification T M hTM hC d hc X hX hXM
  let e := ThompsonSource.coreQuotientEquiv T M hTM hC
  have hq : e.toMonoidHom.comp
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))) = quotientMap M := by
    ext m
    exact ThompsonSource.coreQuotientEquiv_apply T M hTM hC m
  have hm : ((X.subgroupOf M).map
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM)))).map e.toMonoidHom = image M X := by
    rw [map_map,hq]
    rfl
  refine ⟨I,hI,?_,?_⟩
  · rw [← hm,he]
  · exact hm ▸ hn.map e.toMonoidHom e.surjective

/-- Every specified family member satisfies the full original source module input. -/
theorem member_input_of_exceptional {κ : GroupClass}
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hsol : Group.IsSolvable M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmoved : ⁅localV T M,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥)
    [IsElementaryAbelian 2 (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))]
    (d : Exceptional (T.subtype hTM)) (hc : d.count = 1 ∨ d.count = 2)
    (X : Subgroup G) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    ∃ s : ℕ, Input κ T M X s := by
  obtain ⟨I,hI,hstar,hnstar⟩ := member_star_classification T M hTM hC d hc X hX hXM
  let e := ThompsonSource.coreQuotientEquiv T M hTM hC
  have hq : e.toMonoidHom.comp
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure (T.subtype hTM))) = quotientMap M := by
    ext m
    exact ThompsonSource.coreQuotientEquiv_apply T M hTM hC m
  have himage : image M X = (cubicProduct d I).map e.toMonoidHom := by
    rw [← hstar,map_map,hq]
    rfl
  have hn : (image M X).Normal := by
    have hR : (cubicProduct d I).Normal := hstar ▸ hnstar
    rw [himage]
    exact hR.map e.toMonoidHom e.surjective
  let hnorm := member_normal_of_image_normal T hTM hX hXM hn
  obtain ⟨f,_⟩ := member_quotient_compatible hXM hnorm
  let : IsElementaryAbelian 3 (cubicProduct d I) := cubicProduct_elementary d I hI
  let : IsElementaryAbelian 3 (image M X) := by
    rw [himage]
    exact IsElementaryAbelian.map e.toMonoidHom
  have hr := actual_moved_rank_map d I hI (X.subgroupOf M) hstar M.subtype M.subtype_injective
  rw [map_subgroupOf_eq_of_le hXM,ThompsonSource.closure_eq_internalModule] at hr
  refine ⟨I.card,⟨hG,hM,hTM,hsol,hC,hmoved,hX,hXM,hnorm,hI,?_,?_,hr⟩⟩
  · exact IsElementaryAbelian.of_surjective f.symm.toMonoidHom f.symm.surjective
  · rw [Nat.card_congr f.toEquiv,himage,card_map_of_injective e.injective]
    exact cubicProduct_card d I hI

/-- The full earlier B.2.16 theorem supplies the original module input for every source member. -/
theorem member_input_of_noncentral {κ : GroupClass}
    (hB : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u})
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hsol : Group.IsSolvable M)
    (hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = T)
    (hmoved : ⁅localV T M,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥)
    (X : Subgroup G) (hX : X ∈ Y (T : Subgroup G)) (hXM : X ≤ M) :
    ∃ s : ℕ, Input κ T M X s := by
  obtain ⟨hE,d,hc⟩ := ThompsonSource.exceptional hB hG T M hM hTM hsol hC hmoved
  let := hE
  exact member_input_of_exceptional hG T M hM hTM hsol hC hmoved d hc X hX hXM

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
