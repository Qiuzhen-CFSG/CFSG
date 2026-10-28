module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.CanonicalRadicalComplete
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.MovedWeakClosure
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.NormalizerAction
public import CFSG.Quasithin.Chapter13.Section01.RadicalQuotient

/-!
# Original radical centralization and the normalizer action

Both possible active odd-primary radicals are excluded: exponent-p radicals
are canonical radicals, while the higher homocyclic case has already been
eliminated. The primary residuals detect the action of the entire solvable
radical on R₂(N_G(L)). This proves the literal 13.1.4(5) centralization.

For a faithful maximal local component the resulting action kernel is
exactly its solvable radical, giving the original PSL₂(p) action of 13.1.8.
The final application removes radical centralization from the moved-module
weak-closure theorem; the original TI input remains explicit.

Source: Aschbacher--Smith 13.1.4(5),13.1.8, pp.867--869;
13.1.14, pp.875--876.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter3.RadicalCentralization
open ChapterA.Section04 ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Neither possible odd-primary radical can have nonzero intrinsic action. -/
theorem primary_radical_intrinsicModule_eq_bot
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    intrinsicSignalizerModule (primaryRadical p L) = ⊥ := by
  by_contra hi
  let I := primaryRadical p L
  by_cases he : ∀ x : I ⧸ pCore 2 I, x ^ p = 1
  · have hle := primaryRadical_le_XiP_of_exponent h.simpleQTKE T hL.1 ho he
    have hshape := (RadicalConjugateRigidity.maximal_radical_structure
      h.simpleQTKE T hL hn ho hd).1
    have heq : I = XiP p L := le_antisymm hle (XiP_le_primaryRadical L hshape)
    apply hi
    change intrinsicSignalizerModule I = ⊥
    rw [heq]
    exact canonical_radical_intrinsicModule_eq_bot h hmany hL hn ho hd
  · obtain ⟨hp5,a,ha,ea⟩ := primaryRadical_higher_structure h.simpleQTKE T hL.1 hn ho he
    exact active_higher_primary_impossible h hmany hL hn ho hp5 hd hi ha ea

/-- The whole solvable radical centralizes the original reduced normalizer module. -/
theorem solvableRadical_centralizes_normalizerReduced
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (solvableRadical L).map L.subtype ≤ centralizer (normalizerReduced L : Set G) := by
  have hc (p : ℕ) (hp : p.Prime) (ho : Odd p) :
      primaryRadical p L ≤ centralizer (normalizerReduced L : Set G) := by
    let : Fact p.Prime := ⟨hp⟩
    by_cases hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))
    · by_contra hact
      let I := primaryRadical p L
      let M := normalizer (L : Set G)
      have hIM : I ≤ M := (map_subtype_le _).trans L.le_normalizer
      have hiN : (I.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
        (normalizer_le_normalizer_primaryRadical L p)
      have hm : ⁅reducedTwoSubgroup M,I.subgroupOf M⁆ ≠ ⊥ := by
        intro hz
        have he := congrArg (Subgroup.map M.subtype) hz
        rw [map_commutator,map_subgroupOf_eq_of_le hIM,Subgroup.map_bot] at he
        change ⁅(reducedTwoSubgroup (normalizer (L : Set G))).map
          (normalizer (L : Set G)).subtype,I⁆ = ⊥ at he
        rw [← normalizerReduced_eq] at he
        exact hact (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans he))
      exact (intrinsicModule_ne_bot_of_reduced_action I M hIM hiN.isSubnormal
        (primaryRadical_twoPerfect L ho) hm)
        (primary_radical_intrinsicModule_eq_bot h hmany hL hn ho hd)
    · rw [primaryRadical_eq_bot_of_not_dvd h.simpleQTKE T hL.1 ho hd]
      exact bot_le
  let J := normalizer (L : Set G)
  let R := (solvableRadical L).map L.subtype
  have hRJ : R ≤ J := (map_subtype_le _).trans L.le_normalizer
  let N := R.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  have hNC : N ≤ centralizer (reducedTwoSubgroup J : Set J) := by
    apply normal_centralizes_reduced_of_primary_residuals N _ isPReduced_reducedPSubgroup
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have he : ((primeToResidual p N).map N.subtype).map J.subtype = primaryRadical p L := by
      rw [map_embedded_primeToResidual_of_hom,
        map_subgroupOf_eq_of_le hRJ,← map_embedded_primeToResidual_of_hom p (solvableRadical L) L.subtype]
      rfl
    intro x hx
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := mem_centralizer_iff.mp (hc p hp ho (he ▸ mem_map_of_mem J.subtype hx))
      (v : G) (by rw [normalizerReduced_eq]; exact mem_map_of_mem J.subtype hv)
    exact Subtype.ext hh
  intro r hr
  apply mem_centralizer_iff.mpr
  rw [normalizerReduced_eq]
  rintro v ⟨w,hw,rfl⟩
  exact congrArg Subtype.val
    (mem_centralizer_iff.mp (hNC (show (⟨r,hRJ hr⟩ : J) ∈ N from hr)) w hw)

/-- Original 13.1.4(5) and13.1.8 for the literal faithful maximal component,
with all radical-centralization source inputs discharged. -/
theorem maximal_nonquasisimple_normalizer_action_source
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (NormalizerReducedAction.componentMap L).ker = solvableRadical L ∧
      L ⊓ centralizer (normalizerReduced L : Set G) = (solvableRadical L).map L.subtype ∧
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧
        ClassicalGroup.IsPSL (NormalizerReducedAction.componentImage L) 2 p) ∧
      normalizerMoved L ≠ ⊥ ∧
      ∀ L₁ : Subgroup G, (solvableRadical L).map L.subtype ⊔ L₁ = L →
        ⁅normalizerReduced L,L₁⁆ = normalizerMoved L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hne := (faithful_maximal_normalizer_moved h.simpleQTKE hL hTL).2.1
  have hc := solvableRadical_centralizes_normalizerReduced h hmany hL.1 hn
  have hk := NormalizerReducedAction.kernel_eq_solvableRadical hL.1.1 hne hc
  have hC : L ⊓ centralizer (normalizerReduced L : Set G) =
      (solvableRadical L).map L.subtype := by
    have hh := congrArg (Subgroup.map L.subtype) hk
    rw [NormalizerReducedAction.componentMap_ker_ambient,map_comap_eq,range_subtype] at hh
    exact hh
  obtain ⟨p,hp,hp3,he⟩ := nonquasisimple_local_radical_quotient h.simpleQTKE T hL.1.1 hn
  exact ⟨hk,hC,⟨p,hp,hp3,he.of_mulEquiv
    (NormalizerReducedAction.radicalQuotientEquiv hL.1.1 hne hc).symm⟩,
    hne,fun _ hgen => NormalizerReducedAction.supplement_commutator hc hgen⟩

/-- Radical centralization on the literal moved module. -/
theorem solvableRadical_centralizes_normalizerMoved
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (solvableRadical L).map L.subtype ≤ centralizer (normalizerMoved L : Set G) := by
  apply (solvableRadical_centralizes_normalizerReduced h hmany hL hn).trans
  apply centralizer_le
  rw [normalizerMoved_eq,← normalizerReduced_eq]
  apply le_normalizer_iff_commutator_le_left.mp
  rw [normalizerReduced_eq]
  let M := normalizer (L : Set G)
  let : (reducedTwoSubgroup M).Normal := isPReduced_reducedPSubgroup.normal
  have hm := (reducedTwoSubgroup M).le_normalizer_map M.subtype
  rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hm
  exact L.le_normalizer.trans hm

/-- The original moved-module weak-closure application now requires only its TI source input. -/
theorem normalizerMoved_weakClosure_bound_source
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hTI : IsTISubgroup (normalizerMoved L)) :
    (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) i ≤
      centralizer (normalizerMoved L : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved L) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved L) :=
  normalizerMoved_weakClosure_bound h.simpleQTKE hL hn
    (solvableRadical_centralizes_normalizerMoved h hmany hL.1 hn) hTI

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple

namespace CFSG.Quasithin.Chapter14.Section03.FaithfulSource
open Chapter1 Chapter12.Section02 Chapter13.Section01 Chapter13.Section01.SourceNonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L₀ : Subgroup G}

/-- The actual nonquasisimple branch of13.3.2 has a maximal faithful component
whose reduced normalizer action has precisely its solvable radical as kernel. -/
theorem Hypothesis1331.nonquasisimple_maximal_action_of_many
    (h : Hypothesis1331 T L₀)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) :
    ∃ K : Subgroup G, L₀ ≤ K ∧ FaithfulMaximalLocal T K ∧
      ¬ IsQuasisimple (XiQuotient K) ∧
      (solvableRadical K).map K.subtype ≤ centralizer (normalizerReduced K : Set G) ∧
      (NormalizerReducedAction.componentMap K).ker = solvableRadical K ∧
      ∃ p : ℕ, p.Prime ∧ 3 < p ∧
        ClassicalGroup.IsPSL (NormalizerReducedAction.componentImage K) 2 p := by
  obtain ⟨K,hK,hLK,hf,hkn,_⟩ := h.maximal_counterexample_of_many hmany hn
  have ha := maximal_nonquasisimple_normalizer_action_source h.hypothesis1311 hmany hf hkn.2
  exact ⟨K,hLK,hf,hkn.2,
    solvableRadical_centralizes_normalizerReduced h.hypothesis1311 hmany hK hkn.2,
    ha.1,ha.2.2.1⟩

end CFSG.Quasithin.Chapter14.Section03.FaithfulSource
