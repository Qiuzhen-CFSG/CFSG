module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Removing the star kernel after relative block selection

A nonzero normal elementary module commutator is the entire short block
layer. Thus U(K) lies in the original star module, and its centralizer is
exactly O₂(K). The kernel of the literal star action is consequently the
two-core itself. The resulting quotient equivalence preserves the supplied
A₇ marking on every original element; no abstract splitting of a central
cover is used.

Block selection is an explicit premise here, to be discharged separately
in the natural and exceptional source branches.
Source: Aschbacher--Smith C.1.7--11, pp.123--124, C.1.27, p.133, and
C.2.7(3)(a),(b),(d), pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- A reconstructed relative block removes the whole original star kernel. -/
noncomputable def quotientEquiv_of_block (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 7))
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ R))) :
    (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) := by
  let J := K ⊔ R
  let L := K.subgroupOf J
  let : L.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer h.normalizes)
  let V := starV K R
  let q := QuotientGroup.mk' (starKernel K R)
  let a : L ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  have hm : ⁅V,L⁆ ≠ ⊥ := by
    intro hm
    have hL : L ≤ starKernel K R := by
      change L ≤ centralizer (V : Set J)
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)
    have hz : starImage K R K = ⊥ := by
      exact (Subgroup.map_eq_bot_iff (f := q) L).mpr
        ((QuotientGroup.ker_mk' (starKernel K R)).symm ▸ hL)
    let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
    let : Nontrivial (starImage K R K) := e.surjective.nontrivial
    exact (nontrivial_iff_ne_bot _).mp inferInstance hz
  have hu : (ChapterC.blockU L).map L.subtype ≤ V := by
    rw [ChapterC.RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator L V hb hm]
    exact commutator_le_left V L
  have hk : (q.subgroupMap L).ker = pCore 2 L := by
    apply le_antisymm
    · intro l hl
      rw [← hb.short.centralizer_blockU]
      intro u hu'
      have hc : (l : J) ∈ centralizer (V : Set J) :=
        (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hl)
      exact Subtype.ext (hc u (hu (mem_map_of_mem L.subtype hu')))
    · intro l hl
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff _).mpr
      apply core_le_starKernel
      have hh := (inferInstance : L.Normal).isSubnormal.pCore_subgroupOf 2
      rw [←hh] at hl
      exact hl
  let b : (L ⧸ pCore 2 L) ≃* starImage K R K :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective L))
  exact (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans (b.trans e)

/-- The recovered equivalence retains the actual original star map. -/
theorem quotientEquiv_of_block_mk (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : starImage K R K ≃* alternatingGroup (Fin 7))
    (hb : ChapterC.IsBlock (K.subgroupOf (K ⊔ R))) (k : K) :
    quotientEquiv_of_block h e hb (QuotientGroup.mk' (pCore 2 K) k) =
      e (toStarImage K R k) := by rfl

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
