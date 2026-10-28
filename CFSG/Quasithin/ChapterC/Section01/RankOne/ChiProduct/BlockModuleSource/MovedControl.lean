module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Control
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.Movement

/-!
# The moved outside block supplied by the original local seed

Combine the actual block lift, intrinsic module recognition, exceptional
A₇ control and Thompson movement. The remaining local premises are exactly
module support and full offender movement; no ambient block or type marking
is assumed.

Source: Aschbacher--Smith C.1.27--28, printed pp.133--134.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Literal C.1.28 application of the local seed, retaining original J(T). -/
theorem source_outside_moved_chi_of_local_seed
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M K V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ K ≤ M)
    (hV : V = normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hK : IsChiBlock K) (hs : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hU : (blockU K).map K.subtype ≤ V)
    (hJ : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hmove : let q := QuotientGroup.mk' (centralizer (V : Set G));
      let ρ := NormalElementaryQuotient.representation V q (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _);
      K.map q = ⁅K.map q, generatedBy {A | IsBestOffender ρ A}
        ((T.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V : Set G)))) :
          Subgroup (G ⧸ centralizer (V : Set G)))⁆) :
    ∃ L : Subgroup G, K ≤ L ∧ ¬ L ≤ M ∧ IsChiBlockIn L ∧
      (blockU L).map L.subtype ≤ V ∧
      L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [← hf]
    exact centralizer_generalizedFitting_le G
  obtain ⟨L,hKL,hn,hL,hUL⟩ := source_outside_chi_of_local_seed
    hA hC h4 hG T hchar M K V hM hout hV hK hs hU hmove
  exact ⟨L,hKL,hn,hL,hUL,block_moved_of_short_seed hf K L _ hK.short hL hKL hJ⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
