module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.OutsideSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.Product
/-!
# The complete known-simple outside-block and ordered-product theorems

The full earlier A/C and B.4 source theorems discharge every classification
input of the original outside-block argument. The proved C.1.29 assembly
then eliminates ordinary A7 factors through their actual six-point preimages
and gives at most two actual chi-zero blocks outside the prescribed control
overgroup, with the literal ordered product and original Thompson movement.

Source: Aschbacher–Smith C.1.28–29, printed pp.133–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
universe u
variable {G : Type u} [Group G] [Finite G]

theorem outside_moved_chi_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hproper : M ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ :=
  outside_moved_chi_source
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    ChapterB.SourceClassification.irreducibleClassification_knownSimple hG T hf M hM hproper

theorem ordered_chiZero_product_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hf : generalizedFitting G = pCore 2 G) (T : Sylow 2 G) (M : Subgroup G)
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ L : Fin r → Subgroup G,
      (∀ i, IsChiZeroBlockIn (L i)) ∧ (∀ i, ¬L i ≤ M) ∧
      (∀ i, L i = ⁅L i,elementaryAbelianMaxJ (T : Subgroup G)⁆) ∧
      ∀ g : G, ∃ m : M, ∃ b : ∀ i, L i,
        g = (m : G) * (List.ofFn (fun i => (b i : G))).prod :=
  LocalC129.ordered_chiZero_product_of_c128_outside
    (fun hG hf T M hM hn => outside_moved_chi_knownSimple hG hf T M hM hn)
    hG hf T M hM

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
