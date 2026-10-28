module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Restriction
public import Theory.GroupTheory.PCoreRestriction

/-!
# The original two-core supplied to C.1.13(c)

All relative normality and displacement hypotheses for the alternating-five
splitting theorem hold on Q=O₂(K Baum(R)). No central-core equality is used.
The fixed kernel inside U also gives the directness of the final product.

Source: Aschbacher–Smith C.5.4(3–4), p.155, applying C.1.13(c).
-/
public section
open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ConjugateSource CounterexampleCharacteristic.ReducedMarking
variable {G : Type*} [Group G] [Finite G]

theorem source_core_split_inputs (R K : Subgroup G) (hR : IsPGroup 2 R)
    (hK : IsAlternatingBlock K 5)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G)) :
    let Q := (K ⊔ ChapterB.baumann R).pCoreIn 2
    IsPGroup 2 Q ∧ K ≤ normalizer (Q : Set G) ∧ sourceModule K ≤ Q ∧
      ⁅K,Q⁆ ≤ K.pCoreIn 2 := by
  let S := ChapterB.baumann R
  let B := K ⊔ S
  let Q := B.pCoreIn 2
  have hBK : B ≤ normalizer (K : Set G) := sup_le K.le_normalizer hn
  have hBQ : B ≤ normalizer (Q : Set G) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hKQ : K ≤ normalizer (Q : Set G) := le_sup_left.trans hBQ
  have hQK : Q ≤ normalizer (K : Set G) := (pCoreIn_le 2 B).trans hBK
  have he : Q = B ⊓ centralizer (sourceModule K : Set G) :=
    (normal_short_extension_centralizer K S hK.2.1 (hR.to_le inf_le_left) hn).symm
  let : IsElementaryAbelian 2 (sourceModule K) := hK.2.1.elementary.map K.subtype
  refine ⟨isPGroup_pCoreIn 2 B,hKQ,?_,?_⟩
  · exact (le_inf ((show sourceModule K ≤ K from map_subtype_le _).trans le_sup_left)
      (le_centralizer (sourceModule K))).trans he.ge
  · exact (le_inf (le_normalizer_iff_commutator_le_left.mp hQK)
      (le_normalizer_iff_commutator_le_right.mp hKQ)).trans
        (inf_pCoreIn_le_of_le 2 (show K ≤ B from le_sup_left))

omit [Finite G] in
theorem source_product_direct (R K : Subgroup G) (hK : IsAlternatingBlock K 5) :
    Disjoint (sourceModule K) (ChapterB.baumann R ⊓ centralizer (K : Set G)) ∧
      sourceModule K ≤ centralizer
        ((ChapterB.baumann R ⊓ centralizer (K : Set G) : Subgroup G) : Set G) := by
  exact ⟨alternatingModule_disjoint_of_commuting K _ hK inf_le_right,
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (map_subtype_le _)))⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
