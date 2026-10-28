module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import CFSG.Quasithin.Chapter10.SourceThompsonNormalization
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.DeletedSection

/-!
# Original deleted A₅ representatives fixed by the Thompson subgroup

For the actual moved factor W=[D.fullModule,L], the common normalizer
M∩N(L) contains J(T) and normalizes W. The original deleted marking therefore
puts each vector of W into C_W(J(T)) by an element of the original component.
This includes both nonzero vector orbits and zero. No full/local-module
identity, escaping Baumann normalizer, or fixed-vector exclusion is assumed.

The resulting all-vector orbit statement is the input to the original point
Sylow and Thompson completion in SourceA5PointSylow. Source: Aschbacher–Smith,
10.1.1(2),10.1.2(2),10.2.9(1), printed pp.741,750.
-/

public section
open Subgroup Theory.GroupTheory Representation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D in
private theorem deleted_uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
local instance pointSylowDeletedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_deleted_thompson_fixed_representative
    (q : L →* alternatingGroup (Fin 5)) (hq : Function.Surjective q)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin 5)).comp q))
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) :
    ∃ l ∈ L, (MulAut.conj l) v ∈ ⁅D.fullModule,L⁆ ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  have hLM : L ≤ D.maximalLocal := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hLN : L ≤ N := le_inf hLM L.le_normalizer
  have hNW : N ≤ normalizer (W : Set G) := by
    intro n hn
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hn.1),
      mem_normalizer_iff_map_conj_eq.mp hn.2]
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (hLM.trans D.maximalLocal_normalizes_fullModule)
  have hWT : W ≤ (T : Subgroup G) := hWV.trans (D.fullModule_le_sylow (deleted_uniqueness D))
  have hJN : elementaryAbelianMaxJ (T : Subgroup G) ≤ N :=
    le_inf ((sSup_le fun _ hA => hA.1).trans hTM) D.thompson_normalizes_component
  obtain ⟨l, hl⟩ := ChapterB.deleted_section_thompson_fixed_representative
    (T : Subgroup G) L W N T.isPGroup' hWT hLN hNW inf_le_right hJN q hq c ⟨v, hv⟩
  exact ⟨l, l.property, hl⟩

end
end CFSG.Quasithin.Chapter10
