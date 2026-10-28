module
public import Theory.GroupTheory.CComponent.SylowOvergroupUnique
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityJanko

/-!
# The simple-model obstruction to moved-component maximality

Restrict the original full Sylow to a normalized containing component K.
If every overgroup of that intrinsic Sylow has a unique C-component, the
smaller component is characteristic in the intersection of K with its
original local join. The ambient Sylow must therefore fix it.

Uniqueness lifts through the solvable radical of K. Theorems A and C,
applied with the original local hypotheses, identify this literal radical
quotient as a nonabelian simple member of the complete Theorem C list.
Thus a moved component inside a normalized overcomponent yields a failure
of Sylow-overgroup component uniqueness in an actual simple model.

This is a reduction to the still-needed model calculations, not a proof
of unconditional maximality. Source: Aschbacher--Smith, A.3.12 and
1.2.8(1--3), printed pp.47--48 and 506--507.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
open ChapterA.Section03
variable {G : Type*} [Group G] [Finite G]

/-- Unique components in intrinsic Sylow overgroups prevent an ambient Sylow swap. -/
theorem local_chain_normalizes_of_sylow_overgroup_unique
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hu : SylowOvergroupComponentUnique K) :
    (T : Subgroup G) ≤ normalizer (B : Set G) := by
  let H := K ⊔ (T : Subgroup G)
  have hBH : B ≤ H := hBK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hb : B.subgroupOf H ∈ localCComponents S :=
    ((mem_LIn_iff_subgroupOf le_sup_right hBH).mp ⟨hBH,hB⟩).1
  have hk : (S : Subgroup H) ≤ normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq (show K ≤ H from le_sup_left)]
    exact comap_mono hTK
  have hn := SylowOvergroupComponentUnique.normalizes_local_component S hb
    hK.1.subnormal (comap_mono hBK) hk
    (hu.of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  rw [← subgroupOf_normalizer_eq hBH] at hn
  intro t ht
  exact hn (show (⟨t,(show (T : Subgroup G) ≤ H from le_sup_right) ht⟩ : H) ∈ S from ht)

private theorem local_sqtk (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : IsSQTK KnownSimple.IsKnownSimple H := by
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : IsTwoLocal N := ⟨R,hH,isPGroup_pCoreIn 2 H,rfl⟩
  have hh := (hG.twoLocal_sqtk hN).subgroup (H.subgroupOf N)
  exact ⟨hh.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective,
    hh.isKGroup.of_injective
      (subgroupOfEquivOfLe hHN).symm.toMonoidHom (subgroupOfEquivOfLe hHN).symm.injective⟩

/-- A moved component in a Sylow-invariant overcomponent supplies an actual
simple Theorem C model where Sylow-overgroup component uniqueness fails. -/
theorem moved_normalized_simple_quotient_obstruction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    IsSimpleGroup Q ∧ ¬ IsMulCommutative Q ∧ LocalModels.TheoremCModel Q ∧
      ¬ SylowOvergroupComponentUnique Q := by
  let H := K ⊔ (T : Subgroup G)
  let C := K.subgroupOf H
  let Q := C ⧸ solvableRadical C
  let hs : IsSimpleGroup Q := hK.1.isSimpleGroup_quotient_solvableRadical
  let := hK.1.perfect
  have hna : ¬ IsMulCommutative Q := hK.1.not_isMulCommutative_quotient_solvableRadical
  have hq := ChapterA.Section03.SourceComponents.GenerationCore.radical_quotient_sqtk
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (local_sqtk hG hK.2.2) hK.1
  have hmodel : LocalModels.TheoremCModel Q :=
    ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna
      (ChapterA.Section02.theoremC_knownSimple hs hna hq.stronglyQuasithin hq.isKGroup)
  refine ⟨hs,hna,hmodel,?_⟩
  intro hu
  let : Group.IsSolvable (QuotientGroup.mk' (solvableRadical C)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have huC : SylowOvergroupComponentUnique C :=
    hu.of_surjective (QuotientGroup.mk' (solvableRadical C))
      (QuotientGroup.mk'_surjective _)
  have huK : SylowOvergroupComponentUnique K :=
    huC.of_equiv (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).symm
  exact hm.not_ge (conjugateSpanBy_le le_rfl
    (local_chain_normalizes_of_sylow_overgroup_unique T hB hK hBK hTK huK))

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
