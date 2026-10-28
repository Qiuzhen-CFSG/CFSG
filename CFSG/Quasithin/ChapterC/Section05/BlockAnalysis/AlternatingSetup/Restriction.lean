module

public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup.Marked
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.NormalizerRestriction

/-!
# Returning to the original possibly block-permuting Sylow subgroup

Restrict R to its normalizer of K. The original commutator equation puts
J(R) in this restriction, and Baum(R) is present by C.5.4(1). Thompson and
Baumann heredity therefore preserve both original subgroups. The supplied
literal Sylow intersection with K makes the restriction Sylow in its block
extension. The normalized calculation consequently applies to the original
Baumann subgroup, even when R exchanges two blocks.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/
public section
open Subgroup Stellmacher BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
open ConjugateSource CounterexampleCharacteristic.ReducedMarking
variable {G : Type*} [Group G] [Finite G]

theorem source_marked_action (R K : Subgroup G) (hR : IsPGroup 2 R)
    (hK : IsAlternatingBlock K 5) (hmove : K = ⁅K,elementaryAbelianMaxJ R⁆)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K) :
    (K ⊔ ChapterB.baumann R).pCoreIn 2 ≤ ChapterB.baumann R ∧
    ∃ (q : (K ⊔ ChapterB.baumann R : Subgroup G) →* FivePerm)
      (e : sourceModule K ≃* Multiplicative (core (Fin 5))),
      (K.subgroupOf (K ⊔ ChapterB.baumann R)).map q = alternatingGroup (Fin 5) ∧
      ((ChapterB.baumann R).subgroupOf (K ⊔ ChapterB.baumann R)).map q = ChapterB.Offenders.D 5 ∧
      ∀ (s : (K ⊔ ChapterB.baumann R : Subgroup G)) (u : sourceModule K),
        (e.symm (Multiplicative.ofAdd
          (coreRepresentation (Fin 5) (q s) (e u).toAdd)) : G) =
            (s : G) * (u : G) * (s : G)⁻¹ := by
  let T := R ⊓ normalizer (K : Set G)
  obtain ⟨hJeq,hBeq,Q,hQ⟩ := normalizer_restriction R K hR hmove hn P hP
  have hT : IsPGroup 2 T := hR.to_le inf_le_left
  have hm : K = ⁅K,elementaryAbelianMaxJ T⁆ := by rw [hJeq]; exact hmove
  have h := marked_normalized_source K T hK hT inf_le_right Q hQ hm
  exact hBeq ▸ h

theorem source_core_and_module (R K : Subgroup G) (hR : IsPGroup 2 R)
    (hK : IsAlternatingBlock K 5)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G))
    (hc : (K ⊔ ChapterB.baumann R).pCoreIn 2 ≤ ChapterB.baumann R) :
    sourceModule K ≤ ChapterB.baumann R ∧
      (K ⊔ ChapterB.baumann R).pCoreIn 2 =
        ChapterB.baumann R ⊓ centralizer (sourceModule K : Set G) := by
  let S := ChapterB.baumann R
  let : IsElementaryAbelian 2 (sourceModule K) := hK.2.1.elementary.map K.subtype
  have he : (K ⊔ S).pCoreIn 2 = (K ⊔ S) ⊓ centralizer (sourceModule K : Set G) :=
    (normal_short_extension_centralizer K S hK.2.1 (hR.to_le inf_le_left) hn).symm
  have hu : sourceModule K ≤ (K ⊔ S).pCoreIn 2 := by
    rw [he]
    exact le_inf ((map_subtype_le _).trans le_sup_left) (le_centralizer _)
  exact ⟨hu.trans hc,le_antisymm (le_inf hc (he.le.trans inf_le_right))
    ((inf_le_inf le_sup_right le_rfl).trans he.ge)⟩
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
