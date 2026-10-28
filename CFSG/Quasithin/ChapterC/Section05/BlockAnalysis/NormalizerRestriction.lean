module

public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Restricting the original Sylow group to a block normalizer

The original commutator equation puts J(R) inside R∩N(K), while C.5.4(1)
puts Baum(R) there. Heredity preserves both groups. The literal full Sylow
intersection with K supplies a Sylow in K(R∩N(K)) by the coprime index
criterion. Both the natural and alternating C.5.4 source branches use
this same restriction, even when R permutes the original blocks.

Source: Aschbacher–Smith C.5.3–4, printed pp.154–155.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]

theorem normalizer_restriction (R K : Subgroup G) (hR : IsPGroup 2 R)
    (hmove : K = ⁅K,elementaryAbelianMaxJ R⁆)
    (hn : ChapterB.baumann R ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype = R ⊓ K) :
    let T := R ⊓ normalizer (K : Set G)
    elementaryAbelianMaxJ T = elementaryAbelianMaxJ R ∧
      ChapterB.baumann T = ChapterB.baumann R ∧
      ∃ Q : Sylow 2 (K ⊔ T : Subgroup G),
        (Q : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T := by
  let T := R ⊓ normalizer (K : Set G)
  have hBT : ChapterB.baumann R ≤ T := le_inf inf_le_left hn
  have hJ : elementaryAbelianMaxJ R ≤ T := le_inf
    (sSup_le fun _ hA => hA.1) (le_normalizer_iff_commutator_le_left.mpr hmove.symm.le)
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq T R inf_le_left
  have hl := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R T hJ
  have ho : elementaryAbelianMaxOrder T = elementaryAbelianMaxOrder R := le_antisymm hs.1 hl.1
  have hJeq : elementaryAbelianMaxJ T = elementaryAbelianMaxJ R :=
    le_antisymm (hs.2 ho) (hl.2 ho.symm)
  have hBeq : ChapterB.baumann T = ChapterB.baumann R :=
    baumann_eq_of_intermediate R T hBT inf_le_left
  have hT : IsPGroup 2 T := hR.to_le inf_le_left
  have hPT : (P : Subgroup K).map K.subtype ≤ T := by
    rw [hP]
    exact le_inf inf_le_left (inf_le_right.trans K.le_normalizer)
  obtain ⟨Q,hQ⟩ := IsPGroup.exists_sylow_sup_of_coprime_index K T hT inf_le_right
    (P : Subgroup K) P.not_dvd_index hPT
  exact ⟨hJeq,hBeq,Q,hQ⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
