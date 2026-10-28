module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.FullModule
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The original rank-three flag in a classified full unitary module

The section-centralizer conjugation comparing the original chosen module
with the full module preserves all stabilizers inside L. Indeed, its
commutators with L lie in O₂(L), which centralizes the chosen module.
Once the classified full module has order at most 64, the original natural
six-space fills it. Its literal rank-three subgroup keeps its cardinality,
its stabilizer and its ambient centralizer bound in these coordinates.

This supplies the chosen/full-module compatibility used in the Rudvalis
branch of 4.2.13(5). The bound on the full module still belongs to the actual
C.4.8 classification; no equality is inferred before that bound is proved.
Source: Aschbacher–Smith, 4.2.12–13 and 4.4.6, printed pp.610–612,620.
-/

public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The same subgroup of L stabilizes a flag member after a section-centralizer
conjugation. The assumption uses the literal O₂(L), not an abstract kernel. -/
theorem section_conjugate_flag_stabilizer {L U : Subgroup G}
    (hQU : L.pCoreIn 2 ≤ normalizer (U : Set G))
    (c : sectionCentralizer L) :
    L ⊓ normalizer (U.map (MulAut.conj (c : G)).toMonoidHom : Set G) =
      L ⊓ normalizer (U : Set G) := by
  have hs := (le_sectionCentralizer_iff (sectionCentralizer L) L).mp le_rfl
  ext l
  by_cases hl : l ∈ L
  · simp only [mem_inf, hl, true_and]
    rw [← map_equiv_normalizer_eq]
    change (∃ x ∈ normalizer (U : Set G), (MulAut.conj (c : G)) x = l) ↔
      l ∈ normalizer (U : Set G)
    have hq : ⁅(c : G)⁻¹,l⁆ ∈ normalizer (U : Set G) :=
      hQU (hs.2 (commutator_mem_commutator ((sectionCentralizer L).inv_mem c.property) hl))
    have he : (MulAut.conj (c : G)).symm l = ⁅(c : G)⁻¹,l⁆ * l := by
      simp [commutatorElement_def]
    constructor
    · rintro ⟨x,hx,hxl⟩
      have hx' : (MulAut.conj (c : G)).symm l ∈ normalizer (U : Set G) := by
        rw [← hxl, MulEquiv.symm_apply_apply]
        exact hx
      rw [he] at hx'
      exact (mul_mem_cancel_left hq).mp hx'
    · intro hlU
      exact ⟨_, he.symm ▸ (normalizer (U : Set G)).mul_mem hq hlU,
        (MulAut.conj (c : G)).apply_symm_apply l⟩
  · simp [hl]

omit [Finite G] in
/-- The original ambient centralizer bound survives exactly the conjugation
used to compare section Sylows. -/
theorem section_conjugate_flag_centralizer {L U : Subgroup G}
    (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (c : sectionCentralizerIn (normalizer (L : Set G)) L) :
    centralizer (U.map (MulAut.conj (c : G)).toMonoidHom : Set G) ≤
      normalizer (L : Set G) := by
  have hh := map_mono (f := (MulAut.conj (c : G)).toMonoidHom) hC
  have he : (normalizer (L : Set G)).map (MulAut.conj (c : G)).toMonoidHom =
      normalizer (L : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).le_normalizer c.property.1)
  rw [map_centralizer_equiv, he] at hh
  exact hh

/-- The classified full six-space carries the original flag, with its full
L-stabilizer and ambient centralizer bound. Only the source dimension bound
on the full module is required in addition to the original chosen data. -/
theorem chosen_flag_of_section_conjugation {T : Sylow 2 G} {L V U W : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (hV : Nat.card V = 64)
    (hUV : U ≤ V) (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W)
    (hW : Nat.card W ≤ 64) :
    V.map (MulAut.conj (c : G)).toMonoidHom = W ∧
      U.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      Nat.card (U.map (MulAut.conj (c : G)).toMonoidHom) = Nat.card U ∧
      L ⊓ normalizer (U.map (MulAut.conj (c : G)).toMonoidHom : Set G) =
        L ⊓ normalizer (U : Set G) ∧
      centralizer (U.map (MulAut.conj (c : G)).toMonoidHom : Set G) ≤
        normalizer (L : Set G) := by
  have hQLT : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L) ((pCoreIn_le 2 L).trans le_sup_left)
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hQU : L.pCoreIn 2 ≤ normalizer (U : Set G) :=
    ((hQLT.trans D.core_centralizes).trans (centralizer_le hUV)).trans
      (Subgroup.centralizer_le_normalizer _)
  exact ⟨eq_of_le_of_card_ge hVW (by rwa [card_map_of_injective (MulAut.conj (c : G)).injective,hV]),
    (map_mono hUV).trans hVW,card_map_of_injective (MulAut.conj (c : G)).injective,
    section_conjugate_flag_stabilizer hQU ⟨c,c.property.2⟩,
    section_conjugate_flag_centralizer hC c⟩

end CFSG.Quasithin.Chapter4.Section02.Unitary
