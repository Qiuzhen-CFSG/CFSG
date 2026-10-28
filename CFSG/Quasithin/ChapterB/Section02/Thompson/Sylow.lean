module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import Theory.GroupTheory.SylowNormalClosure

/-!
# Higher Thompson subgroups and Sylow normal generation

Conjugating an elementary two-subgroup into a fixed Sylow subgroup preserves
its order. Thus the Sylow and the whole group have the same two-rank and
rank-indexed Thompson families. The whole-group Thompson subgroup is precisely
the normal closure of the Sylow Thompson subgroup.

This is the normal-generation step for the literal images in
Aschbacher--Smith 15.1.13(4), printed p.1091.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

private theorem elementary_conjugate_into_sylow (S : Sylow 2 G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) := by
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P S
  refine ⟨g,?_⟩
  rw [←hg]
  exact map_mono hP

theorem twoRank_sylow_eq_top (S : Sylow 2 G) :
    twoRank (S : Subgroup G) = twoRank (⊤ : Subgroup G) := by
  unfold twoRank
  congr 1
  apply le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ le_top).1
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup G)
  let := hA.2.1
  obtain ⟨g,hg⟩ := elementary_conjugate_into_sylow S A
  obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty (S : Subgroup G)
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have hb := hB.2.2 (A.map (MulAut.conj g).toMonoidHom) hg inferInstance
  rw [card_map_of_injective (MulAut.conj g).injective,
    elementaryAbelianMaxSubgroups_card_eq _ _ hA,
    elementaryAbelianMaxSubgroups_card_eq _ _ hB] at hb
  exact hb

theorem thompsonJ_sylow_le_top (S : Sylow 2 G) (i : ℕ) :
    thompsonJ (S : Subgroup G) i ≤ thompsonJ (⊤ : Subgroup G) i := by
  apply sSup_le
  intro A hA
  apply le_sSup
  exact ⟨le_top,hA.2.1,by simpa only [twoRank_sylow_eq_top S] using hA.2.2⟩

theorem thompsonJ_top_eq_normalClosure_sylow (S : Sylow 2 G) (i : ℕ) :
    thompsonJ (⊤ : Subgroup G) i = normalClosure (thompsonJ (S : Subgroup G) i : Set G) := by
  let : (thompsonJ (⊤ : Subgroup G) i).Characteristic := thompsonJ_characteristic i
  apply le_antisymm ?_ (normalClosure_le_normal (thompsonJ_sylow_le_top S i))
  apply sSup_le
  intro A hA
  let := hA.2.1
  obtain ⟨g,hg⟩ := elementary_conjugate_into_sylow S A
  have hAg : A.map (MulAut.conj g).toMonoidHom ∈ thompsonFamily (S : Subgroup G) i := by
    refine ⟨hg,IsElementaryAbelian.map _,?_,?_⟩
    · simpa only [twoRank_sylow_eq_top S] using hA.2.2.1
    · rw [card_map_of_injective (MulAut.conj g).injective,twoRank_sylow_eq_top S]
      exact hA.2.2.2
  intro a ha
  let N := normalClosure (thompsonJ (S : Subgroup G) i : Set G)
  have hm : g*a*g⁻¹ ∈ N := le_normalClosure ((le_sSup hAg) (mem_map_of_mem _ ha))
  have hb := (inferInstance : N.Normal).conj_mem (g*a*g⁻¹) hm g⁻¹
  simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hb
theorem le_normalizer_thompsonJ (S : Subgroup G) (i : ℕ) :
    S ≤ normalizer (thompsonJ S i : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (thompsonJ S i).map (MulAut.conj s).toMonoidHom = thompsonJ S i
  rw [←thompsonJ_map_equiv]
  exact congrArg (fun R => thompsonJ R i) (mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs))
end CFSG.Quasithin.ChapterB
