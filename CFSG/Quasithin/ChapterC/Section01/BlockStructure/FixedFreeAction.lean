module
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Fixed-free block layers determine the action of the two-core

Suppose an abelian subgroup V contains U(L) and [V,L]≤U(L). The two
rotated commutators [O₂(L),L,V] and [L,V,O₂(L)] vanish. Hence [V,O₂(L)]
lies in the fixed layer of U(L). If that layer is trivial, O₂(L)
centralizes V. This identifies the actual action kernel for both A₇ block
types in the original larger-group quotient of C.5.12.
Source: Aschbacher–Smith C.1.13(c) and C.5.12, printed p.163.
-/
public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]

theorem IsShort.core_centralizes_of_fixedFree_moved
    {L V : Subgroup G} (hL : IsShort L)
    (hVL : ⁅V,L⁆ ≤ ((blockU L).map L.subtype)) (hUV : ((blockU L).map L.subtype) ≤ V) [IsMulCommutative V]
    (hz : blockFixed L = ⊥) : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
  have hOU : ⁅L.pCoreIn 2,L⁆ = ((blockU L).map L.subtype) := by
    change ⁅(pCore 2 L).map L.subtype,L⁆ = (blockU L).map L.subtype
    rw [blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype]
  have hUC : ((blockU L).map L.subtype) ≤ centralizer (V : Set G) := by
    intro u hu v hv
    exact congrArg V.subtype (mul_comm (⟨v,hv⟩ : V) ⟨u,hUV hu⟩)
  have hUO : ((blockU L).map L.subtype) ≤ centralizer (L.pCoreIn 2 : Set G) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨q,hq,rfl⟩
    exact congrArg L.subtype (hL.central hu q hq)
  have hWc : ⁅V,L.pCoreIn 2⁆ ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_commutator_eq_bot_of_rotate
    · rw [hOU]
      exact commutator_eq_bot_iff_le_centralizer.mpr hUC
    · apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [commutator_comm L V]
      exact hVL.trans hUO
  have hW : ⁅V,L.pCoreIn 2⁆ ≤ ((blockU L).map L.subtype) :=
    (commutator_mono le_rfl (pCoreIn_le 2 L)).trans hVL
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  intro w hw
  obtain ⟨u,hu,he⟩ := hW hw
  have hc : u ∈ center L := by
    rw [mem_center_iff]
    intro l
    apply Subtype.ext
    change (l : G) * (u : G) = (u : G) * (l : G)
    change (u : G) = w at he
    rw [he]
    exact hWc hw l l.property
  have hf : (⟨u,hu⟩ : blockU L) ∈ blockFixed L := hc
  rw [hz,mem_bot] at hf
  exact mem_bot.mpr (he.symm.trans (congrArg (fun z : blockU L => ((z : L) : G)) hf))
end CFSG.Quasithin.ChapterC
