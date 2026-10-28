module
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Ambient control from the elementary Thompson Frattini argument

A normal subgroup containing the Thompson subgroup of a Sylow two-subgroup
supplements its normalizer. Transporting this equality through the actual
subtype inclusion gives ambient containment from bounds on those two factors.
The centralizer specialization applies to any normalized module, retaining its
original conjugation action.

Source application: Aschbacher--Smith, combined manuscript (1 March 2004),
the small Thompson case of Lemma 12.6.11, printed p.825.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Relative Frattini control with the literal ambient Thompson subgroup. -/
theorem le_of_thompson_normalizer_control
    (H M D : Subgroup G) (S : Sylow 2 H)
    (hn : H ≤ normalizer (D : Set G)) (hDM : D ≤ M)
    (hJ : elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ≤ D)
    (hN : normalizer (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) : Set G) ≤ M) :
    H ≤ M := by
  let D' := D.subgroupOf H
  let : D'.Normal := normal_subgroupOf_of_le_normalizer hn
  have hm : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) :=
    (elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective _).symm
  have hj : elementaryAbelianMaxJ (S : Subgroup H) ≤ D' := by
    intro x hx
    exact hJ (hm ▸ mem_map_of_mem H.subtype hx)
  have hf := elementaryAbelianMaxJ_frattini_of_le_normal S D' hj
  have hbound : normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) ⊔ D' ≤
      M.subgroupOf H := by
    refine sup_le ?_ ?_
    · intro x hx
      apply hN
      rw [←hm]
      exact le_normalizer_map H.subtype (mem_map_of_mem H.subtype hx)
    · intro x hx
      exact hDM hx
  rw [hf] at hbound
  intro x hx
  exact hbound (show (⟨x,hx⟩ : H) ∈ ⊤ from mem_top _)

/-- A normalized module centralizing the Sylow Thompson subgroup gives
ambient containment once both relevant normalizers are controlled. -/
theorem le_of_thompson_normalizer_centralizer_control
    (H M U : Subgroup G) (S : Sylow 2 H)
    (hn : H ≤ normalizer (U : Set G))
    (hC : H ⊓ centralizer (U : Set G) ≤ M)
    (hJ : elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ≤ centralizer (U : Set G))
    (hN : normalizer (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) : Set G) ≤ M) :
    H ≤ M := by
  apply le_of_thompson_normalizer_control H M (H ⊓ centralizer (U : Set G)) S
    ?_ hC ?_ hN
  · exact (le_inf H.le_normalizer (hn.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  · exact le_inf ((sSup_le fun _ hA => hA.1).trans (map_subtype_le _)) hJ

end Stellmacher
