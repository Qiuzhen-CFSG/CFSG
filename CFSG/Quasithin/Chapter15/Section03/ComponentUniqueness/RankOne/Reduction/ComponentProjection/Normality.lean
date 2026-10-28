module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ComponentProjection.Construction

/-!
# Relative normality after component containment

A noncentral subgroup contained in a component distinguishes that component
from every commuting conjugate. Thus its normalizer in `I` fixes the component.
After `Y₊ ≤ L`, this applies to `S`. Minimality of the outside overgroup gives
`I = L S`, and hence normality of `L` in `I`, not in the ambient group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43, final sentences on printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
variable {G : Type*} [Group G]

/-- A normalizer of a noncentral subgroup in a component preserves the component. -/
theorem normalizes_component_of_noncentral
    {Y S I L : Subgroup G} (hLI : L ≤ I)
    (hL : IsComponent I (L.subgroupOf I))
    (hSI : S ≤ I) (hSY : S ≤ normalizer (Y : Set G))
    (hYL : Y ≤ L) (hact : ⁅L, Y⁆ ≠ ⊥) : S ≤ normalizer (L : Set G) := by
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hcomp : IsComponentIn L I := ⟨hLI, hL⟩
  have hconj : IsComponentIn (L.map (MulAut.conj s).toMonoidHom) I := by
    have h := hcomp.map (MulAut.conj s)
    have he : I.map (MulAut.conj s).toMonoidHom = I :=
      mem_normalizer_iff_map_conj_eq.mp (I.le_normalizer (hSI hs))
    rwa [he] at h
  by_contra hne
  have hc := hcomp.commutator_eq_bot_of_ne hconj (Ne.symm hne)
  have hYconj : Y ≤ L.map (MulAut.conj s).toMonoidHom := by
    have hm := map_mono (f := (MulAut.conj s).toMonoidHom) hYL
    have he : Y.map (MulAut.conj s).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp (hSY hs)
    rwa [he] at hm
  exact hact (eq_bot_iff.mpr ((commutator_mono le_rfl hYconj).trans hc.le))

/-- The source normality deduction, after proving containment. -/
theorem relative_normality_of_containment
    {Y S M I L : Subgroup G}
    (hI : I ∈ minimalOutsideFamily Y S M)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hLM : ¬ L ≤ M) (hYL : Y ≤ L)
    (hSY : S ≤ normalizer (Y : Set G))
    (hN : I ⊓ normalizer (Y : Set G) = M ⊓ I) :
    I = L ⊔ S ∧ I ≤ normalizer (L : Set G) ∧ (L.subgroupOf I).Normal := by
  have hSI : S ≤ I := le_sup_right.trans hI.1.1.2
  have hSL := normalizes_component_of_noncentral hLI hL hSI hSY hYL
    (component_action_ne_bot hLI hLM hN)
  have he := eq_component_join_sylow hI P hP hLI hYL hLM
  have hn : I ≤ normalizer (L : Set G) := he ▸ sup_le L.le_normalizer hSL
  exact ⟨he, hn, normal_subgroupOf_of_le_normalizer hn⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.ComponentProjection
