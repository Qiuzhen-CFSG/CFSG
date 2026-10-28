module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelMovement
public import Theory.GroupTheory.PResidual.SimpleImage

/-!
# Full commutator with the outside kernel residual

The nontrivial two-residual X of C_H(U) normalizes the original L and has
nontrivial commutator image on L/O₂(L). This quotient is the marked A₅
quotient, so simplicity and two-perfection give [L,X]=L. The final consumer
constructs X using the actual omega-orbit action kernel.

Source: Aschbacher–Smith 13.2.9, printed p. 880.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The nontrivial source kernel residual generates the whole original component. -/
theorem outside_twoPerfect_commutator_eq_component
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H X : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hXH : X ≤ H) (hnX : H ≤ normalizer (X : Set G))
    (hXM : X ≤ normalizer (L : Set G))
    (hne : X ≠ ⊥) (hpX : IsPPerfect 2 X) : ⁅L,X⁆ = L := by
  let N := ⁅L,X⁆.subgroupOf L
  have hNL : ⁅L,X⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hXM
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left L X)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hnot : ¬ N ≤ d.flag.module.action.ker := by
    intro hn
    apply outside_twoPerfect_commutator_not_le_component_core d hH hs hXH hnX hne hpX
    rw [← map_subgroupOf_eq_of_le hNL]
    exact (map_mono hn).trans_eq (congrArg (map L.subtype) d.flag.action_kernel)
  have hN : N = ⊤ := normal_eq_top_of_simple_image d.twoPerfect
    d.flag.module.action d.flag.module.onto (d.flag.action_kernel ▸ pCore_isPGroup) N hnot
  exact le_antisymm hNL (subgroupOf_eq_top.mp hN)
/-- The literal kernel residual has full component commutator, with all placement
and normalization conclusions obtained from the original outside source. -/
theorem source_kernel_residual_full_commutator
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    X ≤ H ∧ X ≤ normalizer (L : Set G) ∧ H ≤ normalizer (X : Set G) ∧
      X ≠ ⊥ ∧ IsPPerfect 2 X ∧ ⁅L,X⁆ = L := by
  obtain ⟨hXH,hXM,hnX,hXne,hpX,_⟩ :=
    source_kernel_residual_moves_component d hH hB hZ hs hne
  exact ⟨hXH,hXM,hnX,hXne,hpX,
    outside_twoPerfect_commutator_eq_component d hH hs hXH hnX hXM hXne hpX⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside
