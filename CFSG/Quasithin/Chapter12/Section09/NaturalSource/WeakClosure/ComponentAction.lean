module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.WeakClosure.CoreGeometry
public import Theory.GroupTheory.Commutator.SimpleCoreAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The component centralizes the point-core quotient

After alignment, the chosen seed centralizes O₂(G₁)^g/U^g but acts
nontrivially on K₁^g/O₂(K₁)^g. The actual surviving models give a simple
component quotient, and the C-component is perfect. Thus commutators with
the seed generate the component. The three-subgroups lemma then gives
[K₁,O₂(G₁)]≤U. Since U is abelian, [K₁,O₂(K₁)] centralizes U and V.
The original subgroups, quotient maps and relative normality are retained.

Source: Aschbacher--Smith, 12.9.9(1), printed p.863 of `refs/quasithin.pdf`.
The final two-core action contradiction is assembled in `WeakClosure.lean`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem point_component_perfect {F : InvariantFlag T V n}
    (C : ComponentGeometry F L) : Group.IsPerfect C.K1 := by
  let := C.component.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe C.point_le).toMonoidHom)
    (subgroupOfEquivOfLe C.point_le).surjective

private theorem simple_of_binary_model {X : Type*} [Group X] {d : ℕ}
    (hd : 3 ≤ d) (model : ClassicalGroup.IsPSL X d 2) : IsSimpleGroup X := by
  obtain ⟨k, hk, _, _, ⟨e⟩⟩ := model
  let := Atlas.psl_simple_high_rank (F := k) d hd
  exact e.isSimpleGroup

omit [Finite G] in
/-- All three surviving component quotients are actual simple groups. -/
theorem point_component_quotient_simple {F : InvariantFlag T V n}
    (C : ComponentGeometry F L) (control : LocalControl C) :
    IsSimpleGroup (C.K1 ⧸ pCore 2 C.K1) := by
  rcases control.models with ha | hfour | hfive
  · obtain ⟨e⟩ := ha
    let := alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 7))
    exact e.isSimpleGroup
  · exact simple_of_binary_model (by decide) hfour
  · exact simple_of_binary_model (by decide) hfive

/-- A moving Sylow-contained seed conjugate forces K₁ to centralize Q/U,
where Q is the literal two-core of the point normalizer. -/
theorem point_component_core_displacement_of_moving
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) (control : LocalControl C)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥) :
    ⁅C.K1,F.H.pCoreIn 2⁆ ≤ F.U := by
  let := point_component_perfect C
  let := point_component_quotient_simple C control
  obtain ⟨k, he, hk, hVH, _, _, _, hcore⟩ :=
    exists_aligned_moving_core h hn earlier F hab C control g hAT hmove
  have hATk : conjugate V k ≤ (T : Subgroup G) := he ▸ hAT
  have hmovek : ⁅conjugate V k,V⁆ ≠ ⊥ := by rwa [he]
  have halign : conjugate (F.Vi 1) k = conjugate V k ⊓ centralizer (V : Set G) := by
    rwa [he]
  have hback (B : Subgroup G) : conjugate (conjugate B k) k⁻¹ = B := by
    simpa only [inv_inv] using conjugate_conjugate_inv B k⁻¹
  have hAH : conjugate V k⁻¹ ≤ F.H := by
    have hm : conjugate V k⁻¹ ≤ conjugate (conjugate F.H k) k⁻¹ := map_mono hVH
    rwa [hback] at hm
  have hAQ : ⁅conjugate V k⁻¹,F.H.pCoreIn 2⁆ ≤ F.U := by
    have hm := map_mono (f := (MulAut.conj (k⁻¹)⁻¹).toMonoidHom) hcore
    rw [map_commutator] at hm
    change ⁅conjugate (conjugate (F.H.pCoreIn 2) k) k⁻¹,conjugate V k⁻¹⁆ ≤
      conjugate (conjugate F.U k) k⁻¹ at hm
    rwa [hback,hback,commutator_comm] at hm
  have hnon : ¬ ⁅C.K1,conjugate V k⁻¹⁆ ≤ C.K1.pCoreIn 2 := by
    intro hc
    have hm := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hc
    rw [map_commutator] at hm
    change ⁅conjugate C.K1 k,conjugate (conjugate V k⁻¹) k⁆ ≤
      conjugate (C.K1.pCoreIn 2) k at hm
    rw [conjugate_conjugate_inv] at hm
    exact aligned_component_action_nontrivial h earlier F hab C control k hATk hmovek halign hm
  have hHU : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy V F.H
  have hHQ : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  exact commutator_le_of_perfect_simple_core_action C.K1 (conjugate V k⁻¹)
    (F.H.pCoreIn 2) F.U
    (hAH.trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal))
    hnon (C.point_le.trans hHQ) (C.point_le.trans hHU) (hAH.trans hHU)
    ((pCoreIn_le 2 F.H).trans hHU) hAQ

/-- The source consequence: the component commutator with its own two-core
centralizes the whole abelian point span, hence the unchanged chosen seed. -/
theorem point_component_two_core_centralizes_of_moving
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L) (control : LocalControl C)
    (g : G) (hAT : conjugate V g ≤ (T : Subgroup G))
    (hmove : ⁅conjugate V g, V⁆ ≠ ⊥) :
    ⁅C.K1,C.K1.pCoreIn 2⁆ ≤ centralizer (F.U : Set G) ∧
      ⁅C.K1,C.K1.pCoreIn 2⁆ ≤ centralizer (V : Set G) := by
  have hcore : C.K1.pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C.K1)
      ((pCoreIn_le 2 C.K1).trans C.point_le)
      (((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal).trans
        (normalizer_le_normalizer_characteristic_image C.K1 (pCore 2 C.K1)))
  have hc := ((commutator_mono le_rfl hcore).trans
    (point_component_core_displacement_of_moving h hn earlier F hab C control g hAT hmove)).trans
      (le_centralizer_iff_isMulCommutative.mpr hab)
  exact ⟨hc,hc.trans (centralizer_le (le_conjugateSpanBy V F.H))⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
