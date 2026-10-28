module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.Contracts
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.MiddleEight
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MarkedExtension
public import Theory.SpecificGroups.SymmetricEight.MarkedFlagTransport

/-!
# Both permutation markings of the binary middle node

Align the supplied middle-node basis with an actual A₈--GL₄(2) comparison.
The faithful action quotient extends that component equivalence to S₈.
The normalizer of the even pair stabilizer places the Sylow image in the
full pair stabilizer, and its odd element recovers the whole local image.
Thus one equivalence marks (M ∩ L)⁺ as the even pair stabilizer and M⁺ as
the full pair stabilizer. The latter contradicts the normal four-group.

The geometric node data and the exceptional pair comparison are explicit
premises here. They must be constructed before the source linear exclusion
is complete. No 15.3.28 configuration is treated as an input to 15.3.43.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the n = 1
paragraph of 15.3.43, printed p.1140. The extension argument also occurs in
15.3.28(3), printed p.1131.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- The component intersection and its full Sylow extension have different
permutation images. Both identities refer to the same equivalence. -/
structure MiddlePermutationMarking where
  equiv : c.toComponentAction.Quotient ≃* Equiv.Perm (Fin 8)
  component : (c.toComponentAction.image L).map equiv.toMonoidHom = alternatingGroup (Fin 8)
  component_intersection : (c.toComponentAction.image (M ⊓ L)).map equiv.toMonoidHom =
    Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer ⊓
      alternatingGroup (Fin 8)
  extended_intersection : (c.toComponentAction.image M).map equiv.toMonoidHom =
    Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer

open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals

private theorem component_equiv_of_comparison (h : MiddleNodeData c)
    (e₈ : alternatingGroup (Fin 8) ≃* LinearGroup 4) (b₈ : Basis 3)
    (hp : (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map e₈.toMonoidHom =
      minimalParabolic b₈ 1) :
    ∃ e : c.toComponentAction.image L ≃* alternatingGroup (Fin 8),
      ((c.toComponentAction.image (M ⊓ L)).subgroupOf
        (c.toComponentAction.image L)).map e.toMonoidHom =
          pairStabilizer.subgroupOf (alternatingGroup (Fin 8)) := by
  let g : LinearGroup 4 := h.basis.equiv b₈ (Equiv.refl _)
  have hb : h.basis.map g = b₈ := by ext i; simp [g]
  let e := h.linear.trans ((MulAut.conj g).trans e₈.symm)
  refine ⟨e, ?_⟩
  change (((c.toComponentAction.image (M ⊓ L)).subgroupOf
    (c.toComponentAction.image L)).map
      (e₈.symm.toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp h.linear.toMonoidHom))) = _
  rw [← map_map, ← map_map, h.intersection]
  have hg : (minimalParabolic h.basis 1).map (MulAut.conj g).toMonoidHom =
      minimalParabolic b₈ 1 := by
    unfold minimalParabolic
    rw [cutStabilizer_map_conj, hb]
  rw [hg]
  exact (map_symm_eq_iff_map_eq _).mpr hp

/-- Extend the geometric component marking to the actual action quotient and
recover the whole local image by its odd Sylow element. -/
theorem middle_marking_of_comparison (h : MiddleNodeData c)
    (e₈ : alternatingGroup (Fin 8) ≃* LinearGroup 4) (b₈ : Basis 3)
    (hp : (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map e₈.toMonoidHom =
      minimalParabolic b₈ 1) : Nonempty (MiddlePermutationMarking c) := by
  let d := c.toComponentAction
  let K := d.image L
  let J := d.image (M ⊓ L)
  let Q := d.image M
  let T := d.image S
  have hK : K ≠ ⊤ := by
    intro ht
    apply h.outer
    change T ≤ K
    rw [ht]
    exact le_top
  let : Group.IsPerfect L := SporadicModels.reduced_component_perfect c
  have hc : centralizer (K : Set d.Quotient) = ⊥ :=
    SporadicModels.component_image_centralizer_eq_bot d
  obtain ⟨eK, heK⟩ := component_equiv_of_comparison c h e₈ b₈ hp
  let e : d.Quotient ≃* S8 := symmetricExtension K eK hc hK
  have heL : K.map e.toMonoidHom = alternatingGroup (Fin 8) :=
    symmetricExtension_map K eK hc hK
  have hJK : J ≤ K := map_mono (comap_mono inf_le_right)
  have hcomm : e.toMonoidHom.comp K.subtype =
      (alternatingGroup (Fin 8)).subtype.comp eK.toMonoidHom := by
    apply MonoidHom.ext
    intro k
    exact symmetricExtension_on_subgroup K eK hc hK k
  have heJ : J.map e.toMonoidHom = pairStabilizer ⊓ alternatingGroup (Fin 8) := by
    calc
      J.map e.toMonoidHom = ((J.subgroupOf K).map K.subtype).map e.toMonoidHom := by
        rw [map_subgroupOf_eq_of_le hJK]
      _ = ((J.subgroupOf K).map eK.toMonoidHom).map (alternatingGroup (Fin 8)).subtype := by
        rw [map_map, hcomm, ← map_map]
      _ = pairStabilizer ⊓ alternatingGroup (Fin 8) := by
        rw [heK, subgroupOf_map_subtype]
  have hTN : T ≤ normalizer (J : Set d.Quotient) := by
    change d.image S ≤ normalizer (d.image (M ⊓ L) : Set d.Quotient)
    rw [quotient_intersection_eq c]
    exact ParabolicInspection.quotient_sylow_normalizes_intersection c
  have heT : T.map e.toMonoidHom ≤ pairStabilizer := by
    have hh := (map_mono hTN).trans (J.le_normalizer_map e.toMonoidHom)
    rwa [heJ, normalizer_evenPair] at hh
  have hodd : ¬ T.map e.toMonoidHom ≤ alternatingGroup (Fin 8) := by
    intro ht
    apply h.outer
    intro x hx
    have hxmap : e x ∈ K.map e.toMonoidHom := by
      rw [heL]
      exact ht ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hey⟩ := hxmap
    exact e.injective hey ▸ hy
  refine ⟨⟨e, heL, heJ, ?_⟩⟩
  rw [quotient_local_eq_sup c, Subgroup.map_sup, heJ]
  exact evenPair_sup_of_odd heT hodd

/-- The genuine middle-node marking contradicts the original normal four-group. -/
theorem false_of_middle_node_comparison (h : MiddleNodeData c)
    (e₈ : alternatingGroup (Fin 8) ≃* LinearGroup 4) (b₈ : Basis 3)
    (hp : (pairStabilizer.subgroupOf (alternatingGroup (Fin 8))).map e₈.toMonoidHom =
      minimalParabolic b₈ 1) : False := by
  obtain ⟨mark⟩ := middle_marking_of_comparison c h e₈ b₈ hp
  exact not_middle_eight c mark.equiv mark.extended_intersection

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
