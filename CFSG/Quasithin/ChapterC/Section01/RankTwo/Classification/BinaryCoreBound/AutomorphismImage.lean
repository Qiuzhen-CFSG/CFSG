module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.ThreeAutomorphisms

/-!
# The binary MS quotient as an actual automorphism subgroup

Transport the component-quotient conjugation action through the given matrix
isomorphism and the canonical matrix-to-linear-map comparison. The component
maps onto all inner automorphisms. The proved automorphism coverage then gives
exactly two possible images: the inner group or the full automorphism group.
Every identification retains the actual conjugation map.

Source: Aschbacher–Smith, C.1.32 proof, printed pp.135–136. Eliminating the
outer alternative needs the failure-of-factorization argument and is not
asserted here.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup BinaryLinear.OuterCyclic
universe u
variable {J : Type u} [Group J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

/-- The specified matrix quotient, followed by its actual linear action. -/
noncomputable def Input.linearQuotientEquiv : (L ⧸ pCore 2 L) ≃* LinearGroup 3 :=
  h.quotientEquiv.trans (slEquivLinear 3)

variable [Finite J]

/-- Ambient conjugation, transported to the binary linear group. -/
noncomputable def Input.linearAction : J →* MulAut (LinearGroup 3) :=
  (MulAut.congr h.linearQuotientEquiv).toMonoidHom.comp h.quotientAction

/-- The transported action is compatible with quotient conjugation. -/
theorem Input.linearAction_apply (j : J) (x : L ⧸ pCore 2 L) :
    h.linearAction j (h.linearQuotientEquiv x) =
      h.linearQuotientEquiv (h.quotientAction j x) := by
  change h.linearQuotientEquiv (h.quotientAction j
    (h.linearQuotientEquiv.symm (h.linearQuotientEquiv x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Changing to the concrete model does not change the action kernel. -/
theorem Input.linearAction_kernel : h.linearAction.ker = pCore 2 J := by
  rw [← h.quotientAction_kernel]
  ext j
  exact (MulAut.congr h.linearQuotientEquiv).map_eq_one_iff

/-- Component elements induce precisely their inner automorphisms. -/
theorem Input.linearAction_component (l : L) :
    h.linearAction l =
      MulAut.conj (h.linearQuotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) := by
  change MulAut.congr h.linearQuotientEquiv (h.quotientAction l) = _
  rw [h.quotientAction_component, MulAut.congr_conj]

/-- The image of the given component is the whole inner subgroup. -/
theorem Input.linearAction_component_image :
    L.map h.linearAction = MulAut.innerSubgroup (LinearGroup 3) := by
  apply le_antisymm
  · rintro a ⟨l, hl, rfl⟩
    exact ⟨h.linearQuotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩),
      (h.linearAction_component ⟨l, hl⟩).symm⟩
  · rintro a ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := h.linearQuotientEquiv.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) y
    exact ⟨l, l.property, h.linearAction_component l⟩

/-- The literal two-core quotient is the actual binary conjugation image. -/
noncomputable def Input.linearQuotientEquivRange :
    (J ⧸ pCore 2 J) ≃* h.linearAction.range :=
  (QuotientGroup.quotientMulEquivOfEq h.linearAction_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange h.linearAction)

/-- The equivalence is induced by the original conjugation homomorphism. -/
theorem Input.linearQuotientEquivRange_mk (j : J) :
    (h.linearQuotientEquivRange (QuotientGroup.mk' (pCore 2 J) j) :
      MulAut (LinearGroup 3)) = h.linearAction j := by
  rfl

/-- Automorphism coverage gives two actual subgroup images; it does not
eliminate the graph-automorphism branch. -/
theorem Input.linearAction_range_cases :
    h.linearAction.range = MulAut.innerSubgroup (LinearGroup 3) ∨
      h.linearAction.range = ⊤ := by
  classical
  have hi : MulAut.innerSubgroup (LinearGroup 3) ≤ h.linearAction.range := by
    rw [← h.linearAction_component_image]
    exact map_le_range h.linearAction L
  by_cases hle : h.linearAction.range ≤ MulAut.innerSubgroup (LinearGroup 3)
  · exact Or.inl (le_antisymm hle hi)
  · right
    obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hle
    obtain ⟨g, hg | hg⟩ :=
      BinaryLinear.InvariantNodeActions.ThreeAutomorphisms.inner_graph a
    · exact (hna ⟨g, hg.symm⟩).elim
    · have hgraph : graphLinear 3 ∈ h.linearAction.range := by
        have hm := h.linearAction.range.mul_mem ha
          (h.linearAction.range.inv_mem (hi ⟨g, rfl⟩))
        simpa only [hg, mul_inv_cancel_right] using hm
      apply eq_top_iff.mpr
      intro b _
      obtain ⟨x, hx | hx⟩ :=
        BinaryLinear.InvariantNodeActions.ThreeAutomorphisms.inner_graph b
      · exact hi ⟨x, hx.symm⟩
      · rw [hx]
        exact h.linearAction.range.mul_mem hgraph (hi ⟨x, rfl⟩)

end CFSG.Quasithin.ChapterC.BinaryMS
