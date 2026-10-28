module

public import Theory.GroupTheory.PGroup.NormalIndexTwoStep
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Soundness of normal elementary extension checks

A family containing bottom covers the normal elementary subgroups of a finite
2-group if it is closed under the normal elementary one-element extensions.
To prove this, choose a largest represented normal subgroup inside the target.
If it is smaller than the target, a normal step of relative index two supplies
one new generator. Elementary abelianness passes down from the target, so the
checked extension contradicts maximality.

The element family only needs to be surjective. No subgroup enumeration,
ambient order formula, or normality of arbitrary intermediate subgroups is
assumed. Normality in this argument always refers to the same ambient 2-group.

Source: the normal-index-two step for finite 2-groups in
`Theory.GroupTheory.PGroup.NormalIndexTwoStep`.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open Subgroup

/-- Finite element coverage and local extension checks imply exact subgroup coverage. -/
public theorem eq_node_of_normal_elementary_extensions {G : Type*} [Group G] [Finite G] {ι κ : Type*}
    (hp : IsPGroup 2 G) (K : ι → Subgroup G) (elt : κ → G)
    (hcover : Function.Surjective elt)
    (hbot : ∃ i, K i = ⊥)
    (hstep : ∀ i n, (K i ⊔ zpowers (elt n)).Normal →
      IsElementaryAbelian 2 ↥(K i ⊔ zpowers (elt n)) →
      ∃ j, K i ⊔ zpowers (elt n) = K j)
    (R : Subgroup G) (hn : R.Normal) (he : IsElementaryAbelian 2 R) :
    ∃ i, R = K i := by
  classical
  let : R.Normal := hn
  let : IsElementaryAbelian 2 R := he
  let good : Subgroup G → Prop := fun H => H ≤ R ∧ H.Normal ∧ ∃ i, H = K i
  have hbase : good ⊥ := by
    obtain ⟨i, hi⟩ := hbot
    exact ⟨bot_le, inferInstance, i, hi.symm⟩
  obtain ⟨H, _, hmax⟩ := Finite.exists_le_maximal hbase
  obtain ⟨hHR, hHn, i, hi⟩ := hmax.1
  let : H.Normal := hHn
  by_cases hEq : H = R
  · exact ⟨i, hEq.symm.trans hi⟩
  obtain ⟨X, hXn, hHX, hXR, hindex⟩ :=
    exists_normal_index_two_step G hp H R (lt_of_le_of_ne hHR hEq)
  obtain ⟨x, hxX, hxH, hcosets⟩ :=
    relIndex_eq_two_iff_exists_notMem_and.mp hindex
  have hX : H ⊔ zpowers x = X := by
    apply le_antisymm (sup_le hHX (zpowers_le.mpr hxX))
    intro y hy
    rcases hcosets y hy with h | h
    · have hm := (H ⊔ zpowers x).mul_mem (mem_sup_left h)
        (mem_sup_right ((zpowers x).inv_mem (mem_zpowers x)))
      simpa using hm
    · exact mem_sup_left h
  have hXe : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le hXR
  obtain ⟨n, rfl⟩ := hcover x
  have hext : K i ⊔ zpowers (elt n) = X := by
    rw [← hi]
    exact hX
  have hj : ∃ j, X = K j := by
    cases hext
    exact hstep i n hXn hXe
  have hXH : X ≤ H := hmax.2 ⟨hXR, hXn, hj⟩ hHX
  exact (hxH (hXH hxX)).elim

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
