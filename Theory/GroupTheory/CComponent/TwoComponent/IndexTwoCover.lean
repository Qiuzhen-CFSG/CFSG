module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.GeneralizedFitting.IndexTwoCover

/-!
# Two-components in quasisimple extensions of index two

A C-component is perfect, so it lies in every subgroup of index two.
If that subgroup is normal and quasisimple, it is itself a C-component;
minimality then identifies the two. In particular every two-component is
quasisimple, even when the ambient odd core is nontrivial.

This supplies the B₂ argument for the `3.A₇.2` outer Held row in GLS3,
Table 5.3p, using the definition of B₂ in GLS II, Definition 2.4.
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup.IsCComponent

variable {G : Type*} [Group G] {K L : Subgroup G}

/-- A normal quasisimple subgroup of index two is the unique C-component. -/
theorem eq_of_index_two_quasisimple (hK : K.IsCComponent)
    [L.Normal] [IsQuasisimple L] (hi : L.index = 2) : K = L := by
  let := hK.perfect
  exact hK.eq_of_le (IsComponent.isCComponent
    ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩)
    (le_of_isPerfect_of_index_eq_two K L hi)

end Subgroup.IsCComponent

namespace Theory.GroupTheory.HasQuasisimpleNormalOfIndexTwo

variable {G : Type*} [Group G] {z : ℕ}

/-- The actual index-two covering row makes every two-component quasisimple. -/
theorem isQuasisimple_of_isTwoComponent
    (h : HasQuasisimpleNormalOfIndexTwo G z)
    {K : Subgroup G} (hK : K.IsTwoComponent) : IsQuasisimple K := by
  obtain ⟨L, hn, hq, hi, _⟩ := h
  let := hn
  let := hq
  exact hK.1.eq_of_index_two_quasisimple hi ▸ hq

end Theory.GroupTheory.HasQuasisimpleNormalOfIndexTwo
