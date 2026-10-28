module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.Recognition
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.CyclicFour

/-!
# The original cubic normalizer quotient is A₆

Apply the cubic-TI recognition to the literal elementary-nine Sylow quotient
and symmetric-four subgroup of the original source configuration.  All
normalizer, action, and TI hypotheses are discharged by the earlier source
construction, and the configuration and its marked actors remain unchanged.

Source: Aschbacher, *Sporadic Groups* (1994), 45.9 and Exercise 2, pp.247–249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
open Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
theorem quotient_equiv_alternating_six (c:SourceConfiguration h P) :
    Nonempty (NormalizerAction.Star c.V ≃* alternatingGroup (Fin 6)) := by
  let B := NormalizerAction.Star c.V
  let S : Subgroup B := c.quotientSylow
  obtain ⟨H,eH,hi⟩ := c.exists_symmetric_four_subgroup
  obtain ⟨eH⟩ := eH
  have hTI : ∀g:B, S ⊓ S.map (MulAut.conj g).toMonoidHom=⊥ ∨
      S.map (MulAut.conj g).toMonoidHom=S := by
    intro g
    by_cases hg:g∈normalizer (S:Set B)
    · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
    · exact Or.inl (disjoint_iff_inf_le.mp (c.quotientSylow_Ti g hg) |>.antisymm bot_le)
  let : IsElementaryAbelian 3 S := c.quotientSylow_elementary
  obtain ⟨hc, ⟨eN⟩⟩ := c.quotientSylow_cyclic_four_normalizer
  exact alternatingSix_of_symmetricFour_index_fifteen H eH hi c.quotientSylow
    c.quotientSylow_card hTI hc eN
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
/-- The actual source configuration has an alternating-six normalizer quotient. -/
theorem original_cubic_alternating_six (h:IsType z) (P:Sylow 3 (centralizer z)) :
    ∃c:CubicGeometry.SourceConfiguration h P,
      Nonempty (NormalizerAction.Star c.V ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c,c.quotient_equiv_alternating_six⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
