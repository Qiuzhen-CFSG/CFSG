module

public import Theory.SpecificGroups.ReeTwo.FixingNonsplitFirstCore
public import Theory.SpecificGroups.ReeTwo.FixingActionStandardization

/-!
# The nonstandard split fixing orbit

The nonstandard half of the fixing census reduces to base action two without
changing the marked involution or the split fourth power. A fixed-mark
certificate for that one first core therefore applies to every nonstandard
split extension. The base-two certificate is an explicit premise here.

Source: Shinoda (1975), pp.81–83, via the checked census and marked model
reduction. The first core is intrinsically the centralizer of the second center.
-/

namespace ReeTwo.FixingModel
open Core.FixingActionCensus

/-- Exactly the nonstandard census entries reduce to base two. -/
public theorem baseIndex_eq_two_of_not_standard (i : Fin 20) (hi : ¬ IsStandard i) :
    baseIndex i = 2 :=
  (by decide +kernel : ∀ i : Fin 20, ¬ IsStandard i → baseIndex i = 2) i hi

/-- A fixed-mark certificate for the split base-two model covers the whole
nonstandard split orbit. -/
public theorem nonstandard_fixed_of_two_certificate
    (htwo : ∀ a : MulAut (firstCore 2 false),
      a (centralInvolution 2 false) = centralInvolution 2 false)
    (i : Fin 20) (hi : ¬ IsStandard i) (a : MulAut (firstCore i false)) :
    a (centralInvolution i false) = centralInvolution i false := by
  obtain ⟨e, he⟩ := exists_marked_base_equiv i false
  apply fixed_of_marked_equiv e he _ a
  rw [baseIndex_eq_two_of_not_standard i hi]
  exact htwo

end ReeTwo.FixingModel

namespace ReeTwo.FixingExtension
open Core.FixingActionCensus

/-- Transport the split base-two obstruction to any actual generated
extension with a nonstandard census action. -/
public theorem nonstandard_firstCore_obstruction_of_two_certificate
    (htwo : ∀ a : MulAut (FixingModel.firstCore 2 false),
      a (FixingModel.centralInvolution 2 false) = FixingModel.centralInvolution 2 false)
    {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 4096) (j : Core →* H) (s : H)
    (i : Fin 20) (hi : ¬ IsStandard i)
    (hgen : j.range ⊔ Subgroup.zpowers s = ⊤)
    (hconj : ∀ q, s * j q * s⁻¹ = j (representative i q))
    (hfour : s ^ 4 = 1) :
    ∃ hz : j (Core.root 9) ∈ firstCore H,
      ∀ a : MulAut (firstCore H),
        a ⟨j (Core.root 9), hz⟩ = ⟨j (Core.root 9), hz⟩ := by
  refine ⟨root_nine_mem_firstCore j s (representative i) hgen hconj, ?_⟩
  intro a
  have hε : s ^ 4 = j (CyclicFourCentralExtension.mark false) := by
    simpa [CyclicFourCentralExtension.mark] using hfour
  let e : FixingModel.Model i false ≃* H :=
    CyclicFourCentralExtension.equiv j s hconj hε hcard hgen
  apply root_nine_fixed_of_marked_equiv j _ e.symm
    (FixingModel.centralInvolution i false) ?_ ?_ a
  · apply e.injective
    rw [e.apply_symm_apply]
    exact (CyclicFourCentralExtension.equiv_root_nine j s hconj hε hcard hgen).symm
  · exact FixingModel.nonstandard_fixed_of_two_certificate htwo i hi

end ReeTwo.FixingExtension
