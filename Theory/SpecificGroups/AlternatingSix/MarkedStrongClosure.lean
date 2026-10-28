module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.OddCharacteristic.InvolutionFusion

/-!
# Returning conjugates of an A₆ involution

Every Sylow two-subgroup of the actual six-point alternating group is D₈.
Its two standard reflections are noncommuting involutions. The single
involution class in A₆ places both in the class of any marked involution,
giving the pair required by the marked strong-closure obstruction.

Source: Aschbacher--Smith 1.1.5(3)(a), pp.501--503, and Proposition 2.2.2,
pp.519--520 (combined 1 March 2004 manuscript). This is the inner A₆ case,
including the PSp₄(2)′ and PSL₂(9) overlaps.
-/

public section

namespace AlternatingSix.ShadowLocal

/-- Every involution has two noncommuting conjugates in the supplied Sylow
two-subgroup of A₆. The marked involution need not lie in that Sylow. -/
theorem sylow_noncommuting_conjugates (R : Sylow 2 A6) (v : A6)
    (hv : orderOf v = 2) :
    ∃ a b : R, IsConj v (a : A6) ∧ IsConj v (b : A6) ∧ ¬Commute a b := by
  obtain ⟨e⟩ := alternatingSylow_dihedral R
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Theory.GroupTheory.OddCharacteristicInvolutionFusion.dihedral_pair
      (show 4 ≤ 4 by decide)
  have hea : orderOf (e.symm a : A6) = 2 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq]
    exact ha
  have heb : orderOf (e.symm b : A6) = 2 := by
    rw [Subgroup.orderOf_coe, e.symm.orderOf_eq]
    exact hb
  refine ⟨e.symm a, e.symm b, involutions_isConj v _ hv hea,
    involutions_isConj v _ hv heb, ?_⟩
  intro hc
  apply hab
  have hh := hc.map e.toMonoidHom
  change Commute (e (e.symm a)) (e (e.symm b)) at hh
  simpa only [e.apply_symm_apply] using hh

end AlternatingSix.ShadowLocal

