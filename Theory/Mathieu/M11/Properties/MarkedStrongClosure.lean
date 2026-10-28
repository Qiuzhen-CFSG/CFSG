module

public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.SpecificGroups.OddCharacteristic.InvolutionFusion

/-!
# Returning conjugates of a marked M₁₁ involution

The actual semidihedral Sylow presentation supplies two involutions whose
product has order four. Transfer them to the supplied Sylow subgroup, then
use the proved single involution class to put both in the marked class.
Only this pair is needed by the central-two quotient strong-closure argument.

Source: Aschbacher--Smith 1.1.5(3)(f), pp.501--503, and the Bender inspection
in Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
-/

public section
namespace Sporadic.Mathieu

/-- Every marked involution has noncommuting conjugates in the supplied
Sylow two-subgroup. No additional fusion or pair hypothesis is required. -/
theorem m11_sylow_noncommuting_conjugates (R : Sylow 2 M11)
    (v : M11) (hv : orderOf v = 2) :
    ∃ a b : R, IsConj v (a : M11) ∧ IsConj v (b : M11) ∧ ¬Commute a b := by
  obtain ⟨P, r, s, hr, hs, hrel, _⟩ := m11_exists_semidihedral_sylow
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Theory.GroupTheory.OddCharacteristicInvolutionFusion.semidihedral_pair r s hr hs hrel
  let e := P.equiv R
  have hea : orderOf (e a : M11) = 2 := by
    rw [Subgroup.orderOf_coe, e.orderOf_eq]
    exact ha
  have heb : orderOf (e b : M11) = 2 := by
    rw [Subgroup.orderOf_coe, e.orderOf_eq]
    exact hb
  refine ⟨e a, e b, m11_involutions_isConj v _ hv hea,
    m11_involutions_isConj v _ hv heb, ?_⟩
  intro hc
  apply hab
  have hh := hc.map e.symm.toMonoidHom
  change Commute (e.symm (e a)) (e.symm (e b)) at hh
  simpa only [e.symm_apply_apply] using hh

end Sporadic.Mathieu
