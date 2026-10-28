module

public import Theory.GroupTheory.GeneralizedFitting.OneCentralizer
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootSocle

/-!
# The one-c₂ component step of transvection recognition

For a literal subgroup H of Sp₄(F), a component containing a c₂ involution is
the unique component: that involution has a two-group centralizer, whereas a
second component would be a nontrivial perfect subgroup of that centralizer.
If F(H)=1, the chosen component is therefore the actual simple F*(H).

This supplies the last implication in the stable-component branch of
Aschbacher--Smith G.4.9, printed p.342.  It does not construct the c₂ element
inside the component or eliminate the odd Fitting subgroup.  In particular it
uses one specified involution, so it also applies when H contains
transvections.  No transvection is assumed to lie in the component; the binary
component can be Sp₄(2)' ≅ A₆.
-/

public section

open Subgroup Theory.GroupTheory

namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition

open InvolutionTypes

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The exact one-involution component conclusion used in G.4.9.  The output
keeps the original inclusions K ≤ H ≤ Sp₄(F). -/
theorem simple_socle_of_component_contains_isC2 {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (H : Subgroup (Sp F)) (K : Subgroup H)
    (hK : IsComponent H K) (hfit : fittingSubgroup H = ⊥)
    (t : H) (ht : t ∈ K) (htype : IsC2 (t : Sp F)) :
    generalizedFitting H = K ∧ IsSimpleGroup K := by
  have hp := TwoConjugate.isPGroup_centralizer_of_isC2 hF (t : Sp F) htype
  have he : centralizer ({t} : Set H) =
      (centralizer ({(t : Sp F)} : Set (Sp F))).comap H.subtype := by
    ext x
    rw [mem_centralizer_singleton_iff, mem_comap,
      mem_centralizer_singleton_iff, ← Subtype.coe_inj]
    rfl
  have hC : IsPGroup 2 (centralizer ({t} : Set H)) := by
    rw [he]
    exact hp.comap_subtype
  exact hK.generalizedFitting_eq_and_simple_of_mem_prime_power_centralizer hfit t ht hC

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
