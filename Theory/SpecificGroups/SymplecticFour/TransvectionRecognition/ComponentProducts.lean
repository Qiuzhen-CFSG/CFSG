module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionProducts
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.SocleReduction

/-!
# Commuting-coset input to the actual component conclusion

The G.4.9 geometric construction needs to produce two commuting transvections
in one component coset, with different displacement lines. Their product is
then the c₂ involution required by the existing one-centralizer theorem.
This application keeps the literal inclusions K ≤ H ≤ Sp₄(F); it does not
assume either transvection belongs to K. The zero Fitting-core premise has
an independent original E.2.7 producer in SourceQuadraticOddCore, and the
existence of the marked pair remains with the geometric assembly.

Source: Aschbacher--Smith G.4.9, printed pp.341--342.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal commuting-coset output closes the one-c₂ component step. -/
theorem simple_socle_of_component_commuting_transvections {n : ℕ}
    (hF : Nat.card F=2^n) (H : Subgroup (Sp F)) (K : Subgroup H)
    (hK : IsComponent H K) (hfit : fittingSubgroup H=⊥)
    (a b : H) (ha : IsB1 (a : Sp F)) (hb : IsB1 (b : Sp F))
    (hab : Commute a b) (hne : movedSpace (a : Sp F)≠movedSpace (b : Sp F))
    (hcoset : a⁻¹*b∈K) :
    generalizedFitting H=K ∧ IsSimpleGroup K := by
  have hai : a⁻¹=a := by
    apply H.subtype_injective
    change (a : Sp F)⁻¹=(a : Sp F)
    exact inv_eq_iff_mul_eq_one.mpr (by
      simpa only [ha.1,pow_two] using pow_orderOf_eq_one (a : Sp F))
  have ht : a*b∈K := by simpa only [hai] using hcoset
  have hc : IsC2 ((a*b : H) : Sp F) :=
    isC2_product_of_commute_distinct_movedSpace (F:=F) (a : Sp F) (b : Sp F)
      ha hb (hab.map H.subtype) hne
  exact simple_socle_of_component_contains_isC2 (F:=F) hF H K hK hfit (a*b) ht hc

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
