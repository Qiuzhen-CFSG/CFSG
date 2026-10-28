module
public import Theory.GroupTheory.ElementaryNormalizerThreeRank
public import Theory.GroupTheory.PGroup.ElementaryNormalizer
public import Theory.GroupTheory.TwoLocalSurjective
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.TraceBound

/-!
# Three-parts of all two-locals in PSU₄(3)

The already proved centralizer bounds in elementary orders two, four and
sixteen, together with their automorphism orders, exclude 27 from every
elementary-two normalizer. The characteristic subgroup Ω₁(Z(Q)) embeds
each two-local normalizer in such a normalizer. This stronger order bound
is the model input for partial odd-center quotients in A.2.17.
Source: Aschbacher–Smith A.2.17 and Theorem 0.1.2(4), pp.39 and 4.
-/

open Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open ElementaryLocal

public theorem elementary_normalizer_three_part
    (A : Subgroup (Carrier 4)) (hA : A ≠ ⊥) (hEA : IsElementaryAbelian 2 A) :
    ¬ 3^3 ∣ Nat.card (normalizer (A : Set (Carrier 4))) := by
  have htrace := InvolutionCentralizer.trace_eq_zero_of_projective_involution
  apply A.three_cube_not_dvd_card_normalizer_of_elementary_centralizers hA hEA
    (elementary_card_le_sixteen htrace A hEA)
    (InvolutionCentralizer.centralizer_three_part_of_card_eq_two A) ?_
    (centralizer_not_three_dvd_of_card_eq_sixteen htrace A hEA)
  intro B _ hEB hB
  exact FourCentralizer.four_centralizer_not_nine_dvd_of_trace htrace B hEB hB

public theorem twoLocal_three_part
    (M : Subgroup (Carrier 4)) (hM : IsTwoLocal M) : ¬ 3^3 ∣ Nat.card M := by
  obtain ⟨Q,hQ,hQp,rfl⟩ := hM
  obtain ⟨A,hA,_,hEA,hle⟩ := Q.exists_nontrivial_elementary_with_normalizer_le hQp hQ
  intro hd
  exact elementary_normalizer_three_part A hA hEA (hd.trans (card_dvd_of_le hle))
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
