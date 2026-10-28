module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessRanks

/-!
# The geometric pair under the full M22 automizer rank bound

The selected elementary actor is a subgroup of the full original automizer.
Its rank is at least twice the field degree, so rank at most five leaves
only degrees one and two. All actors are those of the original selected pair.
Source: Aschbacher--Smith 8.2.2--3 and H.14.3(1), pp.714--716,397--398.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem original_actor_normalizes (s : GeometricSelected H T M V I k i S) :
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [← selected_actor_image I M V hVI S i s.twoConjugate]
  rintro _ ⟨a,ha,rfl⟩
  have hn := s.twoConjugate.sylow_le_normalizer (DihedralCubic.A_le_sylow s.twoConjugate ha)
  rw [←subgroupOf_normalizer_eq hVI] at hn
  exact hn

/-- The rank bound for the full automizer bounds the actual pair's degree. -/
theorem parameter_one_or_two_of_rank_five (s : GeometricSelected H T M V I k i S)
    (hr : primeRank 2 (Automizer V) ≤ 5) : k = 1 ∨ k = 2 := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (original_actor_normalizes s)
  have hu := (offender_rank_le_primeRank (inducedAutomizer V A)).trans hr
  have hl := s.actor_rank_ge_twice_parameter
  have hp := s.positive
  change rank (inducedAutomizer V A) ≥ 2*k at hl
  omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
