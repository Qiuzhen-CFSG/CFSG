module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.SmallOrders
public import CFSG.Quasithin.MainConverse.Transport
public import Theory.SpecificGroups.Tits.ThreeRank
public import Theory.SpecificGroups.Tits.ConverseLocalCores.First
public import Theory.SpecificGroups.Tits.ConverseLocalCores.Second
public import Theory.SpecificGroups.Tits.ConverseLocalCoverage

/-!
# The Tits branch of the quasithin converse

A concrete nonabelian Sylow three-subgroup of order 27 bounds three-rank
in the whole Tits group. Together with the checked order bounds away from
three, this proves quasithinness for the actual Parrott presentation.
Transport uses the certified Parrott–Atlas multiplicative equivalence.

The exhaustive Sylow double-coset cover and generation certificates identify
each maximal two-local containing the marked Sylow two-subgroup with one of
the two concrete parabolics. Their intrinsic two-cores are self-centralizing.
Sylow conjugacy and the same model equivalence therefore prove even
characteristic, with all local premises discharged.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2(1), printed pp.3–4 and 481–482;
Parrott, *A Characterization of the Tits' Simple Group* (1972), §5, p.683.
The disputed first-core and quotient invariants in F.1.12(I)(9) are not used.
-/

namespace CFSG.Quasithin.MainConverse.ExceptionalLocal

/-- The actual presented Tits group has three-rank at most two. -/
public theorem tits_threeRank_le_two : primeRank 3 Tits.ParrottGroup ≤ 2 := by
  rw [Theory.GroupTheory.primeRank_equiv 3 Tits.parrottFiniteImageEquiv]
  exact Tits.ThreeRank.rank_le_two

/-- Every maximal two-local has the required three-rank bound. -/
public theorem tits_maximalTwoLocal_threeRank_le_two (M : Subgroup Tits.ParrottGroup)
    (_hM : IsMaximalTwoLocal M) : primeRank 3 M ≤ 2 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3 M.subtype M.subtype_injective).trans
    tits_threeRank_le_two

/-- Quasithinness of the genuine Parrott presentation, with no local premises. -/
public theorem tits_quasithin : IsQuasithin Tits.ParrottGroup :=
  tits_quasithin_of_three_local_rank (MulEquiv.refl _)
    tits_maximalTwoLocal_threeRank_le_two

/-- The same unconditional rank bound for any isomorphic copy of the Tits group. -/
public theorem tits_model_threeRank_le_two {G : Type*} [Group G] [Finite G]
    (e : G ≃* Tits.ParrottGroup) : primeRank 3 G ≤ 2 := by
  rw [Theory.GroupTheory.primeRank_equiv 3 e]
  exact tits_threeRank_le_two

/-- Unconditional quasithinness is invariant under the actual model isomorphism. -/
public theorem tits_model_quasithin {G : Type*} [Group G] [Finite G]
    (e : G ≃* Tits.ParrottGroup) : IsQuasithin G :=
  Theory.GroupTheory.isQuasithin_of_equiv e.symm tits_quasithin

/-- Both concrete parabolics have self-centralizing intrinsic two-core. -/
public theorem tits_parabolics_characteristicTwo :
    HasCharacteristicTwo Tits.ExceptionalParabolics.first ∧
      HasCharacteristicTwo Tits.ExceptionalParabolics.second :=
  ⟨Tits.ConverseLocalCores.first_core_self_centralizing,
    Tits.ConverseLocalCores.second_core_self_centralizing⟩

/-- Exhaustive Sylow-local coverage and the two intrinsic core calculations
imply even characteristic. The unconditional theorem below supplies coverage. -/
public theorem tits_evenCharacteristic_of_sylow_local_coverage
    (hcover : ∀ M : Subgroup Tits.Atlas1600Group, IsMaximalTwoLocal M →
      Tits.atlas1600SylowTwoSubgroup ≤ M →
      M = Tits.ExceptionalParabolics.first ∨ M = Tits.ExceptionalParabolics.second) :
    IsEvenCharacteristic Tits.ParrottGroup := by
  apply IsEvenCharacteristic.of_equiv Tits.parrottFiniteImageEquiv.symm
  apply IsEvenCharacteristicAt.all (T := Tits.atlas1600SylowTwo)
  intro M hM hSM
  have hS : Tits.atlas1600SylowTwoSubgroup ≤ M := by
    simpa only [Tits.atlas1600SylowTwo_coe] using hSM
  rcases hcover M hM hS with rfl | rfl
  · exact tits_parabolics_characteristicTwo.1
  · exact tits_parabolics_characteristicTwo.2

/-- The actual Parrott presentation has even characteristic. The exhaustive
Sylow-local cover discharges the final local premise. -/
public theorem tits_evenCharacteristic : IsEvenCharacteristic Tits.ParrottGroup :=
  tits_evenCharacteristic_of_sylow_local_coverage
    Tits.ConverseLocalCoverage.maximalTwoLocal_eq_first_or_second

/-- Every group isomorphic to the actual Tits presentation has even characteristic. -/
public theorem tits_model_evenCharacteristic {G : Type*} [Group G] [Finite G]
    (e : G ≃* Tits.ParrottGroup) : IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e tits_evenCharacteristic

/-- Both local conditions of the quasithin converse hold for the actual Tits group. -/
public theorem tits_quasithin_evenCharacteristic :
    IsQuasithin Tits.ParrottGroup ∧ IsEvenCharacteristic Tits.ParrottGroup :=
  ⟨tits_quasithin, tits_evenCharacteristic⟩

/-- QT and even characteristic transport along an actual Tits model isomorphism. -/
public theorem tits_model_quasithin_evenCharacteristic
    {G : Type*} [Group G] [Finite G] (e : G ≃* Tits.ParrottGroup) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨tits_model_quasithin e, tits_model_evenCharacteristic e⟩

end CFSG.Quasithin.MainConverse.ExceptionalLocal
