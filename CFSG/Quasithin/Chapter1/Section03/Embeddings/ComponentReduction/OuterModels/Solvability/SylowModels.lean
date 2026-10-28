module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability.SylowSource
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.LocalOrder

/-!
# Literal Held/Rudvalis Sylow inputs for the full Theorem C companion

The fixed Held representative is Sylow by its proved two-group and
self-normalizing properties. The fixed Rudvalis candidate is Sylow by its
proved order and the ambient two-part bound. Thus solvability of their actual
Sylow automorphism groups, together with the proved S₂ fixer theorem, gives
the guarded model conclusions needed by the full Theorem C proof.

Model simplicity is inherited inside the actual source branch. Neither
intrinsic model simplicity nor full automorphism realization is required.
The two local Aut(P) solvability inputs remain explicit pending the finite
profile proofs. The final theorem preserves the literal L/O(L) quotient and
perfect-actor action of Aschbacher--Smith A.3.9, pp.45--46.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory

/-- The actual Held representative supplies a Sylow subgroup to S₂. -/
public theorem held_outer_isSolvable_of_representative_aut
    (hAut : Group.IsSolvable (MulAut
      Held.LocalPairs.SylowGeometry.Calculations.representative))
    [IsSimpleGroup Held.He] : Group.IsSolvable (MulAut.Outer Held.He) := by
  obtain ⟨P, hP⟩ := Held.LocalPairs.SylowGeometry.Calculations.exists_representative_sylow
    Held.LocalPairs.SylowGeometry.Calculations.representative_isPGroup
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.normalizer_eq
  let : Group.IsSolvable (MulAut P) := by
    rw [hP]
    exact hAut
  exact simple_outer_isSolvable_of_sylowAut P

/-- The actual Rudvalis candidate supplies a Sylow subgroup to S₂, using
only its proved order and the ambient two-part bound. -/
public theorem rudvalis_outer_isSolvable_of_candidate_aut
    (hAut : Group.IsSolvable (MulAut
      Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate))
    [IsSimpleGroup Rudvalis.Model] :
    Group.IsSolvable (MulAut.Outer Rudvalis.Model) := by
  let C := Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate
  have hi : ¬ 2 ∣ C.index := by
    intro h
    apply Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
    rw [← C.card_mul_index]
    change 2 ^ 15 ∣ Nat.card
      Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate * C.index
    rw [Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate_card]
    exact Nat.mul_dvd_mul_left 16384 h
  let P : Sylow 2 Rudvalis.Model :=
    Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder.candidate_isTwoGroup.toSylow hi
  let : Group.IsSolvable (MulAut P) := hAut
  exact simple_outer_isSolvable_of_sylowAut P

/-- The complete Theorem C model list from two literal local automorphism
inputs. The guarded helper uses simplicity only in the matching branch. -/
public theorem theoremC_outer_isSolvable_of_model_sylowAut
    (hHeld : Group.IsSolvable (MulAut
      Held.LocalPairs.SylowGeometry.Calculations.representative))
    (hRu : Group.IsSolvable (MulAut
      Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate))
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hS : Section02.LocalModels.TheoremCModel S) :
    Group.IsSolvable (MulAut.Outer S) := by
  apply theoremC_outer_isSolvable_of_simple_model_inputs
    (fun hs => by
      let : IsSimpleGroup Held.He := hs
      exact held_outer_isSolvable_of_representative_aut hHeld)
    (fun hs => by
      let : IsSimpleGroup Rudvalis.Model := hs
      exact rudvalis_outer_isSolvable_of_candidate_aut hRu) hS

/-- The actual A.3.9 consumer of the two literal Sylow automorphism inputs. -/
public theorem perfect_actor_sup_oddCore_quotient_centralizer_of_model_sylowAut
    (hHeld : Group.IsSolvable (MulAut
      Held.LocalPairs.SylowGeometry.Calculations.representative))
    (hRu : Group.IsSolvable (MulAut
      Rudvalis.SylowOvergroups.RadicalCoverage.SylowCertificate.candidate))
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (L : Subgroup G) [L.Normal]
    (hQ : IsQuasisimple (L ⧸ pPrimeCore 2 L))
    (hmodel : Section02.LocalModels.TheoremCModel
      ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))) :
    L ⊔ (normalQuotientAction L (pPrimeCore 2 L)).ker = ⊤ := by
  apply perfect_actor_sup_oddCore_quotient_centralizer_of_simple_model_inputs
    (fun hs => by
      let : IsSimpleGroup Held.He := hs
      exact held_outer_isSolvable_of_representative_aut hHeld)
    (fun hs => by
      let : IsSimpleGroup Rudvalis.Model := hs
      exact rudvalis_outer_isSolvable_of_candidate_aut hRu) L hQ hmodel

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
