module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.SourceModel
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Fusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup

/-!
# The corrected nonsingular marking on the original chosen orbit

The chosen module supplies the inclusion T ≤ N_G(L). Apply the corrected
H.9 adapted-vector theorem to the image of that original Sylow in the
literal normalizer action quotient, then lift its Sylow centralizer. The
result is the actual C_T(w') in C_{N_G(L)}(w'), for an L-conjugate w' of w.

This is the setup for the ambient 12.1.1 argument, not a proof that C_G(w)
lies in N_G(L). The compatible source-model construction remains explicit;
its producer and the ambient source arguments are discharged by the
centralizer assembly owner.
Source: Aschbacher--Smith, printed p.788, with the corrected H.9 marking.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open scoped IsMulCommutative
public section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The corrected relative Sylow conclusion for the original chosen T. -/
theorem doubleNatural_adapted_nonsingular_of_sourceModel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ _S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 →
      ∃ l : L, ∃ w' : componentOrbit V (T : Subgroup G),
        (w' : G) = (l : G) * (w : G) * (l : G)⁻¹ ∧
        B.quadratic (Additive.ofMul w') = 1 ∧
        Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(w' : G)} : Set G))
          (normalizer (L : Set G) ⊓ centralizer ({(w' : G)} : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let M := normalizer (L : Set G)
  let P : Sylow 2 M := T.subtype D.sylow_normalizes_component
  obtain ⟨l, w', he, hq, hP, _⟩ := S.adapted_pair P w hw ⊥ (IsPGroup.of_subsingleton 2 _) bot_le
  refine ⟨l, w', he, hq, ?_⟩
  have hs := (Chapter1.IsSylowIn.map_iff M.subtype M.subtype_injective).mpr hP
  rw [map_inf _ _ _ M.subtype_injective] at hs
  have hPM : (P : Subgroup M).map M.subtype = (T : Subgroup G) := by
    exact map_subgroupOf_eq_of_le D.sylow_normalizes_component
  rw [hPM, subgroupOf_map_subtype] at hs
  rw [inf_comm (centralizer ({(w' : G)} : Set G)) M, ← inf_assoc] at hs
  have hTM : (T : Subgroup G) ⊓ M = (T : Subgroup G) :=
    inf_eq_left.mpr D.sylow_normalizes_component
  rw [hTM] at hs
  exact hs

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
