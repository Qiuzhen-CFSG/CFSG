module

public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Mathlib.GroupTheory.Sylow

/-!
# Characteristic p in Sylow overgroups inside a parabolic

Let S be an ambient Sylow p-subgroup and S ≤ X ≤ P. A normal p-subgroup
Q of P lies in the restriction of S to P, hence in X. If Q contains its
ambient centralizer, it therefore forces O_p(X) to contain its intrinsic
centralizer and F*(X) = O_p(X). No solvability of X or P is required.

This is the finite-group step in the defining-characteristic parabolic
argument of Aschbacher–Smith B.1.13, printed p.74, and GLS III, 2.6.5(e).
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

/-- A normal p-subgroup of an overgroup of S lies in that specified S. -/
theorem normalized_pSubgroup_le_sylow (S : Sylow p G) (P Q : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hQP : Q ≤ P)
    (hPN : P ≤ normalizer (Q : Set G)) (hQ : IsPGroup p Q) :
    Q ≤ (S : Subgroup G) := by
  let : (Q.subgroupOf P).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQP).mpr hPN
  have hQ' : IsPGroup p (Q.subgroupOf P) := hQ.comap_subtype
  have h := hQ'.le_sylow_of_normal (S.subtype hSP)
  intro q hq
  exact h (show (⟨q, hQP hq⟩ : P) ∈ Q.subgroupOf P from hq)

/-- Restriction of a self-centralizing parabolic radical to any Sylow overgroup. -/
theorem centralizer_pCore_le_of_sylow_le_normalizer
    (S : Sylow p G) (X P Q : Subgroup G)
    (hSX : (S : Subgroup G) ≤ X) (hXP : X ≤ P) (hQP : Q ≤ P)
    (hPN : P ≤ normalizer (Q : Set G)) (hQ : IsPGroup p Q)
    (hc : centralizer (Q : Set G) ≤ Q) :
    centralizer (pCore p X : Set X) ≤ pCore p X :=
  centralizer_pCore_le_of_normalized p Q X hQ
    ((normalized_pSubgroup_le_sylow S P Q (hSX.trans hXP) hQP hPN hQ).trans hSX)
    (hXP.trans hPN) hc

/-- The intrinsic generalized Fitting calculation needs no solvability premise. -/
theorem generalizedFitting_eq_pCore_of_sylow_le_normalizer [Finite G] [Fact p.Prime]
    (S : Sylow p G) (X P Q : Subgroup G)
    (hSX : (S : Subgroup G) ≤ X) (hXP : X ≤ P) (hQP : Q ≤ P)
    (hPN : P ≤ normalizer (Q : Set G)) (hQ : IsPGroup p Q)
    (hc : centralizer (Q : Set G) ≤ Q) :
    generalizedFitting X = pCore p X :=
  generalizedFitting_eq_pCore_of_selfCentralizing p
    (centralizer_pCore_le_of_sylow_le_normalizer S X P Q hSX hXP hQP hPN hQ hc)

end Theory.GroupTheory
