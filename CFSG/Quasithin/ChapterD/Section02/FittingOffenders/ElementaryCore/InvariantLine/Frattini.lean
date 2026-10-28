module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.InvariantLine
public import Theory.PGroupCore

/-!
# Eliminating the Frattini subgroup after central-line exclusion

The invariant-line detection theorem turns exclusion of every A-invariant
central subgroup of order three from Φ(P) into Φ(P) = 1. The finite p-group
Frattini criterion then makes P elementary abelian. The second theorem applies
this argument to the literal ambient subgroup O₃(G).

Source: Aschbacher--Smith, D.2.14(2), printed p.186. The explicit line-exclusion
premise is the module-support conclusion following (++); its proof belongs to
the independent support-exclusion branch. The elementary-core assembly must
discharge that premise before using this consumer as a source theorem.
-/

public section
namespace CFSG.Quasithin.ChapterD.ElementaryCore
open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The support-exclusion conclusion discharges the Frattini step of D.2.14(2). -/
theorem frattini_eq_bot_and_isElementaryAbelian_of_line_exclusion
    (P A : Subgroup G) (hP : IsPGroup 3 P)
    [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hn : A ≤ normalizer (P : Set G))
    (hexclude : ∀ Z : Subgroup G, Z ≤ (center P).map P.subtype →
      Nat.card Z = 3 → A ≤ normalizer (Z : Set G) →
      ¬ Z ≤ (frattini P).map P.subtype) :
    frattini P = ⊥ ∧ IsElementaryAbelian 3 P := by
  have hphi : frattini P = ⊥ := by
    by_contra hne
    obtain ⟨Z, hz, hcard, hnorm, hfrat⟩ :=
      exists_invariant_central_line_in_frattini P A hP hA hn hne
    exact hexclude Z hz hcard hnorm hfrat
  let : Fact (IsPGroup 3 P) := ⟨hP⟩
  exact ⟨hphi, frattini_eq_bot_iff_isElementaryAbelian.mp hphi⟩

/-- Literal O₃(G) application, with both intrinsic subgroup images preserved. -/
theorem pCore_frattini_eq_bot_and_isElementaryAbelian_of_line_exclusion
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 4)
    (hexclude : ∀ Z : Subgroup G,
      Z ≤ (center (pCore 3 G)).map (pCore 3 G).subtype →
      Nat.card Z = 3 → A ≤ normalizer (Z : Set G) →
      ¬ Z ≤ (frattini (pCore 3 G)).map (pCore 3 G).subtype) :
    frattini (pCore 3 G) = ⊥ ∧ IsElementaryAbelian 3 (pCore 3 G) := by
  exact frattini_eq_bot_and_isElementaryAbelian_of_line_exclusion
    (pCore 3 G) A pCore_isPGroup hA (by rw [normalizer_eq_top]; exact le_top) hexclude

end CFSG.Quasithin.ChapterD.ElementaryCore
