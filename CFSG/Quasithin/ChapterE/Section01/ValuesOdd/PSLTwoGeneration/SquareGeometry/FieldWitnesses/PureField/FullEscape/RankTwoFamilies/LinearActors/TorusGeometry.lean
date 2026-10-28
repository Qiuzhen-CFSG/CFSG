module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry.Inner
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.TorusGeometry.Outer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.OddLocals

/-!
# Semilinear-normalized odd torus witnesses for linear four-groups

Inner actors use a missing prime in an involution centralizer in the actual
PSL₂ layer. Outer actors use a nonsplit torus prime excluded from the split
PGL₂ Sylow overgroup. Characteristic rotation subgroups and their odd prime
cores retain normalization by the full semilinear actor centralizer.

The only extra mathematical input is the stated PGL₂ Sylow-overgroup
classification. The final application uses the literal ambient tau and
produces an escaping rank-one E-member for the original actor. The field-of-nine
inner case is handled separately by the parent linear-actor assembly.

Source: Aschbacher–Smith A.2.3(2), E.1.2 and E.1.14(6), pp.33, 209–210, 214;
Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

/-- The odd torus construction for all linear four-groups, retaining the
full semilinear centralizer. The only classification input concerns maximal
Sylow overgroups of the actual PGL₂ layer. -/
theorem oddTorusPlacement_of_sylowOvergroups {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (hover : ∀ (Q : Sylow 2 (PGL2 F)) (N : Subgroup (PGL2 F)),
      IsCoatom N → (Q : Subgroup _) ≤ N → PrimeGeometry.Diagonal.SylowOvergroupModel F N) :
    OddTorusPlacement F p := by
  intro T A hA hr hAL hAT hcase M hM hTM
  let L := pGammaL2PGLRange F
  let D := A.subgroupOf L
  let := hA
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hAL
  have hD : Group.rank D = 2 := (Group.rank_congr (subgroupOfEquivOfLe hAL)).trans hr
  have hfourD : IsKleinFour D := LinearWitnesses.large_actor_isKleinFour
    (F := F) ⟨p, 2, hp, ho, by decide, hF⟩
    (Or.inr ⟨(pGammaL2PGLRangeEquiv F).symm⟩) D
    (show 1 < Group.rank D from hD.symm ▸ (by decide : 1 < (2 : ℕ)))
  let e : D ≃* A := subgroupOfEquivOfLe hAL
  have hfour : IsKleinFour A :=
    ⟨(Nat.card_congr e.toEquiv).symm.trans hfourD.card_four,
      (Monoid.exponent_eq_of_mulEquiv e.symm).trans hfourD.exponent_two⟩
  have hw : ∃ r : ℕ, r.Prime ∧ Odd r ∧ ∃ X : Subgroup (PGammaL2 F),
      IsPGroup r X ∧ centralizer (A : Set (PGammaL2 F)) ≤ normalizer (X : Set _) ∧
      ¬ ⁅X, A⁆ ≤ M := by
    by_cases hAJ : A ≤ pGammaL2PSLRange F
    · have hp5 : 5 ≤ p := hcase.resolve_right (not_not_intro hAJ)
      exact TorusGeometry.inner_placement hp ho hF hp5 T A M hfour hAT hAJ hM.ne_top hTM
    · exact TorusGeometry.outer_placement hp ho hF hlarge hover T A M hfour hAL hAJ hM.ne_top hTM
  obtain ⟨r, hr, hro, X, hX, hn, hmove⟩ := hw
  exact ⟨r, hr, hro, X, hX, inf_le_right.trans hn, hmove⟩

/-- Application to the actual E-family: the original actor has an escaping
rank-one E-member. Ambient tau is the full Sylow centralizer, as required
by source E.1.2(E0). -/
theorem exists_eMember_of_sylowOvergroups {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hF : Nat.card F = p ^ 2) (hlarge : 5 < p ^ 2)
    (hover : ∀ (Q : Sylow 2 (PGL2 F)) (N : Subgroup (PGL2 F)),
      IsCoatom N → (Q : Subgroup _) ≤ N → PrimeGeometry.Diagonal.SylowOvergroupModel F N)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hrank : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PGLRange F) (hAT : A ≤ (T : Subgroup _))
    (hcase : 5 ≤ p ∨ ¬ A ≤ pGammaL2PSLRange F)
    (M : Subgroup (PGammaL2 F)) (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M) :
    ∃ K : Subgroup (PGammaL2 F), IsEMemberAt 1 (T : Subgroup _) A K ∧ ¬ K ≤ M := by
  obtain ⟨r, hr, hro, X, hX, hn, hmove⟩ :=
    oddTorusPlacement_of_sylowOvergroups hp ho hF hlarge hover T A hA hrank hAL hAT hcase M hM hTM
  let := hA
  let : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by intro h; subst r; exact hro.not_two_dvd_nat (dvd_refl 2)
  apply CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.exists_escaping_member_of_normalized_odd_commutator
    T A hAT hr2 X hX _ M hmove
  rwa [full_tau_eq_inf_centralizer hp ho hF hlarge]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
