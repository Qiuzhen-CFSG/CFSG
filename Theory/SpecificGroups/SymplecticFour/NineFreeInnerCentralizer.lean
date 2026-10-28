module

public import Theory.GroupAction.InnerCentralizerCardinality
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootSocle
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.RootComponents
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterOrder
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The small centralizer alternative in Sp₄(4)

A root involution centralizer maps onto SL₂(4), so its order is divisible
by five and cannot divide 2304. Every remaining involution has a two-group
centralizer. The actual outer group has order dividing four, so its full
inner-automorphism centralizer is prime to three.
Source: Aschbacher--Smith 14.3.20, printed p.998, even-model inspection.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The numerical centralizer restriction excludes both root classes. -/
theorem not_root_of_centralizer_card_dvd_2304 (hF : Nat.card F = 4)
    (x : Sp F) (hc : Nat.card (centralizer ({x} : Set (Sp F))) ∣ 2304) :
    ¬ InvolutionTypes.IsRootElement x := by
  intro hr
  have hs : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]
    norm_num
  have hd : 60 ∣ Nat.card (centralizer ({x} : Set (Sp F))) := by
    rcases InvolutionCentralizers.root_centralizer_equiv_local x hr with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv, ← hs]
      exact card_dvd_of_surjective pointQuotient pointQuotient_surjective
    · rw [Nat.card_congr e.toEquiv, ← hs]
      exact card_dvd_of_surjective Plane.quotientMap Plane.quotientMap_surjective
  exact (by decide : ¬ 60 ∣ 2304) (hd.trans hc)

/-- No factor nine occurs in the full automorphism centralizer in this row. -/
theorem not_nine_dvd_inner_involution_centralizer (hF : Nat.card F = 4)
    (x : Sp F) (hx : orderOf x = 2)
    (hc : Nat.card (centralizer ({x} : Set (Sp F))) ∣ 2304) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut (Sp F)))) := by
  have hp := TwoConjugate.isPGroup_centralizer_of_nonroot_involution
    (n := 2) hF x hx (not_root_of_centralizer_card_dvd_2304 hF x hc)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have ho : Nat.card (MulAut.Outer (Sp F)) ∣ 4 :=
    DiagramAutomorphisms.card_outer_dvd_two_mul (n := 2) hF (by omega)
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  have hd := (MulAut.centralizer_conj_card_dvd EvenProjective.center_eq_bot x).trans
    (Nat.mul_dvd_mul_left _ ho)
  rw [hk] at hd
  have hcop : Nat.Coprime 3 (2 ^ k * 4) :=
    ((by decide : Nat.Coprime 3 2).pow_right k).mul_right (by decide)
  intro hn
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop)
    (((by decide : 3 ∣ 9).trans hn).trans hd)

end Theory.SpecificGroups.SymplecticFour
