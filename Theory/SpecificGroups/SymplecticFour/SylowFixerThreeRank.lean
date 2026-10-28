module
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.RootComponents
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootSocle
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Cubic rank of symplectic involution centralizers

Both root centralizers project to SL₂ over the original field with a
two-group kernel. The nonroot involution centralizer is a two-group.
Thus each has cubic rank at most one. The proved semilinear description
and Sylow-fixer calculation give the same bound for the actual fixed group
of a pointwise Sylow-fixing involution, at every nonbinary even field.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832; the intrinsic
root-centralizer and automorphism calculations of F.1.12 and 16.1.6.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem threeRank_le_of_two_kernel {X : Type*} [Group X] [Finite X]
    (f : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hk : IsPGroup 2 f.ker) :
    primeRank 3 X ≤ 1 := by
  obtain ⟨k,hk⟩ := hk.exists_card_eq
  exact (primeRank_le_of_coprime_ker 3 f (by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k)).trans
      (Matrix.SL2.binary_odd_primeRank_le_one (by decide : Odd 3))

/-- Both root lengths and the nonroot class have centralizers of cubic rank at most one. -/
theorem involution_centralizer_threeRank_le_one {n : ℕ}
    (hF : Nat.card F = 2^n) (x : Sp F) (hx : orderOf x = 2) :
    primeRank 3 (centralizer ({x} : Set (Sp F))) ≤ 1 := by
  by_cases hr : InvolutionTypes.IsRootElement x
  · rcases InvolutionCentralizers.root_centralizer_equiv_local x hr with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · rw [primeRank_equiv 3 e]
      let : IsElementaryAbelian 2 (pointQuotient (F := F)).ker := pointRadical_elementaryAbelian
      exact threeRank_le_of_two_kernel pointQuotient (IsElementaryAbelian.isPGroup 2 _)
    · rw [primeRank_equiv 3 e]
      let : IsElementaryAbelian 2 (Plane.quotientMap (F := F)).ker := Plane.radical_elementaryAbelian
      exact threeRank_le_of_two_kernel Plane.quotientMap (IsElementaryAbelian.isPGroup 2 _)
  · have hp := TwoConjugate.isPGroup_centralizer_of_nonroot_involution hF x hx hr
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    have hz : primeRank 3 (centralizer ({x} : Set (Sp F))) = 0 :=
      PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
        rw [hk]
        exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h))
    omega

/-- The full fixed group of the original pointwise Sylow-fixing involution has cubic rank at most one. -/
theorem sylow_fixer_fixed_threeRank_le_one {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (P : Sylow 2 (Sp F)) (a : MulAut (Sp F)) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ P, a x = x) : primeRank 3 a.fixedSubgroup ≤ 1 := by
  obtain ⟨x,_,rfl⟩ := DiagramAutomorphisms.aut_fixing_sylow_inner hF hn
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram P a hfix
  rw [MulAut.fixedSubgroup_conj]
  apply involution_centralizer_threeRank_le_one hF x
  rwa [MulAut.conj_orderOf_of_center_eq_bot EvenProjective.center_eq_bot] at ha
end Theory.SpecificGroups.SymplecticFour
