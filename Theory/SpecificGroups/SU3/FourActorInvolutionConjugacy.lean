module

public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.OddCentralInvolutionLifting

/-!
# Involution conjugacy in the projective odd-prime unitary group

Lift the two involutions through the actual odd scalar kernel of SU₃ → PSU₃.
The special-unitary eigenbasis theorem conjugates their lifts, and the natural
projection carries that conjugator to the projective group. In particular this
argument includes characteristic three, without identifying SU₃ with PSU₃.

This supplies the Sylow positioning of the inner involution of an outer
four-group in Aschbacher--Smith, E.1.14(7), printed p.214. The centralizer and
eigenbasis calculation is the one used in A.3.21(a), printed p.55.
-/

public section
open BenderSuzuki.MatrixGroups
namespace Matrix.SU3

/-- All involutions in the actual projective image of the identity-form SU₃
over a quadratic prime field are conjugate in that image. -/
theorem projective_involutions_isConj
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ 2)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hc : ∀ x, J.conj x = x ^ p)
    (a b : ProjectiveSpecialUnitaryMatrixGroup J)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  obtain ⟨x, hx, hx2⟩ := OddCentralLifting.exists_involution_lift J.specialToProjective
    J.odd_card_specialToProjective_ker J.specialToProjective_surjective a
    (ha ▸ pow_orderOf_eq_one a)
  obtain ⟨y, hy, hy2⟩ := OddCentralLifting.exists_involution_lift J.specialToProjective
    J.odd_card_specialToProjective_ker J.specialToProjective_surjective b
    (hb ▸ pow_orderOf_eq_one b)
  have hxne : x ≠ 1 := by
    intro h
    have : a = 1 := hx.symm.trans (h ▸ map_one _)
    simp [this] at ha
  have hyne : y ≠ 1 := by
    intro h
    have : b = 1 := hy.symm.trans (h ▸ map_one _)
    simp [this] at hb
  have hh := involutions_isConj hp hcard J hJ hc x y
    (orderOf_eq_prime hx2 hxne) (orderOf_eq_prime hy2 hyne)
  simpa only [hx, hy] using J.specialToProjective.map_isConj hh

end Matrix.SU3
