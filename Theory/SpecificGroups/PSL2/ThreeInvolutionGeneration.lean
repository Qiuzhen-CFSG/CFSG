module

public import Theory.SpecificGroups.PSL2.PrimeQuadraticMaximal
public import Theory.GroupTheory.ThreeConjugateGeneration
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# Three conjugates of an involution generate odd prime or quadratic PSL2

The actual nonsplit torus and its reflection give two involutions generating
its normalizer, of order q+1. The prime-or-quadratic maximality criterion
makes this a maximal subgroup. Simplicity supplies a third conjugate outside
it, and the checked PSL2 involution fusion theorem identifies both original
generators with conjugates of the prescribed involution.

This proves the inner k₂ = 3 bound used by Guralnick--Malle, Classification
of 2F-modules I, (2.6) and Proposition 4.1, pp.4,8--9, for precisely the
large-field parameters required by Aschbacher--Smith K.2, printed p.453.
The torus construction is Huppert II.8.4 on the literal matrix quotient.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
namespace Theory.PSL2

/-- Every involution has three conjugates generating the actual projective matrix group. -/
theorem exists_three_involution_conjugates {F : Type*} [Field F] [Finite F]
    {p e : ℕ} [Fact p.Prime] (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hF : Nat.card F = p ^ e) (hlarge : 25 < p ^ e)
    (t : PSL2MatrixGroup F) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g : Fin 3 → PSL2MatrixGroup F,
      closure (Set.range fun i => g i * t * (g i)⁻¹) = ⊤ := by
  let : IsSimpleGroup (PSL2MatrixGroup F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  obtain ⟨S, w, hScyc, hScard, _, hwS, hw2, hwinv, hDcard, _⟩ :=
    Glauberman.Dickson.huppert_II_8_4_nonsplit_torus_reflection_data hF
  let : IsCyclic S := hScyc
  have hqodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hqodd
    exact ⟨k, by omega⟩
  have hD : Nat.card (S ⊔ zpowers w : Subgroup (PSL2MatrixGroup F)) = p ^ e + 1 := by
    rw [hDcard, hScard, hgcd]
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hmax := isCoatom_of_card_eq_field_succ ho he hF hlarge (S ⊔ zpowers w) hD
  obtain ⟨a, b, ha, ha2, hb, hb2, hab⟩ :=
    Theory.GroupTheory.ThreeConjugateGeneration.pair_of_cyclic_inverter S w hwS
      (by simpa only [pow_two] using hw2) hwinv
  have hta := involutions_isConj t a (orderOf_eq_prime ht2 ht) (orderOf_eq_prime ha2 ha)
  have htb := involutions_isConj t b (orderOf_eq_prime ht2 ht) (orderOf_eq_prime hb2 hb)
  exact Theory.GroupTheory.ThreeConjugateGeneration.of_maximal_pair ht hta htb (hab ▸ hmax)

end Theory.PSL2
