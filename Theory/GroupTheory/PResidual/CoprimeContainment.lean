module
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PPerfectHom

/-!
# A coprime residual contained in a primary subgroup

For distinct primes p and q, O^{p′}(A) is q-perfect. If it lies in a
q-subgroup, its inclusion is therefore trivial, so A has order prime to p.
This is the action-kernel reduction in Aschbacher–Smith 13.4.7, printed
p.899, with p=3 and q=2. The chapter consumer retains the actual kernel
and its inclusions into the relative fixed-subgroup centralizers.
-/

public section
namespace Subgroup
variable {A : Type*} [Group A] [Finite A]

theorem coprime_card_of_primeToResidual_le_pGroup
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    (Q : Subgroup A) (hQ : IsPGroup q Q) (hRQ : primeToResidual p A ≤ Q) :
    Nat.Coprime p (Nat.card A) := by
  have he := (isPPerfect_primeToResidual (G := A) p q hpq).hom_eq_one_of_isPGroup
    hQ (inclusion hRQ)
  have hb : primeToResidual p A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    exact congrArg (fun f : primeToResidual p A →* Q => (f ⟨a,ha⟩).val) he
  have hc := primeToResidual_index_coprime (G := A) p
  rwa [hb,index_bot] at hc

end Subgroup
