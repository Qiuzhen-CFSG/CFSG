module
public import Theory.Representation.BinaryScalarCommutant

/-!
# Two-groups commuting with a binary scalar action

A scalar involution in characteristic two is trivial. Repeated squaring
therefore kills every element of a commuting two-group. This applies to
arbitrary two-groups, without a finiteness or elementary-abelian assumption.

Source application: the ambient core action in DGS, Groups and Graphs
(1985), (6.5), pp.121--122, via BinaryConjugationSection.TwoGroupScalarCommutant.
-/

public noncomputable section
namespace Representation.BinaryScalarCommutant
variable {F J V : Type*} [Field F] [CharP F 2] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [Module F V] [Nontrivial V]
theorem twoGroup_commuting_action_trivial
    (σ : Representation (ZMod 2) J V)
    (hs : ∀ f : V →ₗ[ZMod 2] V, (∀ j v, f (σ j v) = σ j (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    {Q : Type*} [Group Q] (hQ : IsPGroup 2 Q)
    (η : Representation (ZMod 2) Q V)
    (hcomm : ∀ q j v, η q (σ j v) = σ j (η q v)) :
    ∀ q v, η q v = v := by
  have hp : ∀ n (q : Q), q ^ (2 ^ n) = 1 → η q = 1 := by
    intro n
    induction n with
    | zero => intro q hq; simpa using congrArg η hq
    | succ n ih =>
      intro q hq
      apply commuting_involution_eq_one σ hs (η q) (hcomm q)
      have hh : (q*q) ^ (2^n) = 1 := by
        rw [←pow_two,←pow_mul,Nat.mul_comm 2,←pow_succ]
        exact hq
      simpa only [map_mul] using ih (q*q) hh
  intro q v
  obtain ⟨n,hn⟩ := hQ.exists_pow_pow_eq_one q
  rw [hp n q hn]
  rfl
end Representation.BinaryScalarCommutant
