module

public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Maschke

/-!
# Invariant complements in elementary abelian groups

Maschke's theorem, transported through the canonical `ZMod p`-vector space
on an elementary abelian p-group, gives invariant subgroup complements
for any finite actor of order prime to p. The action is the supplied
homomorphism into the actual automorphism group.
-/

open scoped IsMulCommutative
open Subgroup

/-- Every invariant subgroup has an invariant complement under coprime action. -/
public theorem IsElementaryAbelian.exists_invariant_complement {A V : Type*} [Group A] [Finite A] [Group V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (ρ : A →* MulAut V) (hcop : Nat.Coprime p (Nat.card A))
    (U : Subgroup V) (hU : ∀ a : A, ∀ x ∈ U, ρ a x ∈ U) :
    ∃ W : Subgroup V, IsCompl U W ∧ ∀ a : A, ∀ x ∈ W, ρ a x ∈ W := by
  let σ : Representation (ZMod p) A (Additive V) :=
    { toFun := fun a => (ρ a).toMonoidHom.toAdditive.toZModLinearMap p
      map_one' := by ext x; exact congrArg (fun f : MulAut V => f x.toMul) ρ.map_one
      map_mul' := by intro a b; ext x
                     exact congrArg (fun f : MulAut V => f x.toMul) (ρ.map_mul a b) }
  let e : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)
  let M : Subrepresentation σ := ⟨e U, hU⟩
  have : NeZero (Nat.card A : ZMod p) := ⟨by
    intro hz
    exact (Fact.out : p.Prime).not_dvd_one
      ((Nat.coprime_iff_gcd_eq_one.mp hcop) ▸
        Nat.dvd_gcd (dvd_refl p) ((ZMod.natCast_eq_zero_iff _ _).mp hz))⟩
  obtain ⟨N, hMN⟩ := ComplementedLattice.exists_isCompl M
  refine ⟨e.symm N.toSubmodule, ?_, ?_⟩
  · apply e.isCompl_iff.mpr
    rw [e.apply_symm_apply]
    exact IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hMN.inf_eq_bot)
      (congrArg Subrepresentation.toSubmodule hMN.sup_eq_top)
  · exact N.apply_mem_toSubmodule
