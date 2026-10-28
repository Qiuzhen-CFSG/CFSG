module

public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Sylow isomorphisms through coprime kernels

A surjective homomorphism with kernel of order prime to p restricts to an
isomorphism on each Sylow p-subgroup. Its image is Sylow, so conjugacy gives
an actual multiplicative equivalence with any Sylow subgroup of the target.
No centrality assumption is needed. This supplies the special-to-projective
comparison in the unitary application of Aschbacher–Smith A.3.21(b).
-/

namespace Sylow
variable {G H : Type*} [Group G] [Finite G] [Group H]
variable {p : ℕ} [Fact p.Prime]

/-- Restrict the homomorphism to a Sylow subgroup, then conjugate its image
to the specified target Sylow subgroup. -/
public noncomputable def equivOfSurjectiveCoprime
    (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (P : Sylow p G) (Q : Sylow p H) : P ≃* Q := by
  let : Finite H := Finite.of_surjective f hf
  let e : P ≃* (P : Subgroup G).map f :=
    MulEquiv.ofBijective (f.subgroupMap (P : Subgroup G)) ⟨by
      intro x y h
      exact Subgroup.injective_comp_subtype_of_coprime_ker f hker _ P.isPGroup'
        (congrArg Subtype.val h), f.subgroupMap_surjective _⟩
  exact e.trans ((P.mapSurjective hf).equiv Q)
end Sylow
