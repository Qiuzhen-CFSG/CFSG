module

public import Theory.Mathieu.M11.InvariantDesign
public import Theory.Mathieu.M11.WittUniqueness
public import Theory.Mathieu.M11.Properties.Order

/-!
# Recognition of sharply four-transitive groups of degree eleven

A faithful sharply four-transitive action on eleven points determines the
Mathieu group `M11`, defined as the automorphism group of the explicit small
Witt design. The action preserves a Witt design, and uniqueness of that design
conjugates the action into `M11`. Faithfulness gives an embedding; sharp
transitivity and the order of the concrete model make this embedding surjective.

Source: Jordan's theorem as cited by Wong (1964), Theorem 6(a), p. 108;
Hall, *The Theory of Groups*, Theorem 5.8.1.
-/

namespace Sporadic.Mathieu

open Theory.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G] [MulAction G (Fin 11)]
  [FaithfulSMul G (Fin 11)]

/-- An invariant Witt design and a relabeling to the explicit model identify a
faithful sharply four-transitive group with `M11`. -/
public theorem nonempty_mulEquiv_M11_of_invariant_design
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4)
    (D : SteinerSystem (Fin 11) 4 5)
    (hD : ∀ g : G, MulAction.toPerm g ∈ D.aut)
    (e : Equiv.Perm (Fin 11))
    (he : e • (D.blocks : Set (Finset (Fin 11))) =
      (m11WittDesign.blocks : Set (Finset (Fin 11)))) :
    Nonempty (G ≃* M11) := by
  let f : G →* Equiv.Perm (Fin 11) :=
    (MulAut.conj e).toMonoidHom.comp (MulAction.toPermHom G (Fin 11))
  have hf (g : G) : f g ∈ M11 := by
    change e * MulAction.toPerm g * e⁻¹ ∈ m11WittDesign.aut
    rw [SteinerSystem.mem_aut_iff, ← he]
    have hg := (D.mem_aut_iff _).mp (hD g)
    simp only [mul_smul, inv_smul_smul, hg]
  let φ : G →* M11 := f.codRestrict M11 hf
  have hφ : Function.Injective φ := by
    intro a b hab
    apply MulAction.toPerm_injective (β := Fin 11)
    apply (MulAut.conj e).injective
    exact congrArg (fun x : M11 => (x : Equiv.Perm (Fin 11))) hab
  refine ⟨MulEquiv.ofBijective φ ((Nat.bijective_iff_injective_and_card φ).mpr
    ⟨hφ, ?_⟩)⟩
  rw [sharpFour_degreeEleven_card h, m11_order]

/-- Every finite group with a faithful sharply four-transitive action on eleven
points is isomorphic to the concrete Mathieu group `M11`. -/
public theorem nonempty_mulEquiv_M11_of_sharplyMultiplyPretransitive
    [Finite G]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 11) 4) :
    Nonempty (G ≃* M11) := by
  obtain ⟨D, hD⟩ := sharpFour_degreeEleven_exists_invariantDesign h
  obtain ⟨e, he⟩ := m11WittDesign_unique D
  exact nonempty_mulEquiv_M11_of_invariant_design h D hD e he

end Sporadic.Mathieu
