module

public import Theory.Mathieu.M12.Recognition.InvariantDesign
public import Theory.Mathieu.M12.Recognition.WittUniqueness
public import Theory.Mathieu.M12.Properties.Order

/-!
# Recognition of sharply five-transitive groups of degree twelve

The sharp action constructs an invariant Steiner system `S(5,6,12)`.
A relabeling of its blocks to the explicit W12 design conjugates the faithful
action into the actual group `M12`. Both groups have order 95040, so the
embedding is an isomorphism.

Uniqueness of `S(5,6,12)` supplies the relabeling, so the final recognition
theorem requires only the given finite faithful sharply five-transitive action.

Source: Aschbacher, *A 2-local characterization of M12*, Illinois J. Math.
47 (2003), Lemma 4.11, citing *Sporadic Groups*, Exercise 6.6.7.
-/

namespace Sporadic.Mathieu

open Theory.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G] [MulAction G (Fin 12)]
  [FaithfulSMul G (Fin 12)]

/-- An invariant Steiner system and its identification with the explicit W12
design identify a faithful sharply five-transitive group with the actual M12. -/
public theorem nonempty_mulEquiv_M12_of_invariant_design
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 12) 5)
    (D : SteinerSystem (Fin 12) 5 6)
    (hD : ∀ g : G, MulAction.toPerm g ∈ D.aut)
    (e : Equiv.Perm (Fin 12))
    (he : e • (D.blocks : Set (Finset (Fin 12))) =
      (m12WittDesign.blocks : Set (Finset (Fin 12)))) :
    Nonempty (G ≃* M12) := by
  let f : G →* Equiv.Perm (Fin 12) :=
    (MulAut.conj e).toMonoidHom.comp (MulAction.toPermHom G (Fin 12))
  have hf (g : G) : f g ∈ M12 := by
    rw [mem_M12_iff]
    change (e * MulAction.toPerm g * e⁻¹) •
      (m12WittDesign.blocks : Set (Finset (Fin 12))) =
        (m12WittDesign.blocks : Set (Finset (Fin 12)))
    rw [← he]
    have hg := (D.mem_aut_iff _).mp (hD g)
    simp only [mul_smul, inv_smul_smul, hg]
  let φ : G →* M12 := f.codRestrict M12 hf
  have hφ : Function.Injective φ := by
    intro a b hab
    apply MulAction.toPerm_injective (β := Fin 12)
    apply (MulAut.conj e).injective
    exact congrArg (fun x : M12 => (x : Equiv.Perm (Fin 12))) hab
  refine ⟨MulEquiv.ofBijective φ ((Nat.bijective_iff_injective_and_card φ).mpr
    ⟨hφ, ?_⟩)⟩
  rw [sharpFive_degreeTwelve_card h, m12_order]

/-- Sharp-action recognition reduced to the geometric uniqueness theorem.
The invariant design is constructed from the action, with no design premise. -/
public theorem nonempty_mulEquiv_M12_of_sharp_action_and_witt_uniqueness
    [Finite G]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 12) 5)
    (hunique : ∀ D : SteinerSystem (Fin 12) 5 6,
      ∃ e : Equiv.Perm (Fin 12),
        e • (D.blocks : Set (Finset (Fin 12))) =
          (m12WittDesign.blocks : Set (Finset (Fin 12)))) :
    Nonempty (G ≃* M12) := by
  obtain ⟨D, hD⟩ := sharpFive_degreeTwelve_exists_invariantDesign h
  obtain ⟨e, he⟩ := hunique D
  exact nonempty_mulEquiv_M12_of_invariant_design h D hD e he

/-- Every finite group with a faithful sharply five-transitive action on twelve
points is isomorphic to the concrete Witt-design automorphism group `M12`.
Both the invariant design and its relabeling are constructed from the action. -/
public theorem nonempty_mulEquiv_M12_of_sharplyMultiplyPretransitive
    [Finite G]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 12) 5) :
    Nonempty (G ≃* M12) :=
  nonempty_mulEquiv_M12_of_sharp_action_and_witt_uniqueness h m12WittDesign_unique

end Sporadic.Mathieu
