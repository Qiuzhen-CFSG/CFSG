module

public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Transport of Sylow pointwise innerness through an isomorphism

An actual group equivalence carries the specified Sylow subgroup and its
pointwise automorphism fixer to the corresponding objects in the other group.
Pulling back the conjugating element retains membership in the original Sylow.

This supplies the matrix-model and Hermitian-basis changes used by the
characteristic-two unitary calculation in Aschbacher–Smith, B.1.13, pp.73–74.
-/

public section

namespace MulAut
variable {G H : Type*} [Group G] [Group H]
/-- A model isomorphism preserves pointwise innerness with a Sylow representative. -/
theorem fixing_sylow_inner_of_equiv [Finite G] {p : ℕ} [Fact p.Prime]
    (e : G ≃* H)
    (hH : ∀ (Q : Sylow p H) (b : MulAut H),
      (∀ y ∈ Q, b y = y) → ∃ y ∈ Q, b = conj y)
    (P : Sylow p G) (a : MulAut G) (ha : ∀ x ∈ P, a x = x) :
    ∃ x ∈ P, a = conj x := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hb : ∀ y ∈ Q, MulAut.congr e a y = y := by
    rintro y ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply, ha x hx]
  obtain ⟨y, hy, he⟩ := hH Q (MulAut.congr e a) hb
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, hx, (MulAut.congr e).injective ?_⟩
  rw [MulAut.congr_conj]
  exact he
end MulAut

