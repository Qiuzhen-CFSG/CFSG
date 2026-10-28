module

public import Theory.GroupTheory.PResidual.Quotient

/-!
# The residual of a direct product with a p-group

For an actual splitting `H ≃ R × X` with `R` a p-group, the second
projection identifies `Oᵖ(H)` with `Oᵖ(X)`. The first projection kills
the residual; surjectivity of the second projection gives the reverse
inclusion. The resulting equivalence retains its projection equation.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.9.10, printed p.973, with `R = D₈`, `X = S₄`, and `p = 2`.
-/

public section

namespace Subgroup

variable {H R X : Type*} [Group H] [Group R] [Group X]

/-- The p-group coordinate of every residual element is the identity. -/
theorem fst_eq_one_of_mem_pResidual (p : ℕ) (e : H ≃* R × X)
    (hR : IsPGroup p R) {x : H} (hx : x ∈ pResidual p H) : (e x).1 = 1 :=
  pResidual_le_ker_of_isPGroup p ((MonoidHom.fst R X).comp e.toMonoidHom) hR hx

/-- The residual equivalence is induced by the actual second projection. -/
noncomputable def pResidualEquivOfPGroupFactor [Finite H]
    (p : ℕ) (e : H ≃* R × X) (hR : IsPGroup p R) :
    pResidual p H ≃* pResidual p X := by
  let f : H →* X := (MonoidHom.snd R X).comp e.toMonoidHom
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := e.surjective (1, x)
    exact ⟨y, congrArg Prod.snd hy⟩
  let fR : pResidual p H →* pResidual p X :=
    (f.comp (pResidual p H).subtype).codRestrict (pResidual p X)
      (fun x => map_pResidual_le p f (mem_map_of_mem f x.property))
  apply MulEquiv.ofBijective fR
  constructor
  · intro a b hab
    apply Subtype.ext
    apply e.injective
    apply Prod.ext
    · rw [fst_eq_one_of_mem_pResidual p e hR a.property,
        fst_eq_one_of_mem_pResidual p e hR b.property]
    · exact congrArg Subtype.val hab
  · intro x
    have hx : (x : X) ∈ (pResidual p H).map f := by
      rw [map_pResidual_of_surjective p f hf]
      exact x.property
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

/-- Compatibility with the splitting's second projection. -/
theorem pResidualEquivOfPGroupFactor_apply [Finite H]
    (p : ℕ) (e : H ≃* R × X) (hR : IsPGroup p R) (x : pResidual p H) :
    (pResidualEquivOfPGroupFactor p e hR x : X) = (e x).2 := by
  rfl

end Subgroup
