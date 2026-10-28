module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Natural
public import Theory.GroupTheory.PPerfectHom

/-!
# Rank-one Borels and small invariant subgroups

The exports identify the normalizer of the upper root group with the actual
upper triangular matrices, prove its two-perfectness, and bound nontrivial
invariant subgroups in one or two root groups or natural modules. In the
two-factor cases each Borel acts on its own factor. Two-perfectness also
passes to the product, since any homomorphism to a two-group kills both
factors.

Source: the two even-field cases of Aschbacher–Smith 15.4.20,
`refs/quasithin.pdf`, printed p.1164.
-/

public section
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The product of the two actual Borels is two-perfect. -/
theorem rankOneBorel_prod_isPPerfect (hq : 4 ≤ Nat.card F) :
    IsPPerfect 2 ((rankOneBorel F) × (rankOneBorel F)) := by
  intro N hN hQ
  let := hN
  let π := QuotientGroup.mk' N
  have h₁ := (rankOneBorel_isPPerfect hq).hom_eq_one_of_isPGroup hQ
    (π.comp (MonoidHom.inl _ _))
  have h₂ := (rankOneBorel_isPPerfect hq).hom_eq_one_of_isPGroup hQ
    (π.comp (MonoidHom.inr _ _))
  apply top_unique
  rintro ⟨a, b⟩ _
  apply (QuotientGroup.eq_one_iff _).mp
  have ha : π (a, 1) = 1 := DFunLike.congr_fun h₁ a
  have hb : π (1, b) = 1 := DFunLike.congr_fun h₂ b
  calc
    π (a, b) = π ((a, 1) * (1, b)) := by simp
    _ = 1 := by rw [map_mul, ha, hb, one_mul]

end Matrix.SpecialLinearGroup
