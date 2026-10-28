module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Cocycle

/-!
# Aligning an outer SL₂ involution with its field automorphism

An arbitrary automorphism of SL₂ over a finite field of characteristic two
is inner times an entrywise field automorphism. For an involution, transport
through the canonical SL₂-to-PSL₂ equivalence gives an involutory field
automorphism and a determinant-one cocycle. Outerness excludes the trivial
field automorphism. Determinant-one Hilbert–90 trivializes the cocycle, so
one inner change of coordinates aligns the original actor with that same
field automorphism on every group element.

The exact intertwining identity supplies the group action used by the
natural-module fixed-field argument for Aschbacher--Smith, Lemma 2.4.12(2),
printed p.532. The semilinear and cocycle inputs are the binary linear case
of GLS, Volume 4, Chapter 4, Lemma 3.4(c).
-/

public section
namespace Representation.SL2NaturalOffenders
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- One change of basis aligns an outer involution with its nontrivial
involutory field automorphism on every group element. -/
theorem outer_involution_actor_alignment
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) (ha : a^2=1)
    (houter : ¬∃g,a=MulAut.conj g) :
    ∃ σ : F≃+*F, σ≠RingEquiv.refl F ∧ Function.Involutive σ ∧
      ∃c : Matrix.SpecialLinearGroup (Fin 2) F, ∀g,
        (MulAut.conj c⁻¹) (a g) =
          Theory.PSL2.sl2FieldAut σ ((MulAut.conj c⁻¹) g) := by
  obtain ⟨b,σ,hab⟩ := Theory.PSL2.sl2_semilinear_coverage a
  have hne : σ≠RingEquiv.refl F := by
    intro he
    apply houter
    refine ⟨b,?_⟩
    rw [hab,he]
    have hrefl : Theory.PSL2.sl2FieldAut (RingEquiv.refl F)=1 := by
      ext g i j
      rfl
    rw [hrefl,mul_one]
  let e := Theory.PSL2.sl2QuotientEquiv F
  have hsq : (MulAut.conj (e b) * Theory.PSL2.fieldAut σ)^2=1 := by
    have hh := congrArg (MulAut.congr e) ha
    rw [map_pow,map_one,hab,map_mul,MulAut.congr_conj] at hh
    exact hh
  obtain ⟨hs,hb⟩ := Theory.PSL2.semilinear_involution_data σ (e b) hsq
  have heq (g : Matrix.SpecialLinearGroup (Fin 2) F) :
      e (Theory.PSL2.sl2FieldAut σ g)=Theory.PSL2.fieldAut σ (e g) :=
    (Theory.PSL2.fieldAut_apply_quotientMap σ g).symm
  have hcoc : b * Theory.PSL2.sl2FieldAut σ b=1 := by
    apply e.injective
    rw [map_mul,map_one,heq]
    exact hb
  obtain ⟨c,hc⟩ := Theory.PSL2.involutory_sl2_cocycle_trivial σ hs hne b hcoc
  refine ⟨σ,hne,hs,c,?_⟩
  intro g
  rw [hab]
  change c⁻¹ * (b * Theory.PSL2.sl2FieldAut σ g * b⁻¹) * c⁻¹⁻¹ =
    Theory.PSL2.sl2FieldAut σ (c⁻¹ * g * c⁻¹⁻¹)
  rw [hc]
  simp only [map_mul,map_inv,mul_inv_rev,inv_inv]
  group
end Representation.SL2NaturalOffenders
