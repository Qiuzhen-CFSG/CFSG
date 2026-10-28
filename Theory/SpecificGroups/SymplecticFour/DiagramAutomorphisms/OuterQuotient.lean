module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.CyclicNormalOddQuotient
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# A cyclic normal subgroup of the symplectic outer group

Over a finite field of characteristic two with more than two elements,
arbitrary automorphisms permute the two actual parabolic conjugacy classes.
Inner automorphisms fix them. Thus the action descends to the actual outer
group, with image in a permutation group on at most two elements.

Assuming the separately owned classification of diagram-preserving
automorphisms as inner times entrywise field automorphisms, the kernel in the
outer group is exactly the image of the cyclic field-automorphism group. This
proves a cyclic normal subgroup with cyclic quotient, hence the required
restriction on odd-prime subgroups. No simplicity or perfectness premise is
needed, and the sole classification input is displayed explicitly.

Source: GLS3, Theorem 2.5.12(c)--(e), `refs/KGroup/GLS3/chapter2.tex`; the
outer-group restriction used in Aschbacher--Smith, `refs/quasithin.pdf`, printed
p.510, for the symplectic type in Remark A.2.4 on p.33. The conclusion here is
the stated restriction, not the stronger exact cyclic outer-group formula.
-/

@[expose] public section

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F]

/-- Entrywise application of field automorphisms is a group homomorphism. -/
def fieldAutomorphismHom : (F ≃+* F) →* MulAut (Sp F) where
  toFun := fieldAutomorphism
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    rfl

variable [Finite F] [CharP F 2]

private theorem parabolicClass_permutations_isCyclic (hF : 2 < Nat.card F) :
    IsCyclic (Equiv.Perm (parabolicClasses hF)) := by
  classical
  let := Fintype.ofFinite (parabolicClasses hF)
  apply isCyclic_of_card_dvd_prime (p := 2)
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hc : Fintype.card (parabolicClasses hF) ≤ 2 := by
    simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hF
  simpa using Nat.factorial_dvd_factorial hc

/-- The outer group has a cyclic normal subgroup with cyclic quotient once
the diagram-preserving semilinear classification is supplied. -/
theorem outer_cyclic_normal_cyclic_quotient (hF : 2 < Nat.card F)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ) :
    ∃ N : Subgroup (MulAut.Outer (Sp F)), ∃ _ : N.Normal,
      IsCyclic N ∧ IsCyclic (MulAut.Outer (Sp F) ⧸ N) := by
  let π : MulAut (Sp F) →* MulAut.Outer (Sp F) :=
    QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))
  let D := (parabolicClassAction hF).ker
  let N : Subgroup (MulAut.Outer (Sp F)) := D.map π
  have hN : N.Normal := (inferInstance : D.Normal).map π (QuotientGroup.mk'_surjective _)
  let := hN
  have hinner : MulAut.innerSubgroup (Sp F) ≤ D := by
    rintro a ⟨g, rfl⟩
    exact (mem_parabolicClassAction_ker_iff hF _).mpr (inner_preservesDiagram g)
  let ρ : MulAut.Outer (Sp F) →* Equiv.Perm (parabolicClasses hF) :=
    QuotientGroup.lift _ (parabolicClassAction hF) hinner
  have hker : ρ.ker = N := QuotientGroup.ker_lift _ _ hinner
  let φ : (F ≃+* F) →* MulAut.Outer (Sp F) := π.comp fieldAutomorphismHom
  have hfield : φ.range = N := by
    apply le_antisymm
    · rintro x ⟨σ, rfl⟩
      exact ⟨fieldAutomorphism σ,
        (mem_parabolicClassAction_ker_iff hF _).mpr (field_preservesDiagram σ), rfl⟩
    · rintro x ⟨a, ha, rfl⟩
      obtain ⟨g, σ, rfl⟩ := hclass a ((mem_parabolicClassAction_ker_iff hF a).mp ha)
      refine ⟨σ, ?_⟩
      have hi : π (MulAut.conj g) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
      change π (fieldAutomorphism σ) = π (MulAut.conj g * fieldAutomorphism σ)
      rw [map_mul, hi, one_mul]
  have hcN : IsCyclic N := by
    rw [← hfield]
    let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
    exact isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hcQ : IsCyclic (MulAut.Outer (Sp F) ⧸ N) := by
    let : IsCyclic (Equiv.Perm (parabolicClasses hF)) :=
      parabolicClass_permutations_isCyclic hF
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange ρ)
    exact isCyclic_of_injective e.toMonoidHom e.injective
  exact ⟨N, hN, hcN, hcQ⟩

/-- The restriction on the actual outer quotient needed for odd-prime
subgroups in the quasithin outer-automorphism argument. -/
theorem outer_hasCyclicNormalOddQuotient (hF : 2 < Nat.card F)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ) :
    Theory.GroupTheory.HasCyclicNormalOddQuotient (MulAut.Outer (Sp F)) := by
  obtain ⟨N, hN, hcN, hcQ⟩ := outer_cyclic_normal_cyclic_quotient hF hclass
  let := hN
  let := hcQ
  exact ⟨N, hN, hcN, fun _ _ _ _ _ => inferInstance⟩
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
