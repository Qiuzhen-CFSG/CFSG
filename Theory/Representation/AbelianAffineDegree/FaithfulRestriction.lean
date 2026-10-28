module
public import Theory.Representation.AbelianAffineDegree

/-!
# Free automizer bounds with a faithful restriction

Only faithfulness on the abelian subgroup is needed to obtain a nontrivial
occurring character. Its orbit under a free subgroup of the automizer bounds
the representation degree, even when the full ambient action has a kernel.
Scalar extension gives the same bound over any coefficient field.

The application is the nilpotent odd-plane branch of Aschbacher--Smith 8.2.7,
printed p.718. The full Fitting subgroup may have other prime factors and
higher homocyclic layers; only the selected omega plane must act faithfully.
-/

public section
open scoped IsMulCommutative
namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A free subgroup of the induced automizer bounds faithful degree. -/
theorem card_le_finrank_of_free_automizer_of_faithful_restriction [IsAlgClosed k]
    [FiniteDimensional k V] (ρ : Representation k G V)
    (N : Subgroup G) [Finite N] [Nontrivial N] [IsMulCommutative N]
    (hρ : Function.Injective (ρ.comp N.subtype)) (horder : (Nat.card N : k) ≠ 0)
    {C : Type*} [Group C] (a : C →* N.normalizerMonoidHom.range)
    (hfree : ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (a c).val) :
    Nat.card C ≤ Module.finrank k V := by
  classical
  let π := (automizerWeightPerm ρ N).comp a
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  have hχ : ∃ χ : CharacterWeight (ρ.comp N.subtype), χ.val ≠ 1 := by
    by_contra! h
    apply hn
    apply eq_of_characterWeight_values (ρ.comp N.subtype)
      hρ horder
    intro χ
    simp [h χ]
  obtain ⟨χ, hχ⟩ := hχ
  have hstab (c : C) (hc : π c χ = χ) : c = 1 := by
    by_contra hne
    apply hχ
    have hfix : ∀ n : N, χ.val ((a c).val n) = χ.val n := by
      intro n
      have hh := congrArg (fun ψ : CharacterWeight (ρ.comp N.subtype) =>
        ψ.val ((a c).val n)) hc
      change χ.val ((a c).val.symm ((a c).val n)) = χ.val ((a c).val n) at hh
      simpa using hh.symm
    apply MonoidHom.ext
    intro n
    obtain ⟨x, rfl⟩ := (hfree c hne).commutatorMap_surjective n
    change χ.val (x / (a c).val x) = 1
    rw [map_div, hfix, div_self']
  have hinj : Function.Injective (fun c : C => π c χ) := by
    intro c d h
    change π c χ = π d χ at h
    have hcd : π (d⁻¹ * c) χ = χ := by
      rw [map_mul, map_inv]
      change (π d).symm (π c χ) = χ
      rw [h]
      exact (π d).symm_apply_apply χ
    exact (inv_mul_eq_one.mp (hstab _ hcd)).symm
  obtain ⟨hfinite, hcard⟩ := characterWeight_card_le (ρ.comp N.subtype) horder
  let := hfinite
  exact (Nat.card_le_card_of_injective _ hinj).trans hcard

/-- The automizer bound over an arbitrary coefficient field. -/
theorem card_le_finrank_of_free_automizer_of_faithful_restriction_of_field
    [FiniteDimensional k V] (ρ : Representation k G V)
    (N : Subgroup G) [Finite N] [Nontrivial N] [IsMulCommutative N]
    (hρ : Function.Injective (ρ.comp N.subtype)) (horder : (Nat.card N : k) ≠ 0)
    {C : Type*} [Group C] (a : C →* N.normalizerMonoidHom.range)
    (hfree : ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (a c).val) :
    Nat.card C ≤ Module.finrank k V := by
  let K := AlgebraicClosure k
  have horder' : (Nat.card N : K) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap k K).injective
    simpa using h
  have h := card_le_finrank_of_free_automizer_of_faithful_restriction (ρ.extendScalars K) N
    ((extendScalars_faithful_iff K (ρ.comp N.subtype)).mp hρ) horder' a hfree
  simpa only [Module.finrank_baseChange] using h

/-- Apply the bound to a free subgroup of a marked quotient action.
No splitting of the original extension is required. -/
theorem card_le_finrank_of_free_quotientAction_of_faithful_restriction
    [FiniteDimensional k V] (ρ : Representation k G V)
    (N : Subgroup G) [N.Normal] [Finite N] [Nontrivial N] [IsMulCommutative N]
    (hρ : Function.Injective (ρ.comp N.subtype)) (horder : (Nat.card N : k) ≠ 0)
    {Q : Type*} [Group Q] (q : G →* Q) (hq : Function.Surjective q)
    (α : Q →* MulAut N) (hα : ∀ g, α (q g) = MulAut.conjNormal g)
    (C : Subgroup Q)
    (hfree : ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (α c)) :
    Nat.card C ≤ Module.finrank k V := by
  let a : C →* N.normalizerMonoidHom.range :=
    (α.comp C.subtype).codRestrict _ (by
      intro c
      obtain ⟨g, hg⟩ := hq c.val
      refine ⟨⟨g, N.normalizer_eq_top ▸ Subgroup.mem_top g⟩, ?_⟩
      change MulAut.conjNormal g = α c.val
      rw [← hα, hg])
  exact card_le_finrank_of_free_automizer_of_faithful_restriction_of_field ρ N hρ horder a hfree

end Representation
