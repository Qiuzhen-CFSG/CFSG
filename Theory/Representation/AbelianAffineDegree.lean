module

public import Theory.Representation.AbelianFrobeniusDegree
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Degree bounds from free subgroups of an abelian automizer

A group acting freely on a nontrivial abelian subgroup, by automorphisms
induced from its ambient normalizer, acts freely on each nontrivial occurring
character. Consequently its order bounds every faithful cross-characteristic
degree. The actors need not lift to a subgroup of the ambient group: the
action on weights already factors through the automizer.

The quotient-action corollary retains the original quotient map and actual
conjugation on the kernel. This is the character-orbit argument for the odd
plane extensions in Aschbacher–Smith, combined manuscript (1 March 2004),
the last sentence of Lemma 8.2.7, printed p.718.
-/

public section
open scoped IsMulCommutative
namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A free subgroup of the induced automizer bounds faithful degree. -/
theorem card_le_finrank_of_fixedPointFree_automizer [IsAlgClosed k]
    [FiniteDimensional k V] (ρ : Representation k G V)
    (N : Subgroup G) [Finite N] [Nontrivial N] [IsMulCommutative N]
    (hρ : Function.Injective ρ) (horder : (Nat.card N : k) ≠ 0)
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
      (hρ.comp Subtype.val_injective) horder
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
theorem card_le_finrank_of_fixedPointFree_automizer_of_field
    [FiniteDimensional k V] (ρ : Representation k G V)
    (N : Subgroup G) [Finite N] [Nontrivial N] [IsMulCommutative N]
    (hρ : Function.Injective ρ) (horder : (Nat.card N : k) ≠ 0)
    {C : Type*} [Group C] (a : C →* N.normalizerMonoidHom.range)
    (hfree : ∀ c : C, c ≠ 1 → MonoidHom.FixedPointFree (a c).val) :
    Nat.card C ≤ Module.finrank k V := by
  let K := AlgebraicClosure k
  have horder' : (Nat.card N : K) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap k K).injective
    simpa using h
  have h := card_le_finrank_of_fixedPointFree_automizer (ρ.extendScalars K) N
    ((extendScalars_faithful_iff K ρ).mp hρ) horder' a hfree
  simpa only [Module.finrank_baseChange] using h

/-- Apply the bound to a free subgroup of a marked quotient action.
No splitting of the original extension is required. -/
theorem card_le_finrank_of_fixedPointFree_quotientAction
    [FiniteDimensional k V] (ρ : Representation k G V)
    (N : Subgroup G) [N.Normal] [Finite N] [Nontrivial N] [IsMulCommutative N]
    (hρ : Function.Injective ρ) (horder : (Nat.card N : k) ≠ 0)
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
  exact card_le_finrank_of_fixedPointFree_automizer_of_field ρ N hρ horder a hfree

end Representation

namespace Subgroup

/-- A self-centralizing normal subgroup has a faithful quotient conjugation
action, with the original quotient map as its marking. -/
theorem exists_faithful_quotient_conjugation {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (hN : centralizer (N : Set G) = N) :
    ∃ α : (G ⧸ N) →* MulAut N, Function.Injective α ∧
      ∀ g, α (QuotientGroup.mk' N g) = MulAut.conjNormal g := by
  have hker : (MulAut.conjNormal : G →* MulAut N).ker = centralizer (N : Set G) := by
    ext g
    change (MulAut.conjNormal (H := N) g : MulAut N) = 1 ↔ g ∈ centralizer (N : Set G)
    constructor
    · intro h n hn
      have he := congrArg (fun a : MulAut N => (a ⟨n, hn⟩ : G)) h
      change g * n * g⁻¹ = n at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro h
      apply MulEquiv.ext
      intro n
      apply Subtype.ext
      change g * (n : G) * g⁻¹ = n
      rw [← h n n.property, mul_inv_cancel_right]
  have hk : (MulAut.conjNormal : G →* MulAut N).ker = N := hker.trans hN
  let α := QuotientGroup.lift N (MulAut.conjNormal : G →* MulAut N) hk.ge
  refine ⟨α, ?_, fun _ => rfl⟩
  apply (MonoidHom.ker_eq_bot_iff α).mp
  rw [QuotientGroup.ker_lift, hk, QuotientGroup.map_mk'_self]

end Subgroup
