module

public import Theory.Representation.PSL3Two.ResidualFFForms.Criteria
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Vanishing of invariant forms from simple-constituent costs

A commutator-generated binary module satisfying `SimpleBudget A d` admits no
nonzero invariant bilinear form when its fixed codimension for `A` is at most
`d`. No splitting, faithfulness, symmetry or nondegeneracy is required.

Induct on dimension and choose a simple submodule `N`. If `N` is trivial,
commutator generation puts it in both radicals. Otherwise non-self-duality
annihilates the restricted form. A nonzero cross-pairing would surject from
`V/N` onto the simple dual of `N`; the quotient/submodule codimension inequality
would then contradict the sum bound in `SimpleBudget`. Repeat for the flipped
form and descend through `V/N`, which retains commutator generation.

This is the general conditional constituent argument motivated by
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(3.8), printed p.878, and the constituent cost bounds behind (1.4), p.842.
The concrete construction of `SimpleBudget` is a separate input.
-/

public section

open Representation Representation.BinaryOffender
namespace BinaryLinearThree.ResidualFFForms
universe u v

-- An invariant dual subspace has an invariant coannihilator in the original
-- module; finite-dimensional annihilator duality exchanges zero and top.
private theorem irreducible_dual {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

variable {G : Type v} [Group G]
variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

private def formIntertwiner (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    IntertwiningMap ρ ρ.dual where
  toLinearMap := B
  isIntertwining' g := by
    ext v w
    change B (ρ g v) w = B v (ρ g⁻¹ w)
    simpa only [ρ.self_inv_apply] using hB g v (ρ g⁻¹ w)

private theorem form_zero_of_not_self_dual
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (hdual : ¬ Nonempty (ρ.Equiv ρ.dual)) : B = 0 := by
  let f := formIntertwiner ρ B hB
  rcases IsIrreducible.injective_or_eq_zero f with hi | hz
  · have hs : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp : Module.finrank (ZMod 2) V =
          Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V))).mp hi
    exact False.elim (hdual ⟨f.ofBijective ⟨hi, hs⟩⟩)
  · exact congrArg IntertwiningMap.toLinearMap hz

private theorem linear_form_zero_of_full (ρ : Representation (ZMod 2) G V)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (f : Module.Dual (ZMod 2) V)
    (hf : ∀ g v, f (ρ g v) = f v) : f = 0 := by
  have h : subspaceCommutator ρ ⊤ ⊤ ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    change f (ρ g v - v) = 0
    rw [map_sub, hf, sub_self]
  rw [hfull] at h
  ext v
  exact h Submodule.mem_top

private theorem full_quotient (ρ : Representation (ZMod 2) G V)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (N : Subrepresentation ρ) :
    subspaceCommutator N.quotientRepresentation ⊤ ⊤ = ⊤ := by
  have h : subspaceCommutator ρ ⊤ ⊤ ≤
      (subspaceCommutator N.quotientRepresentation ⊤ ⊤).comap N.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    change N.toSubmodule.mkQ (ρ g v - v) ∈
      subspaceCommutator N.quotientRepresentation ⊤ ⊤
    rw [map_sub, ← N.quotientRepresentation_mk]
    exact Submodule.subset_span ⟨g, hg, N.toSubmodule.mkQ v, Submodule.mem_top, rfl⟩
  rw [hfull] at h
  apply top_unique
  intro q _
  obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective q
  exact h Submodule.mem_top

-- Work with one orientation first, so the argument also applies to nonsymmetric
-- bilinear forms by running it again on the flip.
private theorem simple_le_right_radical [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (d : ℕ)
    (hbudget : SimpleBudget.{u} A d) (hcost : fixedCodim ρ A ≤ d)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (N : Subrepresentation ρ) [IsIrreducible N.toRepresentation]
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    N.toSubmodule ≤ B.flip.ker := by
  by_cases htriv : N.toRepresentation = 1
  · intro n hn
    apply linear_form_zero_of_full ρ hfull
    intro g v
    have hgn : ρ g n = n := by
      have h := congrArg (fun σ : Representation (ZMod 2) G N.toSubmodule =>
        (σ g ⟨n, hn⟩ : V)) htriv
      exact h
    change B (ρ g v) n = B v n
    simpa only [hgn] using hB g v n
  · obtain ⟨hdual, hsum⟩ := hbudget N.toSubmodule N.toRepresentation inferInstance
      htriv ((fixedCodim_subrepresentation_le ρ N A).trans hcost)
    let b := B.compl₁₂ N.toSubmodule.subtype N.toSubmodule.subtype
    have hb : b = 0 := form_zero_of_not_self_dual N.toRepresentation b
      (fun g v w => hB g v.val w.val) hdual
    let f : IntertwiningMap ρ N.toRepresentation.dual :=
      { toLinearMap := B.compl₁₂ LinearMap.id N.toSubmodule.subtype
        isIntertwining' g := by
          ext v n
          change B (ρ g v) n.val = B v (ρ g⁻¹ n.val)
          simpa only [ρ.self_inv_apply] using hB g v (ρ g⁻¹ n.val) }
    have hk : N.toSubmodule ≤ f.toLinearMap.ker := by
      intro n hn
      ext m
      exact LinearMap.congr_fun (LinearMap.congr_fun hb ⟨n, hn⟩) m
    let : IsIrreducible N.toRepresentation.dual := irreducible_dual N.toRepresentation
    rcases IsIrreducible.surjective_or_eq_zero f with hs | hz
    · let q := N.toSubmodule.liftQ f.toLinearMap hk
      have hq : Function.Surjective q := by
        intro l
        obtain ⟨v, hv⟩ := hs l
        exact ⟨N.toSubmodule.mkQ v, hv⟩
      have he (g : G) (v : V ⧸ N.toSubmodule) :
          q (N.quotientRepresentation g v) = N.toRepresentation.dual g (q v) := by
        induction v using Submodule.Quotient.induction_on with
        | _ v => exact LinearMap.congr_fun (f.isIntertwining' g) v
      have hqcost := fixedCodim_le_of_equivariant_surjection
        N.quotientRepresentation N.toRepresentation.dual q hq he A
      have hadd := fixedCodim_quotient_add_subrepresentation_le ρ N A
      omega
    · intro n hn
      ext v
      exact congrArg (fun f : IntertwiningMap ρ N.toRepresentation.dual => f v ⟨n, hn⟩) hz

/-- The single-actor simple-constituent budget excludes every invariant bilinear
form on a commutator-generated module within that budget. This holds for
arbitrary groups and nonsplit finite-dimensional binary representations. -/
theorem form_zero_of_simpleBudget [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (d : ℕ)
    (hbudget : SimpleBudget.{u} A d) (hcost : fixedCodim ρ A ≤ d)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) V)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) : B = 0 := by
  generalize hn : Module.finrank (ZMod 2) V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hz : Module.finrank (ZMod 2) V = 0
    · have : Subsingleton V := (Module.finrank_zero_iff).mp hz
      ext v w
      have hv : v = 0 := Subsingleton.elim _ _
      simp only [hv, map_zero, LinearMap.zero_apply]
    · let : Nontrivial V := Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hz)
      obtain ⟨N, hN⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρ
      let : IsIrreducible N.toRepresentation := hN
      have hright := simple_le_right_radical ρ A d hbudget hcost hfull N B hB
      have hleft : N.toSubmodule ≤ B.ker :=
        simple_le_right_radical ρ A d hbudget hcost hfull N B.flip
          (fun g v w => hB g w v)
      let b := B.liftQ₂ N.toSubmodule N.toSubmodule hleft hright
      have hbinv (g : G) (v w : V ⧸ N.toSubmodule) :
          b (N.quotientRepresentation g v) (N.quotientRepresentation g w) = b v w := by
        induction v using Submodule.Quotient.induction_on with
        | _ v =>
          induction w using Submodule.Quotient.induction_on with
          | _ w => exact hB g v w
      have hadd := fixedCodim_quotient_add_subrepresentation_le ρ N A
      let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial
        N.toRepresentation
      have hpos : 0 < Module.finrank (ZMod 2) N.toSubmodule := Module.finrank_pos
      have hdim := N.toSubmodule.finrank_quotient_add_finrank
      have hlt : Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) < n := by omega
      have hb := ih (Module.finrank (ZMod 2) (V ⧸ N.toSubmodule)) hlt
        N.quotientRepresentation (by omega) (full_quotient ρ hfull N) b hbinv rfl
      ext v w
      exact LinearMap.congr_fun
        (LinearMap.congr_fun hb (N.toSubmodule.mkQ v)) (N.toSubmodule.mkQ w)

end BinaryLinearThree.ResidualFFForms
