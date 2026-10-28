module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra

/-!
# A dimension bound for faithful full binary SL₂(7)-modules

A faithful representation of SL₂(7) over the binary field whose action
differences span the whole module has dimension at least seven.

For the concrete element `x = !![0,1;6,3]`, we have `x⁴ = -1` and `x⁸ = 1`.
Thus `N = σ(x) - 1` satisfies `N⁸ = 0` and `N⁴ = σ(-1) - 1 ≠ 0`.
Strict growth of the first four kernels gives `dim ker N⁴ ≥ 4`. The image
of `N⁴` is invariant because `-1` is central. If this image had dimension
at most two, perfectness and the solvability of S₄ would make its action
trivial. Equivariance would then make `N⁴` vanish on every action difference,
contrary to full commutator generation. Hence `dim range N⁴ ≥ 3`, and
rank-nullity gives the bound.

Source motivation: Aschbacher–Smith, combined manuscript (1 March 2004),
C.1.31–34, printed pp.135–137, and B.2.3–5, printed pp.75–76. This is a
standalone supporting lemma, proved by elementary linear algebra and
perfectness; it does not use a pushing-up classification or a module catalogue.
-/

open Matrix
open scoped MatrixGroups
namespace Representation.BinaryOffender.SL2SevenCentralProduct

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev S := Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)
private instance : Group.IsPerfect S :=
  ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 7)) (by decide) (by decide)⟩
private def x : S := ⟨!![0, 1; 6, 3], by decide⟩
private theorem x_four : x ^ 4 = -1 := by decide +kernel
private theorem x_eight : x ^ 8 = 1 := by decide +kernel
private theorem neg_one_ne_one : (-1 : S) ≠ 1 := by decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem four_le_ker (N : Module.End (ZMod 2) V)
    (h8 : N ^ 8 = 0) (h4 : N ^ 4 ≠ 0) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.ker (N ^ 4)) := by
  have hgrow : ∀ k ≤ 4, k ≤ Module.finrank (ZMod 2) (LinearMap.ker (N ^ k)) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      have hne : LinearMap.ker (N ^ k) ≠ LinearMap.ker (N ^ (k + 1)) := by
        intro heq
        have he := Module.End.ker_pow_constant heq (8 - k)
        have hk8 : k + (8 - k) = 8 := by omega
        rw [hk8, h8, LinearMap.ker_zero] at he
        have hk0 := LinearMap.ker_eq_top.mp he
        apply h4
        calc
          N ^ 4 = N ^ (k + (4 - k)) := by congr 1; omega
          _ = 0 := by rw [pow_add, hk0, zero_mul]
      have hlt : LinearMap.ker (N ^ k) < LinearMap.ker (N ^ (k + 1)) := by
        refine lt_of_le_of_ne ?_ hne
        rw [pow_succ']
        exact LinearMap.ker_le_ker_comp _ _
      have hd := Submodule.finrank_lt_finrank_of_lt hlt
      have hi := ih (by omega)
      omega
  exact hgrow 4 le_rfl

section PerfectAction
variable {G V : Type*} [Group G] [Group.IsPerfect G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem small_action_trivial (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V ≤ 2) (g : G) (v : V) : ρ g v = v := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card V ≤ Fintype.card (Fin 4) := by
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hdim
  let e : V ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm V) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : G →* Equiv.Perm V := {
    toFun a := {
      toFun := ρ a
      invFun := ρ a⁻¹
      left_inv := by
        intro w
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      right_inv := by
        intro w
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] }
    map_one' := by ext w; simp
    map_mul' := by intro a b; ext w; simp }
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf : f g = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict g) 1)
  exact congrArg (fun a : Equiv.Perm V => a v) hf

private theorem three_le_range (ρ : Representation (ZMod 2) G V)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (D : Module.End (ZMod 2) V) (hne : D ≠ 0)
    (hequiv : ∀ g, D * ρ g = ρ g * D) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range D) := by
  by_contra hdim
  have hstable : ∀ g, LinearMap.range D ≤ (LinearMap.range D).comap (ρ g) := by
    intro g w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨ρ g v, DFunLike.congr_fun (hequiv g) v⟩
  let τ := ρ.subrepresentation (LinearMap.range D) hstable
  have hfix (g : G) (v : V) : ρ g (D v) = D v := by
    have hh := small_action_trivial τ (by omega) g ⟨D v, v, rfl⟩
    exact congrArg Subtype.val hh
  have hann : subspaceCommutator ρ ⊤ ⊤ ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    rintro w ⟨g, _, v, _, rfl⟩
    change D (ρ g v - v) = 0
    rw [map_sub]
    have hh := DFunLike.congr_fun (hequiv g) v
    change D (ρ g v) = ρ g (D v) at hh
    rw [hh, hfix, sub_self]
  exact hne (LinearMap.ker_eq_top.mp (top_unique (hfull ▸ hann)))

end PerfectAction

/-- A faithful binary SL₂(7)-module generated by its displacements has dimension
at least seven. No irreducibility or composition-factor hypothesis is needed. -/
public theorem seven_le_finrank_of_faithful_full
    (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) V)
    (hσ : Function.Injective σ) (hfull : subspaceCommutator σ ⊤ ⊤ = ⊤) :
    7 ≤ Module.finrank (ZMod 2) V := by
  have hz : σ (-1) ≠ 1 := by
    intro he
    apply neg_one_ne_one
    apply hσ
    simpa only [map_one] using he
  let : Nontrivial (Module.End (ZMod 2) V) := ⟨⟨σ (-1), 1, hz⟩⟩
  let : CharP (Module.End (ZMod 2) V) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (Module.End (ZMod 2) V)).injective 2
  let N : Module.End (ZMod 2) V := σ x - 1
  have h4 : N ^ 4 = σ (-1) - 1 := by
    change (σ x - 1) ^ (2 ^ 2) = _
    rw [sub_pow_char_pow_of_commute 2 2 (Commute.one_right _), ← map_pow, one_pow]
    exact congrArg (fun g => σ g - 1) x_four
  have h8 : N ^ 8 = 0 := by
    change (σ x - 1) ^ (2 ^ 3) = _
    rw [sub_pow_char_pow_of_commute 2 3 (Commute.one_right _), ← map_pow, one_pow]
    change σ (x ^ 8) - 1 = 0
    rw [x_eight, map_one, sub_self]
  have h4ne : N ^ 4 ≠ 0 := by
    rw [h4]
    exact sub_ne_zero.mpr hz
  have hker := four_le_ker N h8 h4ne
  have hrange : 3 ≤ Module.finrank (ZMod 2) (LinearMap.range (N ^ 4)) := by
    rw [h4]
    apply three_le_range σ hfull (σ (-1) - 1) (sub_ne_zero.mpr hz)
    intro g
    rw [sub_mul, mul_sub, one_mul, mul_one, ← map_mul, ← map_mul]
    simp
  have hdim := LinearMap.finrank_range_add_finrank_ker (N ^ 4)
  omega

end Representation.BinaryOffender.SL2SevenCentralProduct
