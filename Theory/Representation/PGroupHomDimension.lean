module

public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Intertwiner dimensions for modular p-group representations

For a finite p-group in characteristic p, the dimension of equivariant maps
from V to W is at most dim(V) times dim(W^G). Choose a nonzero fixed vector
in V and evaluate there. The kernel descends injectively to maps out of the
quotient by that fixed line. Induction on dim(V), followed by rank-nullity,
proves the bound. Applying the same argument to contragredient maps gives
the dual bound dim(W) times dim((V*)^G).

These are the two linear Hom-space bounds used in Guralnick–Malle,
Classification of 2F-modules II, author manuscript, Corollary 2.11(a),
pp.9–10. In particular, both apply to the common endomorphism centralizer;
they do not estimate only a single group element.
-/

public noncomputable section
namespace Representation
namespace PGroupHomDimension

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k G W)

private def evalFixed (v : V) (hv : ∀ g, ρ g v = v) :
    IntertwiningMap ρ σ →ₗ[k] invariants σ where
  toFun f := ⟨f v, fun g => by rw [← f.isIntertwining, hv]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fixedLine (v : V) (hv : ∀ g, ρ g v = v) : Subrepresentation ρ where
  toSubmodule := Submodule.span k {v}
  apply_mem_toSubmodule g x hx := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hv]
    exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))

private def descend (v : V) (hv : ∀ g, ρ g v = v) :
    (evalFixed ρ σ v hv).ker →ₗ[k]
      IntertwiningMap (fixedLine ρ v hv).quotientRepresentation σ where
  toFun f :=
    { toLinearMap := (fixedLine ρ v hv).toSubmodule.liftQ f.val.toLinearMap (by
        intro x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        have hz : f.val v = 0 := congrArg Subtype.val f.property
        simp [hz])
      isIntertwining' g := by
        ext x
        change f.val (ρ g x) = σ g (f.val x)
        exact LinearMap.congr_fun (f.val.isIntertwining' g) x }
  map_add' f h := by
    ext x
    obtain ⟨w, rfl⟩ := (fixedLine ρ v hv).toSubmodule.mkQ_surjective x
    rfl
  map_smul' c f := by
    ext x
    obtain ⟨w, rfl⟩ := (fixedLine ρ v hv).toSubmodule.mkQ_surjective x
    rfl

private theorem descend_injective (v : V) (hv : ∀ g, ρ g v = v) :
    Function.Injective (descend ρ σ v hv) := by
  intro f h he
  apply Subtype.ext
  ext x
  exact congrArg (fun a : IntertwiningMap (fixedLine ρ v hv).quotientRepresentation σ =>
    a ((fixedLine ρ v hv).toSubmodule.mkQ x)) he

/-- The common fixed space of the target bounds equivariant maps from any
finite-dimensional representation of a modular p-group. -/
theorem finrank_le [Finite G] [FiniteDimensional k V] [FiniteDimensional k W]
    (hc : ringChar k ≠ 0) (hG : IsPGroup (ringChar k) G) :
    Module.finrank k (IntertwiningMap ρ σ) ≤
      Module.finrank k V * Module.finrank k (invariants σ) := by
  classical
  generalize hn : Module.finrank k V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hV : Nontrivial V
    · let : Nontrivial V := hV
      obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector hc hG ρ
      let U := fixedLine ρ v hfix
      have hU : Module.finrank k U.toSubmodule = 1 := finrank_span_singleton hv
      have hsum := U.toSubmodule.finrank_quotient_add_finrank
      have hlt : Module.finrank k (V ⧸ U.toSubmodule) < n := by omega
      have hquot := ih _ hlt U.quotientRepresentation rfl
      have hker := LinearMap.finrank_le_finrank_of_injective
        (f := descend ρ σ v hfix) (descend_injective ρ σ v hfix)
      have hrange := (evalFixed ρ σ v hfix).range.finrank_le
      have hdim := (evalFixed ρ σ v hfix).finrank_range_add_finrank_ker
      change Module.finrank k (IntertwiningMap U.quotientRepresentation σ) ≤
        Module.finrank k (V ⧸ U.toSubmodule) * Module.finrank k (invariants σ) at hquot
      nlinarith
    · let : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
      let : Subsingleton (IntertwiningMap ρ σ) :=
        Function.Injective.subsingleton (IntertwiningMap.toLinearMap_injective ρ σ)
      rw [Module.finrank_zero_of_subsingleton]
      exact Nat.zero_le _

private def dual (f : IntertwiningMap ρ σ) : IntertwiningMap σ.dual ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    ext l v
    change l (σ g⁻¹ (f v)) = l (f (ρ g⁻¹ v))
    rw [f.isIntertwining]

private def dualLinear : IntertwiningMap ρ σ →ₗ[k] IntertwiningMap σ.dual ρ.dual where
  toFun := dual ρ σ
  map_add' f h := by ext l v; exact map_add l (f v) (h v)
  map_smul' c f := by ext l v; exact map_smul l c (f v)

private theorem dualLinear_injective : Function.Injective (dualLinear ρ σ) := by
  intro f h he
  ext v
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k _).mp
  intro l
  have he' := congrArg (fun a : IntertwiningMap σ.dual ρ.dual => a l v) he
  rw [map_sub]
  exact sub_eq_zero.mpr he'

/-- The dual common fixed space gives the symmetric Hom-space bound. -/
theorem finrank_le_dual [Finite G] [FiniteDimensional k V] [FiniteDimensional k W]
    (hc : ringChar k ≠ 0) (hG : IsPGroup (ringChar k) G) :
    Module.finrank k (IntertwiningMap ρ σ) ≤
      Module.finrank k W * Module.finrank k (invariants ρ.dual) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := dualLinear ρ σ) (dualLinear_injective ρ σ)
  have hdual := finrank_le σ.dual ρ.dual hc hG
  rw [Subspace.dual_finrank_eq] at hdual
  exact h.trans hdual

end PGroupHomDimension
end Representation
