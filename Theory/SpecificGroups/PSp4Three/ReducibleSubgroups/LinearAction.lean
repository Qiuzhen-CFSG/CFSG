module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# Solvability from an invariant subspace

For a faithful linear action preserving W, restriction to W and the induced
map on V/W define homomorphisms. Their common kernel is abelian: its elements
have the form 1 + a, where a kills W and has image in W, so every product of
two such differences is zero. Consequently solvable action images on W and
V/W imply solvability of the original group.

This linear-algebra argument supplies the radicals in the reducible Sp₄(3)
case used for Aschbacher–Smith, Theorem 0.1.2(4), condition K
(`refs/quasithin.pdf`, printed pp.4 and 482).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSp4Three.ReducibleLinear

variable {F V G : Type*} [Field F] [AddCommGroup V] [Module F V] [Group G]

variable (ρ : G →* (V ≃ₗ[F] V)) (W : Submodule F V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W)

include hW in
private theorem map_subspace (g : G) : W.map (ρ g).toLinearMap = W := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hW g v hv
  · intro v hv
    refine ⟨ρ (g⁻¹) v, hW (g⁻¹) v hv, ?_⟩
    simp

def restriction : G →* (W ≃ₗ[F] W) where
  toFun g := (ρ g).ofSubmodules W W (by exact map_subspace ρ W hW g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp] theorem restriction_apply (g : G) (v : W) :
    (restriction ρ W hW g v).val = ρ g v.val := rfl

def quotient : G →* ((V ⧸ W) ≃ₗ[F] (V ⧸ W)) where
  toFun g := Submodule.Quotient.equiv W W (ρ g) (by exact map_subspace ρ W hW g)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => change W.mkQ (ρ 1 x) = W.mkQ x; simp
  map_mul' g h := by
    ext x
    induction x using Submodule.Quotient.induction_on with
    | _ x => change W.mkQ (ρ (g * h) x) = W.mkQ (ρ g (ρ h x)); simp

@[simp] theorem quotient_apply (g : G) (v : V) :
    quotient ρ W hW g (W.mkQ v) = W.mkQ (ρ g v) := rfl

private theorem kernel_commutes (hρ : Function.Injective ρ) {g h : G}
    (hgW : restriction ρ W hW g = 1) (hgQ : quotient ρ W hW g = 1)
    (hhW : restriction ρ W hW h = 1) (hhQ : quotient ρ W hW h = 1) :
    g * h = h * g := by
  have hd (k : G) (hk : quotient ρ W hW k = 1) (v : V) : ρ k v - v ∈ W := by
    apply (Submodule.Quotient.eq W).mp
    exact LinearEquiv.congr_fun hk (W.mkQ v)
  apply hρ
  ext v
  have hgv := congrArg Subtype.val
    (LinearEquiv.congr_fun hgW ⟨ρ h v - v, hd h hhQ v⟩)
  have hhv := congrArg Subtype.val
    (LinearEquiv.congr_fun hhW ⟨ρ g v - v, hd g hgQ v⟩)
  change ρ g (ρ h v - v) = ρ h v - v at hgv
  change ρ h (ρ g v - v) = ρ g v - v at hhv
  rw [map_sub] at hgv hhv
  simp only [map_mul, LinearEquiv.mul_apply]
  calc
    ρ g (ρ h v) = (ρ h v - v) + ρ g v := sub_eq_iff_eq_add.mp hgv
    _ = (ρ g v - v) + ρ h v := by abel
    _ = ρ h (ρ g v) := (sub_eq_iff_eq_add.mp hhv).symm

theorem isSolvable_of_factors (hρ : Function.Injective ρ)
    [Group.IsSolvable (restriction ρ W hW).range]
    [Group.IsSolvable (quotient ρ W hW).range] : Group.IsSolvable G := by
  let factors := (restriction ρ W hW).rangeRestrict.prod (quotient ρ W hW).rangeRestrict
  have hker : ∀ k ∈ factors.ker,
      restriction ρ W hW k = 1 ∧ quotient ρ W hW k = 1 := by
    intro k hk
    have he : factors k = 1 := hk
    exact ⟨congrArg (fun x => x.1.val) he, congrArg (fun x => x.2.val) he⟩
  let : Group.IsSolvable factors.ker := Group.isSolvable_of_comm fun g h => by
    apply Subtype.ext
    exact kernel_commutes ρ W hW hρ (hker g.val g.property).1 (hker g.val g.property).2
      (hker h.val h.property).1 (hker h.val h.property).2
  apply Group.isSolvable_of_ker_le_range factors.ker.subtype factors
  intro g hg
  exact ⟨⟨g, hg⟩, rfl⟩

include hW in
theorem isSolvable_of_subspace (hρ : Function.Injective ρ)
    [Group.IsSolvable (W ≃ₗ[F] W)]
    [Group.IsSolvable ((V ⧸ W) ≃ₗ[F] (V ⧸ W))] : Group.IsSolvable G :=
  isSolvable_of_factors ρ W hW hρ

end Matrix.PSp4Three.ReducibleLinear
