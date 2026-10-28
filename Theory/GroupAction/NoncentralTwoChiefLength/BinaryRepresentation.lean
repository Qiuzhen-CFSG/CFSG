module

public import Theory.GroupAction.NoncentralTwoChiefLength
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic

/-!
# Fixed indices of binary representations

A binary representation gives an action by automorphisms on the literal
multiplicative additive group. For a cyclic actor, the fixed index is unchanged
by contragredient duality: the fixed kernels of an operator and its transpose
have the same dimension. For a cubic actor, a surjective intertwiner with
pointwise fixed kernel preserves the fixed index, since a fixed displacement
has both order dividing two and orbit sum zero over three terms.

These linear-algebra facts support the concrete module calculations in
Aschbacher–Smith 13.8.33, printed p.968. Transport retains both the actor map
and the actual equivariant group identification.
-/

@[expose] public section

open Module
namespace Representation.BinaryFixedPoints
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The literal action on the additive group, written multiplicatively. -/
@[reducible] def action (ρ : Representation (ZMod 2) G V) :
    MulDistribMulAction G (Multiplicative V) where
  smul g v := Multiplicative.ofAdd (ρ g v.toAdd)
  one_smul v := by change ρ 1 v.toAdd = v.toAdd; simp
  mul_smul g h v := by change ρ (g * h) v.toAdd = ρ g (ρ h v.toAdd); simp
  smul_one g := by change ρ g 0 = 0; exact map_zero _
  smul_mul g v w := by
    change ρ g (v.toAdd + w.toAdd) = ρ g v.toAdd + ρ g w.toAdd
    exact map_add _ _ _

/-- The index of the actual fixed subgroup for this representation. -/
noncomputable def fixedIndex (ρ : Representation (ZMod 2) G V) : ℕ :=
  letI := action ρ
  (FixedPoints.subgroup G (Multiplicative V)).index

@[simp] theorem action_smul (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    letI := action ρ
    g • Multiplicative.ofAdd v = Multiplicative.ofAdd (ρ g v) := rfl

/-- The dual action is contragredient, including the inverse on the actor. -/
theorem dual_action_smul (ρ : Representation (ZMod 2) G V) (g : G)
    (f : Module.Dual (ZMod 2) V) (v : V) :
    letI := action ρ.dual
    (g • Multiplicative.ofAdd f).toAdd v = f (ρ g⁻¹ v) := rfl

/-- The fixed subgroup and the invariant subspace have the same elements. -/
def fixedEquiv (ρ : Representation (ZMod 2) G V) :
    letI := action ρ
    FixedPoints.subgroup G (Multiplicative V) ≃ ρ.invariants := by
  letI := action ρ
  exact { toFun := fun v => ⟨v.val.toAdd, v.property⟩
          invFun := fun v => ⟨Multiplicative.ofAdd v.val, v.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

theorem fixedIndex_mul_card (ρ : Representation (ZMod 2) G V) [Finite V] :
    fixedIndex ρ * Nat.card ρ.invariants = Nat.card V := by
  let := action ρ
  have h := (FixedPoints.subgroup G (Multiplicative V)).index_mul_card
  rw [Nat.card_congr (fixedEquiv ρ)] at h
  exact h

theorem fixedIndex_eq_of_equivariant {A X : Type*} [Group A] [Group X]
    (ρ : Representation (ZMod 2) G V) [MulDistribMulAction A X]
    (f : A →* G) (hf : Function.Surjective f)
    (e : X ≃* Multiplicative V)
    (heq : ∀ a w, e (a • w) = Multiplicative.ofAdd (ρ (f a) (e w).toAdd)) :
    (FixedPoints.subgroup A X).index = fixedIndex ρ := by
  let := action ρ
  exact FixedPoints.index_eq_of_equivariant_surjective_actor f hf e heq

/-- A source group action may use a surjective actor map and any genuine
compatible module identification. -/
theorem cubicLength_eq_of_equivariant {A X : Type*} [Group A] [Group X]
    (ρ : Representation (ZMod 2) G V) [MulDistribMulAction A X]
    (f : A →* G) (hf : Function.Surjective f)
    (e : X ≃* Multiplicative V)
    (heq : ∀ a x, e (a • x) = Multiplicative.ofAdd (ρ (f a) (e x).toAdd)) :
    FixedPoints.cubicLength A X = Nat.log 4 (fixedIndex ρ) := by
  unfold FixedPoints.cubicLength
  rw [fixedIndex_eq_of_equivariant ρ f hf e heq]

private theorem invariants_eq_ker (ρ : Representation (ZMod 2) G V)
    (g : G) (hg : ∀ a, a ∈ Subgroup.zpowers g) :
    ρ.invariants = (ρ g - LinearMap.id).ker := by
  ext v
  rw [ρ.mem_invariants_iff_of_forall_mem_zpowers g hg]
  simp [LinearMap.mem_ker, sub_eq_zero]

private theorem dual_invariants_eq_ker (ρ : Representation (ZMod 2) G V)
    (g : G) (hg : ∀ a, a ∈ Subgroup.zpowers g) :
    ρ.dual.invariants = (ρ g - LinearMap.id).dualMap.ker := by
  ext f
  rw [ρ.dual.mem_invariants_iff_of_forall_mem_zpowers g hg]
  rw [LinearMap.ext_iff]
  change (∀ v, f (ρ g⁻¹ v) = f v) ↔ _
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have hv := h (ρ g v)
    simpa [map_sub, sub_eq_zero] using hv.symm
  · intro h v
    have hv := LinearMap.congr_fun h (ρ g⁻¹ v)
    have he : f v - f (ρ g⁻¹ v) = 0 := by simpa [map_sub] using hv
    exact (sub_eq_zero.mp he).symm

/-- Contragredient duality preserves the fixed index for a cyclic actor. -/
theorem fixedIndex_dual (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V] [Finite V]
    (g : G) (hg : ∀ a, a ∈ Subgroup.zpowers g) :
    fixedIndex ρ.dual = fixedIndex ρ := by
  let : Finite (Module.Dual (ZMod 2) V) :=
    Finite.of_injective (fun f => (f : V → ZMod 2)) DFunLike.coe_injective
  have hd : finrank (ZMod 2) ρ.dual.invariants = finrank (ZMod 2) ρ.invariants := by
    rw [dual_invariants_eq_ker ρ g hg, invariants_eq_ker ρ g hg]
    have h₁ := (ρ g - LinearMap.id).finrank_range_add_finrank_ker
    have h₂ := (ρ g - LinearMap.id).dualMap.finrank_range_add_finrank_ker
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h₂
    omega
  have hc : Nat.card ρ.dual.invariants = Nat.card ρ.invariants := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ρ.dual.invariants),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ρ.invariants), hd]
  have hv : Nat.card (Module.Dual (ZMod 2) V) = Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) V),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Subspace.dual_finrank_eq]
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ρ.invariants))
  rw [← hc, fixedIndex_mul_card, hv, hc, fixedIndex_mul_card]

/-- A fixed kernel contributes no index to a binary cubic action. -/
theorem fixedIndex_eq_of_surjective_trivial_kernel
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (g : G) (hg : ∀ a, a ∈ Subgroup.zpowers g) (hc : g ^ 3 = 1)
    (f : V →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (heq : ∀ a v, f (ρ a v) = σ a (f v))
    (hker : ∀ v, f v = 0 → ρ g v = v) : fixedIndex ρ = fixedIndex σ := by
  let := action ρ
  let := action σ
  let F : Multiplicative V →* Multiplicative W := f.toAddMonoidHom.toMultiplicative
  have hF : Function.Surjective F := hf
  have he : (FixedPoints.subgroup G (Multiplicative W)).comap F =
      FixedPoints.subgroup G (Multiplicative V) := by
    ext v
    constructor
    · intro hv
      have hv' : σ g (f v.toAdd) = f v.toAdd := hv g
      have hd : f (ρ g v.toAdd + v.toAdd) = 0 := by
        rw [map_add, heq, hv', ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      have hh := hker (ρ g v.toAdd + v.toAdd) hd
      rw [map_add, add_comm (ρ g v.toAdd) v.toAdd] at hh
      have hs : ρ g (ρ g v.toAdd) = v.toAdd := add_right_cancel hh
      have ht : ρ g (ρ g (ρ g v.toAdd)) = v.toAdd := by
        calc
          _ = ρ (g * (g * g)) v.toAdd := by simp [map_mul]
          _ = v.toAdd := by rw [← pow_three, hc]; simp
      have hgfix : ρ g v.toAdd = v.toAdd := (congrArg (ρ g) hs).symm.trans ht
      exact (ρ.mem_invariants_iff_of_forall_mem_zpowers g hg v.toAdd).mpr hgfix
    · intro hv a
      change σ a (f v.toAdd) = f v.toAdd
      rw [← heq, show ρ a v.toAdd = v.toAdd from hv a]
  change (FixedPoints.subgroup G (Multiplicative V)).index = _
  rw [← he]
  exact (FixedPoints.subgroup G (Multiplicative W)).index_comap_of_surjective hF

end Representation.BinaryFixedPoints
