module
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Field-sized movement on a fixed subspace of a symplectic cover

Let U be an embedded binary central cover of the natural symplectic module.
Suppose T and an element b act through the same symplectic marking. If b
moves C_U(T), then its displacement there has at least the order of the
coefficient field. Fixed-vector lifting first detects the movement in the
natural quotient. Scalar multiples of a moved vector lift back to C_U(T)
and yield distinct commutators, without choosing a splitting of the cover.

This is the fixed-subspace form of the full-cover argument from MS93
(1.5)(ii), used in the original characteristic comparison in (3.7),
printed pp.872--875. The original-star consumer applies it before imposing
any restriction on the field degree.
-/

public noncomputable section
open Matrix Subgroup Representation Representation.OneCohomology
open scoped commutatorElement IsMulCommutative
namespace Representation.SymplecticFourOrthogonalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) (L (K := F)) W}
variable {G : Type*} [Group G] [Finite G]

/-- Nontrivial inner movement on a full fixed preimage has at least field order. -/
theorem fixed_actor_displacement_card_ge
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (T : Subgroup G) (β : T →* L (K := F))
    (hT : ∀ (t : T) (w : W), j (Multiplicative.ofAdd (σ (β t) w)) =
      (t:G)*j (Multiplicative.ofAdd w)*(t:G)⁻¹)
    (b : G) (γ : L (K := F))
    (hb : ∀ w : W, j (Multiplicative.ofAdd (σ γ w)) =
      b*j (Multiplicative.ofAdd w)*b⁻¹)
    (v : G) (hv : v ∈ j.range ⊓ centralizer (T : Set G)) (hn : ⁅v,b⁆ ≠ 1) :
    Nat.card F ≤ Nat.card (⁅j.range ⊓ centralizer (T : Set G),zpowers b⁆ : Subgroup G) := by
  classical
  obtain ⟨w,rfl⟩ := hv.1
  have hw (t : T) : σ (β t) w.toAdd=w.toAdd := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hT]
    change (t:G)*j w*(t:G)⁻¹=j w
    rw [hv.2 t t.property,mul_inv_cancel_right]
  have hn' : binaryNatural γ (p w.toAdd)-p w.toAdd ≠ 0 := by
    intro he
    have hf := cover_fixed_of_projection_fixed p hp γ w.toAdd (sub_eq_zero.mp he)
    have he' := congrArg (fun z => j (Multiplicative.ofAdd z)) hf
    rw [hb,mul_inv_eq_iff_eq_mul] at he'
    exact hn (commutatorElement_eq_one_iff_commute.mpr he'.symm)
  choose lift hlift using fun c : F => hp.1 (c • p w.toAdd)
  have hfix (c : F) (t : T) : σ (β t) (lift c)=lift c := by
    apply cover_fixed_of_projection_fixed p hp
    rw [hlift]
    change (β t).val.val *ᵥ (c • p w.toAdd)=c • p w.toAdd
    rw [Matrix.mulVec_smul]
    have he := congrArg p (hw t)
    rw [p.isIntertwining] at he
    exact congrArg (fun z => c • z) he
  have hlc (c : F) : j (Multiplicative.ofAdd (lift c)) ∈
      j.range ⊓ centralizer (T : Set G) := by
    refine ⟨⟨_,rfl⟩,?_⟩
    intro t ht
    have he := congrArg (fun z => j (Multiplicative.ofAdd z)) (hfix c ⟨t,ht⟩)
    rw [hT,mul_inv_eq_iff_eq_mul] at he
    exact he
  let f : F → (⁅j.range ⊓ centralizer (T : Set G),zpowers b⁆ : Subgroup G) := fun c =>
    ⟨⁅b,j (Multiplicative.ofAdd (lift c))⁆,
      by rw [commutator_comm]; exact commutator_mem_commutator (mem_zpowers b) (hlc c)⟩
  have he (c : F) : (f c:G) = j (Multiplicative.ofAdd (σ γ (lift c)-lift c)) := by
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hb]
    rfl
  have hfi : Function.Injective f := by
    intro a c hac
    have heq := congrArg Subtype.val hac
    rw [he,he] at heq
    have heq' := congrArg p (congrArg Multiplicative.toAdd (hj heq))
    change p (σ γ (lift a)-lift a)=p (σ γ (lift c)-lift c) at heq'
    simp only [map_sub,p.isIntertwining,hlift] at heq'
    change γ.val.val *ᵥ (a • p w.toAdd)-a • p w.toAdd =
      γ.val.val *ᵥ (c • p w.toAdd)-c • p w.toAdd at heq'
    rw [Matrix.mulVec_smul,Matrix.mulVec_smul,←smul_sub,←smul_sub] at heq'
    exact (smul_left_injective F hn') heq'
  exact Nat.card_le_card_of_injective f hfi
end Representation.SymplecticFourOrthogonalCover
