module
public import Theory.Representation.ExchangedProductDisplacement
public import Theory.Representation.Quotient
public import Theory.Representation.SchurLinearOperator
public import Theory.Representation.SL2.SchurTensorDisplacement
public import Theory.Representation.Suzuki.SmallDegree.Classification
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent
public import Theory.Representation.Suzuki.ComponentPairDegree

/-!
# The three-eighths bound for an exchanged Suzuki pair

The concrete Suzuki tensor classification makes every faithful absolutely
irreducible factor at least four-dimensional. The exact exchanged-product
calculation therefore gives displacement at least three-eighths of the whole
module. Passing through the actual endomorphism field and its algebraic closure
preserves the original operator and descends this ratio to binary dimension.

Multiplication marks a centerless component pair by two copies of the original
component. Conjugation by its genuine involution swaps those coordinates. This
connects the estimate to the literal pair, without a supplied tensor model or
an assumption that an arbitrary constituent is invariant.

The Chapter 10 natural-constituent exclusion supplies the proved stable
constituent and Schur linearity. Source: Aschbacher--Smith D.3.7--9,
printed pp.197--201; application D.3.21 and10.1.1, pp.204--207 and741.
-/

public noncomputable section
open scoped TensorProduct MonoidAlgebra
open Module Representation
namespace Representation.Suzuki
open Representation.FrobeniusTensor
open BenderSuzuki.MatrixGroups

/-- A faithful simple Suzuki factor has degree at least four over an
algebraically closed field of characteristic two. -/
theorem absolute_finrank_four_le
    {K J W : Type*} [Field K] [IsAlgClosed K] [CharP K 2] [Group J]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (r : ℕ) (hr : 0 < r) (e : J ≃* SuzukiMatrixGroup r)
    (τ : Representation K J W) (hi : τ.IsIrreducible) (hf : Function.Injective τ) :
    4 ≤ finrank K W := by
  let : Algebra (ZMod 2) K := ZMod.algebra _ 2
  let : Algebra (SuzukiNatural.F r) K :=
    (IsAlgClosed.lift : SuzukiNatural.F r →ₐ[ZMod 2] K).toRingHom.toAlgebra
  have hτ : IsIrreducible (τ.comp e.symm.toMonoidHom) :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr hi
  obtain ⟨I,hI,⟨E⟩⟩ := SuzukiSmallDegree.exists_nonempty_tensorRep_equiv (by omega : 1 ≤ r)
    (τ.comp e.symm.toMonoidHom) hτ (hf.comp e.symm.injective)
  rw [E.toLinearEquiv.finrank_eq,SuzukiSmallDegree.finrank_tensorSpace]
  have h := Nat.pow_le_pow_right (by decide : 0 < 4) (Finset.card_pos.mpr hI)
  simpa using h

/-- The three-eighths exchange bound descends through the actual Schur field
to the original binary Suzuki-product module and the original operator. -/
theorem binary_product_exchange_displacement
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (r : ℕ) (hr : 0 < r) (e : J ≃* SuzukiMatrixGroup r)
    (ρ : Representation (ZMod 2) (J × J) V) (hi : ρ.IsIrreducible)
    (hf : Function.Injective ρ)
    (T : Module.End (ZMod 2) V) (h2 : T*T=1)
    (hT : ∀ g v, T (ρ g v) = ρ (g.2,g.1) (T v))
    (hc : ∀ (f : IntertwiningMap ρ ρ) v, T (f v) = f (T v)) :
    3 * finrank (ZMod 2) V ≤ 8 * finrank (ZMod 2) (T-1).range := by
  let := hi
  let E := SchurField ρ
  let F := Closure ρ
  let S := SchurOperator.linear ρ T hc
  let R := S.baseChange F
  have hS2 : S*S = 1 := SchurOperator.linear_square ρ T hc h2
  have hR2 : R*R = 1 := by
    rw [←LinearMap.baseChange_mul,hS2,LinearMap.baseChange_one]
  have hS (g : J × J) : S * ρ.endFieldRep g = ρ.endFieldRep (g.2,g.1) * S := by
    ext v
    exact SchurOperator.linear_intertwines ρ T hc MulEquiv.prodComm hT g v
  have hR (g : J × J) (v) : R (absoluteRep ρ g v) = absoluteRep ρ (g.2,g.1) (R v) := by
    have h := congrArg (fun f : Module.End E ρ.asModule => f.baseChange F) (hS g)
    rw [LinearMap.baseChange_mul,LinearMap.baseChange_mul] at h
    exact LinearMap.congr_fun h v
  have hb := ExchangedProduct.three_mul_finrank_le_eight_displacement (absoluteRep ρ)
    (absoluteRep_injective ρ hf) (fun d τ hi hf => by
      simpa using absolute_finrank_four_le r hr e τ hi hf) R hR2 hR
  change 3 * finrank F (F ⊗[E] ρ.asModule) ≤ 8 * finrank F (S.baseChange F - 1).range at hb
  rw [Module.finrank_baseChange,SL2.SchurTensorDisplacement.displacement_rank_baseChange] at hb
  exact SchurOperator.ratio_descent ρ T hc 3 8 hb
end Representation.Suzuki

namespace Representation.Suzuki
open Subgroup Theory.GroupTheory

/-- Multiplication marks a centerless exchanged component pair by two copies
of the original component. Conjugation by the actual involution swaps the
coordinates in this marking. -/
theorem exchanged_pair_coordinates
    {Γ : Type*} [Group Γ] (J : Subgroup Γ) (hJ : IsComponent Γ J)
    (hZ : center J = ⊥) (a : Γ) (h2 : a*a=1)
    (han : a ∉ normalizer (J : Set Γ)) :
    ∃ e : J × J ≃* ↥(J ⊔ J.map (MulAut.conj a).toMonoidHom),
      (∀ x y, (e (x,y) : Γ) = x * (a * y * a⁻¹)) ∧
      ∀ x y, a * (e (x,y) : Γ) * a⁻¹ = e (y,x) := by
  let K := J.map (MulAut.conj a).toMonoidHom
  have hne : J ≠ K := fun he => han (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : J ≤ centralizer (K : Set Γ) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne (hJ.map_conj a) hne)
  have hd : Disjoint J K := by
    apply disjoint_def.mpr
    intro x hxJ hxK
    have hz : (⟨x,hxJ⟩ : J) ∈ center J := mem_center_iff.mpr fun j =>
      Subtype.ext ((hc j.property x hxK).symm)
    exact congrArg Subtype.val (show (⟨x,hxJ⟩ : J) = 1 from mem_bot.mp (hZ ▸ hz))
  obtain ⟨e₀,he₀⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting J K hd hc
  let q : J ≃* K := (MulAut.conj a).subgroupMap J
  let e := ((MulEquiv.refl J).prodCongr q).trans e₀
  have he (x y : J) : (e (x,y) : Γ) = x * (a*y*a⁻¹) := he₀ x (q y)
  refine ⟨e,he,?_⟩
  intro x y
  rw [he,he]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left h2
  have hcc : (a*(x : Γ)*a⁻¹)*(y : Γ) = y*(a*x*a⁻¹) :=
    hc y.property _ (mem_map_of_mem _ x.property)
  calc
    a * (x * (a*y*a⁻¹)) * a⁻¹ = (a*(x : Γ)*a⁻¹)*(y : Γ) := by
      rw [hai]
      simp only [mul_assoc,h2,mul_one]
    _ = y*(a*x*a⁻¹) := hcc

/-- The exact component action and its genuine exchanger satisfy the
three-eighths bound, without any assumed tensor coordinates. -/
theorem exchanged_component_displacement
    {Γ V : Type*} [Group Γ] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (J : Subgroup Γ) (hJ : IsComponent Γ J)
    (a : Γ) (h2 : a*a=1) (han : a ∉ normalizer (J : Set Γ))
    (r : ℕ) (hr : 0 < r) (eJ : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)
    (ρ : Representation (ZMod 2) ↥(J ⊔ J.map (MulAut.conj a).toMonoidHom) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (T : Module.End (ZMod 2) V) (hT2 : T*T=1)
    (hT : ∀ (x y : ↥(J ⊔ J.map (MulAut.conj a).toMonoidHom)),
      a * (x : Γ) * a⁻¹ = y → ∀ v, T (ρ x v) = ρ y (T v))
    (hc : ∀ (f : IntertwiningMap ρ ρ) v, T (f v) = f (T v)) :
    3 * finrank (ZMod 2) V ≤ 8 * finrank (ZMod 2) (T-1).range := by
  let : Fact (0 < r) := ⟨hr⟩
  let : IsSimpleGroup J := eJ.isSimpleGroup
  let : IsQuasisimple J := hJ.2
  have hZ : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp h))
  obtain ⟨e,_,he⟩ := exchanged_pair_coordinates J hJ hZ a h2 han
  let σ : Representation (ZMod 2) (J × J) V := ρ.comp e.toMonoidHom
  have hs : σ.IsIrreducible := (irreducible_comp_surjective_iff e.toMonoidHom e.surjective ρ).mpr hi
  apply binary_product_exchange_displacement r hr eJ σ hs (hf.comp e.injective) T hT2
  · intro g v
    exact hT (e g) (e (g.2,g.1)) (he g.1 g.2) v
  · intro f v
    let f' : IntertwiningMap ρ ρ := {
      toLinearMap := f.toLinearMap
      isIntertwining' x := by
        have h := f.isIntertwining' (e.symm x)
        change f.toLinearMap * ρ (e (e.symm x)) = ρ (e (e.symm x)) * f.toLinearMap at h
        change f.toLinearMap * ρ x = ρ x * f.toLinearMap
        simpa only [e.apply_symm_apply] using h }
    exact hc f' v
end Representation.Suzuki

