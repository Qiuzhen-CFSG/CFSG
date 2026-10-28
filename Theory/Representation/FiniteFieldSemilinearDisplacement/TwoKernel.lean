module
public import Theory.Representation.FiniteFieldSemilinearDisplacement.Descent
public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.Algebra.Algebra.ZMod
public import Theory.Representation.Quotient

/-!
# Semilinear descent with a two-group coefficient kernel

First take the nonzero fixed space of the coefficient kernel in characteristic
two. It is a vector space over the coefficient field and is invariant under
the whole actor. The quotient acts faithfully on the field, so Galois descent
spans this fixed space with vectors fixed by the whole actor. No restriction
is made on the odd part of the coefficient image.

This supplies the invariant-vector construction on the two-dimensional
multiplicity space in Aschbacher--Smith D.3.21(3), printed p.206.
-/

public section
namespace Representation.FiniteFieldSemilinearDisplacement
open Subgroup
variable {F A V : Type*} [Field F] [Finite F] [CharP F 2]
  [Group A] [Finite A] [AddCommGroup V] [Module (ZMod 2) V]
  [Module F V] [Algebra (ZMod 2) F] [IsScalarTower (ZMod 2) F V]
  [Finite V] [Nontrivial V]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] [IsScalarTower (ZMod 2) F V] in
/-- A two-group coefficient kernel does not obstruct semilinear descent. -/
theorem exists_fixed_vector_of_two_kernel
    (ρ : Representation (ZMod 2) A V) (τ : A →* (F ≃+* F))
    (hsemi : ∀ a c v, ρ a (c • v) = τ a c • ρ a v)
    (hker : IsPGroup 2 τ.ker) :
    ∃ v : V, v ≠ 0 ∧ ∀ a, ρ a v = v := by
  classical
  let W : Submodule F V := {
    carrier := {v | ∀ a : τ.ker, ρ a v = v}
    zero_mem' := by intro a; exact map_zero _
    add_mem' := by intro v w hv hw a; rw [map_add,hv a,hw a]
    smul_mem' := by
      intro c v hv a
      rw [hsemi,MonoidHom.mem_ker.mp a.property,hv a]
      rfl }
  have hstable (a : A) (v : W) : ρ a v.val ∈ W := by
    intro n
    have hn := (inferInstance : τ.ker.Normal).conj_mem n.val n.property a⁻¹
    have hv := v.property ⟨a⁻¹ * n * (a⁻¹)⁻¹,hn⟩
    have hh := congrArg (ρ a) hv
    simpa only [←Module.End.mul_apply,←map_mul,inv_inv,
      mul_assoc,mul_inv_cancel_left] using hh
  let σ : Representation (ZMod 2) A W := {
    toFun a := {
      toFun := fun v => ⟨ρ a v.val,hstable a v⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun c v => Subtype.ext (map_smul _ _ _) }
    map_one' := by ext v; exact LinearMap.congr_fun ρ.map_one v.val
    map_mul' a b := by ext v; exact LinearMap.congr_fun (ρ.map_mul a b) v.val }
  have hk : τ.ker ≤ σ.ker := by
    intro a ha
    apply LinearMap.ext
    intro v
    exact Subtype.ext (v.property ⟨a,ha⟩)
  let Q := A ⧸ τ.ker
  let q := QuotientGroup.mk' τ.ker
  let σq : Representation (ZMod 2) Q W := quotientOfLEKer σ τ.ker hk
  let τq : Q →* (F ≃+* F) := τ.range.subtype.comp
    (QuotientGroup.quotientKerEquivRange τ).toMonoidHom
  have hτq : Function.Injective τq :=
    Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange τ).injective
  have hq (a : A) : τq (q a) = τ a := rfl
  have hsemiq (a : Q) (c : F) (v : W) : σq a (c • v) = τq a c • σq a v := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective τ.ker a
    apply Subtype.ext
    exact hsemi a c v.val
  let : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [ringChar.eq (ZMod 2) 2]; decide : ringChar (ZMod 2) ≠ 0)
    (by simpa only [ringChar.eq (ZMod 2) 2] using hker) (ρ.comp τ.ker.subtype)
  have hvW : v ∈ W := hfix
  let : Nontrivial W := ⟨⟨⟨v,hvW⟩,0,fun hh => hv (congrArg Subtype.val hh)⟩⟩
  let : Fintype Q := Fintype.ofFinite Q
  have hspan := Descent.span_fixed_eq_top σq τq hτq hsemiq
  have hex : ∃ w : W, w ≠ 0 ∧ ∀ a, σq a w = w := by
    by_contra! hn
    have hz : Submodule.span F {w : W | ∀ a, σq a w = w} ≤ ⊥ := by
      apply Submodule.span_le.mpr
      intro w hw
      change w = 0
      by_contra hw0
      obtain ⟨a,ha⟩ := hn w hw0
      exact ha (hw a)
    rw [hspan] at hz
    exact top_ne_bot (le_antisymm hz bot_le)
  obtain ⟨w,hw,hwa⟩ := hex
  refine ⟨w.val,fun hh => hw (Subtype.ext hh),fun a => ?_⟩
  exact congrArg Subtype.val (hwa (q a))
end Representation.FiniteFieldSemilinearDisplacement
