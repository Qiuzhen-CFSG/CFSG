module

public import Theory.Representation.QuadraticFourGroup.TensorClassification
public import Theory.Representation.SpecialLinearRestriction
public import Theory.SpecificGroups.SL2.AffineFreeAction
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Odd component commutators on quadratic tensor sections

A faithful two-dimensional action of a perfect group has determinant one.
An odd-order element fixing a nonzero vector would be unipotent and hence
trivial. Tensoring with the second natural factor preserves this fixed-point
freeness. On the actual irreducible subquotient, a nontrivial odd element in
one factor therefore displaces all four field dimensions. The general
commutator-rank inequality bounds this by twice the displacement of its
first entry in the original module.

This supplies the quantitative input of GLS2, Theorem 26.24, final paragraph,
without requiring the chosen tensor composition factor to be invariant under
the normalizing actor. The group-theoretic commutator witness remains literal.
-/

public section

open Subgroup Theory.GroupTheory Matrix
open scoped TensorProduct
namespace Representation.QuadraticFourGroup
open TensorClassification BinaryOffender NaturalTensor
variable {J F : Type*} [Group J] [Group.IsPerfect J] [Field F] [CharP F 2]
  (τ : Representation F J (Fin 2 → F)) (hτ : Function.Injective τ)

include hτ in
theorem faithful_plane_odd_fixed (g : J) (ho : Odd (orderOf g)) (hne : g ≠ 1)
    (v : Fin 2 → F) (hv : τ g v = v) : v = 0 := by
  obtain ⟨f,e,hf,he⟩ := τ.exists_specialLinear_restriction hτ
    (det_eq_one_of_perfect τ) (d := 2) (by simp)
  by_contra hvne
  have hev : e v ≠ 0 := fun hh => hvne (e.injective (hh.trans e.map_zero.symm))
  have hfix : (f g).val *ᵥ (e v) = e v := by
    rw [← specialLinearNatural_apply, ← he, hv]
  have hg : f g = 1 := Matrix.SpecialLinearGroup.AffineFreeAction.eq_one_of_fixed_vector_of_coprime
    (p := 2) (f g) ho.coprime_two_left
    (by rw [← map_pow, pow_orderOf_eq_one, map_one]) (e v) hev hfix
  exact hne (hf (hg.trans f.map_one.symm))

variable {n : ℕ} [Group.IsPerfect (Factor n)]

theorem binaryTensor_first_odd_fixed
    (τ₁ τ₂ : Representation (GaloisField 2 n) (Factor n) (NaturalSpace n))
    (hτ₁ : Function.Injective τ₁)
    (g : Factor n) (ho : Odd (orderOf g)) (hne : g ≠ 1)
    (v : TensorSpace n) (hv : binaryTensor τ₁ τ₂ (g,1) v = v) : v = 0 := by
  have hi : Function.Injective (τ₁ g - (1 : Module.End (GaloisField 2 n) (NaturalSpace n))) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    exact faithful_plane_odd_fixed τ₁ hτ₁ g ho hne w (sub_eq_zero.mp hw)
  have hit := Module.Flat.rTensor_preserves_injective_linearMap
    (M := NaturalSpace n) (τ₁ g - 1) hi
  apply hit
  rw [map_zero]
  change TensorProduct.map (τ₁ g - 1) LinearMap.id v = 0
  have hm : TensorProduct.map (τ₁ g - 1) LinearMap.id =
      TensorProduct.map (τ₁ g) (τ₂ 1) - 1 := by
    rw [map_one]
    ext x y
    simp [TensorProduct.sub_tmul]
  rw [hm]
  exact sub_eq_zero.mpr hv

theorem IsNaturalTensorAlong.first_odd_fixed
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {π : E →* Factor n × Factor n} {σ : Representation (ZMod 2) E W}
    (h : IsNaturalTensorAlong π σ)
    (x : E) (g : Factor n) (hg : π x = (g,1))
    (ho : Odd (orderOf g)) (hne : g ≠ 1)
    (w : W) (hw : σ x w = w) : w = 0 := by
  obtain ⟨τ₁,τ₂,hτ₁,_,⟨e⟩⟩ := h
  have he := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x w
  change e (σ x w) = binaryTensor τ₁ τ₂ (π x) (e w) at he
  rw [hw, hg] at he
  have hz := binaryTensor_first_odd_fixed τ₁ τ₂ hτ₁ g ho hne (e w) he.symm
  exact e.toLinearEquiv.injective (hz.trans e.toLinearEquiv.map_zero.symm)

theorem IsNaturalTensorAlong.first_odd_operatorFixedCodim
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {π : E →* Factor n × Factor n} {σ : Representation (ZMod 2) E W}
    (h : IsNaturalTensorAlong π σ) (hn : n ≠ 0)
    (x : E) (g : Factor n) (hg : π x = (g,1))
    (ho : Odd (orderOf g)) (hne : g ≠ 1) :
    operatorFixedCodim (σ x) = 4 * n := by
  have hk : (σ x - 1).ker = ⊥ := LinearMap.ker_eq_bot'.mpr fun w hw =>
    h.first_odd_fixed x g hg ho hne w (sub_eq_zero.mp hw)
  have hc := operatorFixedCodim_add_finrank (σ x)
  rw [hk, finrank_bot, add_zero] at hc
  rw [hc]
  obtain ⟨τ₁,τ₂,_,_,⟨e⟩⟩ := h
  rw [e.toLinearEquiv.finrank_eq]
  rw [← Module.finrank_mul_finrank (ZMod 2) (GaloisField 2 n) (TensorSpace n),
    GaloisField.finrank 2 hn]
  simp [TensorSpace, NaturalSpace]
  omega

theorem IsIrreducibleSection.operatorFixedCodim_le
    {H X Y : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y]
    {ρ : Representation (ZMod 2) H X} {σ : Representation (ZMod 2) H Y}
    (h : IsIrreducibleSection ρ σ) (x : H) :
    operatorFixedCodim (σ x) ≤ operatorFixedCodim (ρ x) := by
  obtain ⟨_,U,N,⟨e⟩⟩ := h
  have he := operatorFixedCodim_eq_of_equiv (N.quotientRepresentation x) (σ x)
    e.toLinearEquiv (fun v => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x v)
  rw [← he]
  exact operatorFixedCodim_le_of_section (ρ x) U.toSubmodule (U.toRepresentation x)
    (N.quotientRepresentation x) N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective
    (fun _ => rfl) (fun _ => rfl)

theorem IsNaturalTensorAlong.first_odd_commutator_bound
    {G E V W : Type*} [Group G] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (ι : E →* G)
    {π : E →* Factor n × Factor n} {σ : Representation (ZMod 2) E W}
    (hs : IsIrreducibleSection (ρ.comp ι) σ)
    (h : IsNaturalTensorAlong π σ) (hn : n ≠ 0)
    (x : E) (g : Factor n) (hg : π x = (g,1))
    (ho : Odd (orderOf g)) (hne : g ≠ 1)
    (a b : G) (hx : ι x = a * b * a⁻¹ * b⁻¹) :
    2 * n ≤ fixedCodim ρ (zpowers a) := by
  have hc := hs.operatorFixedCodim_le x
  rw [h.first_odd_operatorFixedCodim hn x g hg ho hne] at hc
  change 4 * n ≤ operatorFixedCodim (ρ (ι x)) at hc
  rw [hx] at hc
  have hb := fixedCodim_commutator_le_twice ρ a b
  rw [fixedCodim_zpowers_eq_displacement_rank] at hb
  change operatorFixedCodim (ρ (a * b * a⁻¹ * b⁻¹)) ≤
    2 * fixedCodim ρ (zpowers a) at hb
  omega
end Representation.QuadraticFourGroup
