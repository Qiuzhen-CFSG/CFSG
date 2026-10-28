module
public import Theory.Representation.BinaryOffender.Homogeneous.FaithfulMultiplicity
public import Theory.Representation.Suzuki.SupportMultiplicity
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# A faithful Suzuki action over the natural support field

Take the literal Suzuki orbit of an irreducible support--actor constituent.
Its finite copy coordinates retain the entire support action. A natural SL₃
subgroup makes the commutant scalar over the original field, so the commuting
Suzuki group acts faithfully on the multiplicity coordinates over that field.
Faithfulness follows from simplicity and the vanishing original fixed space.
The coordinates also retain the starred actor needed to bound multiplicity.

Source: Aschbacher--Smith A.1.41--42 and D.3.9, pp.31--32,200--201;
application to the centralizing branch of 10.2.3, printed p.745.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace Representation.Suzuki
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Field F] [Algebra (ZMod 2) F]

/-- The actual Suzuki orbit carries a faithful action on its natural-field multiplicities. -/
theorem natural_support_faithful_multiplicity
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (eK : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (X J : Subgroup G) (hJX : J ≤ X) (hc : K ≤ centralizer (X : Set G))
    (R : Submodule (ZMod 2) V) (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation)
    (j : J ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (b : R ≃ₗ[ZMod 2] (Fin 3 → F))
    (hb : ∀ (g : J) v, b ((invariantSubspace ρ X R hR).toRepresentation
      (inclusion hJX g) v) = specialLinearNatural 3 (j g) (b v)) :
    ∃ n : ℕ, ∃ e : orbitSpan ρ K R ≃ₗ[ZMod 2] (Fin n → R),
      (∀ (x : X) (v : orbitSpan ρ K R),
        e ⟨ρ x v,(CommutingMultiplicity.orbit_invariant_of_commuting ρ X K hc R hR
          x.property v).2 v.property⟩ =
          fun i => (invariantSubspace ρ X R hR).toRepresentation x (e v i)) ∧
      ∃ f : K →* Matrix.GeneralLinearGroup (Fin n) F, Function.Injective f := by
  classical
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup K := eK.isSimpleGroup
  let O := orbitSpan ρ K R
  let U := invariantSubspace ρ K O (orbitSpan_invariant ρ K R)
  have hn : U ≠ ⊥ := by
    intro hh
    have hO : O = ⊥ := congrArg Subrepresentation.toSubmodule hh
    have hR0 : R = ⊥ := bot_unique ((le_orbitSpan ρ K R).trans hO.le)
    exact ((Subrepresentation.irreducible_iff_isAtom _).mp hi).ne_bot
      (Subrepresentation.toSubmodule_injective hR0)
  have hf := simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp K.subtype) hfix U hn
  obtain ⟨n,e,he⟩ := CommutingMultiplicity.commuting_orbit_coordinates ρ X K hc R hR hi
  have hXO := CommutingMultiplicity.orbit_invariant_of_commuting ρ X K hc R hR
  let α := (invariantSubspace ρ X O hXO).toRepresentation.comp
    ((inclusion hJX).comp j.symm.toMonoidHom)
  let σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F) (Fin 3 → F) :=
    restrictScalars (k := ZMod 2) (specialLinearNatural 3)
  let c := e.trans (LinearEquiv.piCongrRight fun _ => b)
  have hec : ∀ g v, c (α g v) = fun i => σ g (c v i) := by
    intro g v
    change (fun i => b (e _ i)) = _
    have h := he ((inclusion hJX) (j.symm g)) v
    change e (α g v) = _ at h
    rw [h]
    funext i
    exact (hb (j.symm g) _).trans (by rw [j.apply_symm_apply]; rfl)
  have hcomm : ∀ a g v, U.toRepresentation a (α g v) = α g (U.toRepresentation a v) := by
    intro a g v
    apply Subtype.ext
    change ρ a.val (ρ (j.symm g).val v.val) = ρ (j.symm g).val (ρ a.val v.val)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v.val) ((hc a.property _ (hJX (j.symm g).property)).symm)
  have hs (f : (Fin 3 → F) →ₗ[ZMod 2] (Fin 3 → F))
      (hh : ∀ g v, f (σ g v) = σ g (f v)) : ∃ c : F, ∀ v, f v = c • v :=
    SL3OddNaturalNormalizer.centralizer_scalar f.toAddMonoidHom hh
  exact ⟨n,e,he,ScalarMultiplicity.faithful_action_of_copy_coordinates σ hs α
    U.toRepresentation hf hcomm c hec⟩
end Representation.Suzuki
