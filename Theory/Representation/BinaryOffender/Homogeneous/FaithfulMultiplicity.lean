module
public import Theory.Representation.BinaryOffender.Homogeneous.CommutingMultiplicity
public import Theory.Representation.ScalarMultiplicity.Faithful
public import Theory.Representation.GeneralLinearNatural

/-!
# Faithful scalar actions on commuting homogeneous orbits

The orbit of a simple support constituent under a commuting group is a sum
of copies of that same support module. Finite isotypic coordinates intertwine
the entire support action. A scalar commutant then gives a genuine faithful
matrix action on the multiplicity space: its action on pure tensors detects
the original actor. The Suzuki support application uses the natural SL₃
scalar field and keeps the starred actor in the support throughout.

Source: Aschbacher--Smith A.1.41--42 and D.3.9, printed pp.31--32,200--201.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra
open Representation Representation.BinaryOffender.Homogeneous
namespace Representation.BinaryOffender.Homogeneous.CommutingMultiplicity
variable {D C V : Type*} [Group D] [Group C]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Finite coordinates intertwining the complete homogeneous support action. -/
theorem homogeneous_coordinates (σ : Representation (ZMod 2) D V)
    (I : Subrepresentation σ) (hi : IsIrreducible I.toRepresentation)
    (hh : homogeneousPart I ⊤ = ⊤) :
    ∃ n : ℕ, ∃ e : V ≃ₗ[ZMod 2] (Fin n → I.toRepresentation.asModule),
      ∀ d v, e (σ d v) = fun i => I.toRepresentation.asModuleEquiv.symm
        (I.toRepresentation d (I.toRepresentation.asModuleEquiv (e v i))) := by
  let := simple_asSubmodule I hi
  have htop : isotypicComponent (ZMod 2)[D] σ.asModule I.asSubmodule = ⊤ := by
    have hle : homogeneousPart I ⊤ ≤
        (isotypicComponent (ZMod 2)[D] σ.asModule I.asSubmodule).restrictScalars (ZMod 2) := by
      apply iSup_le
      intro J
      apply iSup_le
      intro h v hv
      exact (show J.asSubmodule ≤ isotypicComponent (ZMod 2)[D] σ.asModule I.asSubmodule from
        le_sSup ((sameModule_iff_linearEquiv J I).mp h.2.symm)) hv
    rw [hh] at hle
    exact top_unique hle
  let : Module.Finite (ZMod 2) σ.asModule := σ.asModuleEquiv.symm.finiteDimensional
  let : Module.Finite (ZMod 2)[D] σ.asModule := Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  let C₀ := isotypicComponent (ZMod 2)[D] σ.asModule I.asSubmodule
  let : IsSemisimpleModule (ZMod 2)[D] σ.asModule :=
    IsSemisimpleModule.congr ((LinearEquiv.ofEq C₀ ⊤ htop).trans Submodule.topEquiv).symm
  obtain ⟨n,⟨q⟩⟩ := (IsIsotypicOfType.of_isotypicComponent_eq_top htop).linearEquiv_fun
  let e : V ≃ₗ[ZMod 2] (Fin n → I.toRepresentation.asModule) :=
    σ.asModuleEquiv.symm.trans (q.restrictScalars (ZMod 2))
  refine ⟨n,e,?_⟩
  intro d v
  change q (σ.asModuleEquiv.symm (σ d v)) = _
  rw [σ.asModuleEquiv_symm_map_rho,q.map_smul]
  funext i
  change (MonoidAlgebra.of (ZMod 2) D d) • (q (σ.asModuleEquiv.symm v) i) = _
  apply Subtype.ext
  change σ.asModuleEquiv ((MonoidAlgebra.of (ZMod 2) D d) • (q (σ.asModuleEquiv.symm v) i).val) = _
  rw [Representation.asModuleEquiv_map_smul,Representation.asAlgebraHom_of]
  rfl


end Representation.BinaryOffender.Homogeneous.CommutingMultiplicity

namespace Representation.BinaryOffender.Homogeneous.CommutingMultiplicity
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- Coordinates on the literal commuting orbit preserve every support actor. -/
theorem commuting_orbit_coordinates
    (ρ : Representation (ZMod 2) G V) (X K : Subgroup G)
    (hc : K ≤ centralizer (X : Set G))
    (R : Submodule (ZMod 2) V) (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation) :
    ∃ n : ℕ, ∃ e : orbitSpan ρ K R ≃ₗ[ZMod 2] (Fin n → R),
      ∀ (x : X) (v : orbitSpan ρ K R),
        e ⟨ρ x v,(orbit_invariant_of_commuting ρ X K hc R hR x.property v).2 v.property⟩ =
          fun i => (invariantSubspace ρ X R hR).toRepresentation x (e v i) := by
  let O := orbitSpan ρ K R
  have hRO : R ≤ O := le_orbitSpan ρ K R
  have hXO := orbit_invariant_of_commuting ρ X K hc R hR
  let U := invariantSubspace ρ X O hXO
  let I₀ := invariantSubspace ρ X R hR
  let I := sectionLower (ρ.comp X.subtype) I₀ U
  let σ := U.toRepresentation
  let τ := (invariantSubspace ρ K O (orbitSpan_invariant ρ K R)).toRepresentation
  let e₀ : I.toRepresentation.Equiv I₀.toRepresentation :=
    .mk (sectionLowerEquiv (ρ.comp X.subtype) hRO) (by intro x; rfl)
  have hi' : IsIrreducible I.toRepresentation :=
    (RepEquiv.ofRepresentationEquiv e₀).irreducible_of_euqiv hi
  have hh : ∀ a x v, τ a (σ x v) = σ x (τ a v) := by
    intro a x v
    apply Subtype.ext
    change ρ a.val (ρ x.val v.val) = ρ x.val (ρ a.val v.val)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact congrArg (fun g => ρ g v.val) ((hc a.property x.val x.property).symm)
  have hg : orbitSpan τ ⊤ I.toSubmodule = ⊤ := by
    apply Submodule.map_injective_of_injective (f := O.subtype) Subtype.val_injective
    rw [orbitSpan_map_equivariant τ ρ K.subtype O.subtype (fun _ _ => rfl)]
    have hiO : I.toSubmodule.map O.subtype = R := by
      change (R.comap O.subtype).map O.subtype = R
      rw [Submodule.map_comap_subtype,inf_eq_right.mpr hRO]
    rw [hiO,←MonoidHom.range_eq_map,Subgroup.range_subtype,Submodule.map_top,Submodule.range_subtype]
  obtain ⟨n,e,he⟩ := homogeneous_coordinates σ I hi'
    (homogeneous_of_commuting_orbit σ τ hh I hg)
  let q := I.toRepresentation.asModuleEquiv.trans e₀.toLinearEquiv
  refine ⟨n,e.trans (LinearEquiv.piCongrRight fun _ => q),?_⟩
  intro x v
  change (fun i => q (e (σ x v) i)) = _
  rw [he]
  funext i
  exact LinearMap.congr_fun (e₀.isIntertwining' x) _
end Representation.BinaryOffender.Homogeneous.CommutingMultiplicity

namespace Representation.ScalarMultiplicity
variable {k F D C E V : Type*} [Field k] [Field F] [Group D] [Group C]
  [AddCommGroup E] [Module F E] [Module k E] [Nontrivial E]
  [AddCommGroup V] [Module k V]
/-- A faithful commuting actor induces a faithful matrix action over the scalar field. -/
theorem faithful_action_of_copy_coordinates
    (σ : Representation k D E)
    (hs : ∀ (f : E →ₗ[k] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : F, ∀ v, f v = c • v)
    (α : Representation k D V) (τ : Representation k C V) (hf : Function.Injective τ)
    (hc : ∀ a d v, τ a (α d v) = α d (τ a v))
    {n : ℕ} (e : V ≃ₗ[k] (Fin n → E))
    (he : ∀ d v, e (α d v) = fun i => σ d (e v i)) :
    ∃ f : C →* Matrix.GeneralLinearGroup (Fin n) F, Function.Injective f := by
  classical
  let ν : Representation k C (Fin n → E) := e.conjRingEquiv.toMonoidHom.comp τ
  have hν : Function.Injective ν := e.conjRingEquiv.injective.comp hf
  have hn : ∀ a d x, ν a (fun i => σ d (x i)) = fun i => σ d (ν a x i) := by
    intro a d x
    obtain ⟨v,rfl⟩ := e.surjective x
    change e (τ a (e.symm (fun i => σ d (e v i)))) = _
    rw [←he d v,e.symm_apply_apply,hc,he]
    change (fun i => σ d (e (τ a v) i)) = fun i => σ d (e (τ a (e.symm (e v))) i)
    rw [e.symm_apply_apply]
  obtain ⟨f,hf⟩ := exists_injective_unit σ hs ν hν hn
  exact ⟨Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp f,
    Matrix.GeneralLinearGroup.toLin.symm.injective.comp hf⟩
end Representation.ScalarMultiplicity
