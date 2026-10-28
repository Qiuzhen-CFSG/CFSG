module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Idempotents

/-!
# Detecting the radical by coordinate simple representations

For a finite group algebra, vanishing on all irreducible representations on
coordinate spaces detects the Jacobson radical. Indeed, every quotient by a
maximal left ideal is a finite-dimensional simple module, which can be put
in coordinates. Conversely, the radical annihilates every simple module.
Finite dimensionality makes radical elements nilpotent.

A central idempotent acts as zero or the identity on a simple module. These
facts let a complete family of block simples detect the radical inside the
literal block ideal, before applying orthogonal-idempotent lifting.

Source: Feit, *The Representation Theory of Finite Groups*, I.6 and I.8,
with the nil-ideal lifting setting of I.12.1--4 and the simple-module
correspondence of I.13.5--7. Feit uses right modules; the arguments here use
Mathlib's left modules throughout.
-/

public section
noncomputable section
open scoped MonoidAlgebra

namespace Representation.BlockFrames
variable {K G : Type*} [Field K] [Group G]

private theorem equiv_action {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) (x : K[G]) (v : V) :
    e (ρ.asAlgebraHom x v) = σ.asAlgebraHom x (e v) := by
  exact (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap).map_smul x v

private theorem exists_coordinates {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V) :
    ∃ σ : Representation K G (Fin (Module.finrank K V) → K), Nonempty (ρ.Equiv σ) := by
  let b := (Module.finBasis K V).equivFun
  let σ : Representation K G (Fin (Module.finrank K V) → K) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  refine ⟨σ, ⟨{ b with isIntertwining' := ?_ }⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  change b (ρ g v) = b (ρ g (b.symm (b v)))
  rw [b.symm_apply_apply]

private theorem irreducible_equiv {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] {ρ : Representation K G V} {σ : Representation K G W}
    (e : ρ.Equiv σ) (hρ : IsIrreducible ρ) : IsIrreducible σ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  have hf : Function.Bijective f := e.bijective
  exact (irreducible_iff_isSimpleModule_asModule σ).mpr
    ((LinearMap.isSimpleModule_iff_of_bijective f hf).mp
      ((irreducible_iff_isSimpleModule_asModule ρ).mp hρ))

/-- A central idempotent acts as zero or the identity on a simple representation. -/
theorem central_idempotent_action {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) [IsIrreducible ρ] {b : K[G]}
    (hb : b ∈ Set.center K[G]) (hi : IsIdempotentElem b) :
    ρ.asAlgebraHom b = 0 ∨ ρ.asAlgebraHom b = 1 := by
  let T := IntertwiningMap.centralAlgebraMul ρ hb
  rcases IsIrreducible.injective_or_eq_zero T with hinj | hz
  · right
    apply LinearMap.ext
    intro v
    apply hinj
    change (ρ.asAlgebraHom b * ρ.asAlgebraHom b) v = ρ.asAlgebraHom b v
    rw [← map_mul, hi.eq]
  · left
    exact congrArg IntertwiningMap.toLinearMap hz

set_option backward.isDefEq.respectTransparency false in
/-- Coordinate simple representations detect the Jacobson radical. -/
theorem mem_jacobson_of_simple_actions_zero [Finite G] (x : K[G])
    (hx : ∀ (k : ℕ) (ρ : Representation K G (Fin k → K)),
      IsIrreducible ρ → ρ.asAlgebraHom x = 0) :
    x ∈ Ring.jacobson K[G] := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  apply Ideal.mem_sInf.mpr
  intro I hI
  let : I.IsMaximal := hI
  let : IsSimpleModule K[G] (K[G] ⧸ I) :=
    isSimpleModule_iff_isCoatom.mpr hI.1
  let f : RestrictScalars K K[G] (K[G] ⧸ I) →ₗ[K] (K[G] ⧸ I) :=
    { (RestrictScalars.addEquiv K K[G] (K[G] ⧸ I)).toAddHom with
      map_smul' c v := by
        change (RestrictScalars.addEquiv K K[G] (K[G] ⧸ I)) (c • v) =
          c • (RestrictScalars.addEquiv K K[G] (K[G] ⧸ I)) v
        rw [RestrictScalars.addEquiv_map_smul, algebraMap_smul] }
  have : FiniteDimensional K (RestrictScalars K K[G] (K[G] ⧸ I)) :=
    FiniteDimensional.of_injective f (RestrictScalars.addEquiv K K[G] (K[G] ⧸ I)).injective
  let ρ := Representation.ofModule (k := K) (G := G) (K[G] ⧸ I)
  have hρ : IsIrreducible ρ := (isSimpleModule_iff_irreducible_ofModule (K[G] ⧸ I)).mp inferInstance
  obtain ⟨σ, ⟨e⟩⟩ := exists_coordinates ρ
  have hσ := hx _ σ (irreducible_equiv e hρ)
  have hr : ρ.asAlgebraHom x = 0 := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (ρ.asAlgebraHom x v) = e (0 : _)
    rw [equiv_action, hσ, LinearMap.zero_apply, map_zero]
  have h := LinearMap.congr_fun hr
    ((RestrictScalars.addEquiv K K[G] (K[G] ⧸ I)).symm (I.mkQ 1))
  rw [ofModule_asAlgebraHom_apply_apply, LinearMap.zero_apply] at h
  have h' : x • I.mkQ 1 = 0 := by
    exact (RestrictScalars.addEquiv K K[G] (K[G] ⧸ I)).symm.injective (by simpa using h)
  have h'' : I.mkQ x = 0 := by
    simpa only [← map_smul, smul_eq_mul, mul_one] using h'
  exact (Submodule.Quotient.mk_eq_zero I).mp h''

/-- The radical acts trivially on every simple representation. -/
theorem simple_action_zero_of_mem_jacobson {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) [IsIrreducible ρ] {x : K[G]}
    (hx : x ∈ Ring.jacobson K[G]) : ρ.asAlgebraHom x = 0 := by
  apply LinearMap.ext
  intro v
  have h := Module.le_comap_jacobson
    (LinearMap.toSpanSingleton K[G] ρ.asModule (ρ.asModuleEquiv.symm v)) hx
  change x • (ρ.asModuleEquiv.symm v) ∈ Module.jacobson K[G] ρ.asModule at h
  rw [IsSemisimpleModule.jacobson_eq_bot] at h
  have hz : x • (ρ.asModuleEquiv.symm v) = 0 := h
  simpa using congrArg ρ.asModuleEquiv hz

/-- Finite dimensionality makes every radical element nilpotent. -/
theorem nilpotent_of_mem_jacobson [Finite G] {x : K[G]}
    (hx : x ∈ Ring.jacobson K[G]) : IsNilpotent x := by
  let : IsArtinianRing K[G] := IsArtinianRing.of_finite K K[G]
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := K[G])
  rw [← Ideal.jacobson_bot] at hx
  have hn' : (Ideal.jacobson (⊥ : Ideal K[G])) ^ n = ⊥ := hn
  exact ⟨n, Ideal.mem_bot.mp (hn' ▸ Ideal.pow_mem_pow hx n)⟩

end Representation.BlockFrames
