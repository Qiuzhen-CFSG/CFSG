module

public import Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Regular orbits for finite p-groups in characteristic p

The orbit map sends a coefficient function to the corresponding linear
combination of translates. A nonzero kernel has a nonzero fixed vector,
whose regular coefficients are constant. Thus a nonzero orbit sum makes
this map injective. Equality of dimensions gives a regular orbit basis
and identifies the fixed line with the orbit sum.

This elementary modular representation argument is used for the Steinberg
module in GLS3, §2.8; the fixed-vector input is proved in
`Theory.Representation.TwoDimensionalOddOrder`.
-/

@[expose] public section
open scoped BigOperators
namespace Representation
namespace PGroupRegularOrbit
variable {E P V : Type*} [Field E] [Group P] [Fintype P]
  [AddCommGroup V] [Module E V]

def regular : Representation E P (P → E) where
  toFun g :=
    { toFun := fun f h => f (g⁻¹*h)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext f h; simp
  map_mul' g h := by ext f k; simp [mul_assoc]

def orbitMap (ρ : Representation E P V) (v : V) : (P → E) →ₗ[E] V where
  toFun f := ∑ g, f g • ρ g v
  map_add' f h := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [mul_smul, Finset.smul_sum]

lemma orbitMap_equivariant (ρ : Representation E P V) (v : V) (g : P) (f : P → E) :
    orbitMap ρ v (regular g f) = ρ g (orbitMap ρ v f) := by
  change (∑ h, f (g⁻¹*h) • ρ h v) = ρ g (∑ h, f h • ρ h v)
  rw [map_sum]
  simp_rw [map_smul, ← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ (fun h => by simp)

omit [Fintype P] in
lemma regular_fixed_iff (f : P → E) :
    (∀ g : P, regular (E := E) g f = f) ↔ ∀ g, f g = f 1 := by
  constructor
  · intro hf g
    have h := congrFun (hf g) g
    simpa [regular] using h.symm
  · intro hf g
    funext h
    exact (hf _).trans (hf _).symm

lemma orbitMap_injective (hc : ringChar E ≠ 0) (hp : IsPGroup (ringChar E) P)
    (ρ : Representation E P V) (v : V) (hv : (∑ g : P, ρ g v) ≠ 0) :
    Function.Injective (orbitMap ρ v) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  by_contra hk
  let K : Subrepresentation (regular (E := E) (P := P)) :=
    { toSubmodule := (orbitMap ρ v).ker
      apply_mem_toSubmodule := by
        intro g f hf
        change orbitMap ρ v (regular g f) = 0
        rw [orbitMap_equivariant]
        change orbitMap ρ v f = 0 at hf
        rw [hf, map_zero] }
  have : Nontrivial K.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hk
  obtain ⟨f, hf, hfix⟩ := pGroup_fix_nonzero_vector hc hp K.toRepresentation
  have hconst : ∀ g, f.val g = f.val 1 := by
    apply (regular_fixed_iff f.val).mp
    intro g
    exact congrArg Subtype.val (hfix g)
  have hone : f.val 1 ≠ 0 := by
    intro hz
    apply hf
    apply Subtype.ext
    funext g
    exact (hconst g).trans hz
  have hzero := f.property
  change (∑ g, f.val g • ρ g v) = 0 at hzero
  simp_rw [hconst] at hzero
  rw [← Finset.smul_sum] at hzero
  exact (smul_ne_zero hone hv) hzero

noncomputable def orbitEquiv [FiniteDimensional E V]
    (hc : ringChar E ≠ 0) (hp : IsPGroup (ringChar E) P)
    (ρ : Representation E P V) (v : V) (hv : (∑ g : P, ρ g v) ≠ 0)
    (hdim : Module.finrank E V = Fintype.card P) : (P → E) ≃ₗ[E] V :=
  (orbitMap ρ v).linearEquivOfInjective (orbitMap_injective hc hp ρ v hv)
    (by simpa using hdim.symm)

lemma fixed_iff [FiniteDimensional E V]
    (hc : ringChar E ≠ 0) (hp : IsPGroup (ringChar E) P)
    (ρ : Representation E P V) (v : V) (hv : (∑ g : P, ρ g v) ≠ 0)
    (hdim : Module.finrank E V = Fintype.card P) (w : V) :
    (∀ g : P, ρ g w = w) ↔ ∃ c : E, w = c • ∑ g : P, ρ g v := by
  let e := orbitEquiv hc hp ρ v hv hdim
  constructor
  · intro hw
    obtain ⟨f, rfl⟩ := e.surjective w
    have hf : ∀ g : P, regular (E := E) g f = f := by
      intro g
      apply e.injective
      change orbitMap ρ v (regular g f) = orbitMap ρ v f
      rw [orbitMap_equivariant]
      exact hw g
    have hh := (regular_fixed_iff f).mp hf
    refine ⟨f 1, ?_⟩
    change (∑ g, f g • ρ g v) = _
    simp_rw [hh]
    exact Finset.smul_sum.symm
  · rintro ⟨c, rfl⟩ g
    rw [map_smul]
    congr 1
    simpa only [Representation.norm, LinearMap.sum_apply] using ρ.self_norm_apply g v
/-- The equivalence is the concrete orbit-sum map. -/
lemma orbitEquiv_apply [FiniteDimensional E V]
    (hc : ringChar E ≠ 0) (hp : IsPGroup (ringChar E) P)
    (ρ : Representation E P V) (v : V) (hv : (∑ g : P, ρ g v) ≠ 0)
    (hdim : Module.finrank E V = Fintype.card P) (f : P → E) :
    orbitEquiv hc hp ρ v hv hdim f = ∑ g, f g • ρ g v := rfl

/-- Delta functions map to the specified orbit, so this is an actual orbit basis. -/
noncomputable def orbitBasis [FiniteDimensional E V]
    (hc : ringChar E ≠ 0) (hp : IsPGroup (ringChar E) P)
    (ρ : Representation E P V) (v : V) (hv : (∑ g : P, ρ g v) ≠ 0)
    (hdim : Module.finrank E V = Fintype.card P) : Module.Basis P E V :=
  (Pi.basisFun E P).map (orbitEquiv hc hp ρ v hv hdim)

lemma orbitBasis_apply [FiniteDimensional E V]
    (hc : ringChar E ≠ 0) (hp : IsPGroup (ringChar E) P)
    (ρ : Representation E P V) (v : V) (hv : (∑ g : P, ρ g v) ≠ 0)
    (hdim : Module.finrank E V = Fintype.card P) (g : P) :
    orbitBasis hc hp ρ v hv hdim g = ρ g v := by
  classical
  simp [orbitBasis, orbitEquiv_apply, Pi.basisFun_apply, Pi.single_apply]

end PGroupRegularOrbit
end Representation
