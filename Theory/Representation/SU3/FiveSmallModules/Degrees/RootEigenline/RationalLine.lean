module

public import Theory.Representation.PGroupScalarWitness
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Rational lines from a cyclic torus modulo scalars

A cyclic torus preserves the root-fixed space. When its eighth powers are
central, absolute irreducibility makes them scalar. Perfectness of a finite
characteristic-two field provides the scalar's eighth root. Subtracting that
root from the torus generator gives a nilpotent operator, hence an eigenvector.
The root group and torus then preserve its line, and its scalars give a genuine
unit-valued character of their join.

This is the coefficient-field descent step in the root-group route to
Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3, p.10,
used in Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline

/-- A scalar eighth power in characteristic two gives a rational eigenvector.
The original finite field is perfect; no splitting field is needed. -/
private theorem exists_eigenvector_of_eighth_power
    {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Nontrivial V]
    (f : Module.End K V) (a : K) (hf : f ^ 8 = a • 1) :
    ∃ b : K, ∃ v : V, v ≠ 0 ∧ f v = b • v := by
  let : CharP (Module.End K V) 2 :=
    charP_of_injective_ringHom (algebraMap K (Module.End K V)).injective 2
  obtain ⟨b, hb⟩ := (bijective_iterateFrobenius K 2 3).surjective a
  have hb' : b ^ 8 = a := hb
  have hnil : (f - b • 1) ^ 8 = 0 := by
    have hc : Commute f (b • (1 : Module.End K V)) := by
      simp [Commute, SemiconjBy]
    have hh := sub_pow_char_pow_of_commute 2 3 hc
    simpa only [show 2 ^ 3 = 8 by decide, smul_pow, one_pow, hf, hb', sub_self] using hh
  have he : f.HasGenEigenvalue b 8 := by
    simp only [Module.End.HasGenEigenvalue, Module.End.HasUnifEigenvalue,
      Module.End.genEigenspace_nat, hnil, LinearMap.ker_zero]
    exact top_ne_bot
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_hasGenEigenvalue he).exists_hasEigenvector
  exact ⟨b, v, hv.2, hv.apply_eq_smul⟩

/-- Scalars on a nonzero invariant line form an actual unit-valued character. -/
private theorem exists_character_of_eigenvector
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (v : V) (hv : v ≠ 0)
    (hline : ∀ g : G, ∃ a : K, ρ g v = a • v) :
    ∃ χ : G →* Kˣ, ∀ g, ρ g v = (χ g : K) • v := by
  classical
  choose a ha using hline
  have hone : a 1 = 1 := by
    apply smul_left_injective K hv
    simpa using (ha 1).symm
  have hmul (g h : G) : a (g * h) = a g * a h := by
    apply smul_left_injective K hv
    change a (g * h) • v = (a g * a h) • v
    rw [← ha, map_mul, Module.End.mul_apply, ha, map_smul, ha, smul_smul, mul_comm]
  have hne (g : G) : a g ≠ 0 := by
    intro hz
    have hh := hmul g g⁻¹
    rw [mul_inv_cancel, hone, hz, zero_mul] at hh
    exact one_ne_zero hh
  exact ⟨{ toFun := fun g => Units.mk0 (a g) (hne g)
           map_one' := Units.ext hone
           map_mul' := fun g h => Units.ext (hmul g h) }, ha⟩

/-- Root fixed vectors and a cyclic torus whose eighth powers are central
supply a line over the original finite characteristic-two field. -/
theorem eigenline_of_fixed_space
    {K G V : Type*} [Field K] [Finite K] [CharP K 2] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) [ρ.IsAbsolutelyIrreducible]
    (P T : Subgroup G) [IsCyclic T]
    (hnorm : T ≤ Subgroup.normalizer (P : Set G))
    (hcentral : ∀ t ∈ T, t ^ 8 ∈ Subgroup.center G)
    (hfixed : Representation.invariants (ρ.comp P.subtype) ≠ ⊥) :
    ∃ (χ : ↥(P ⊔ T) →* Kˣ) (v : V),
      v ≠ 0 ∧ ∀ b : ↥(P ⊔ T), ρ b v = (χ b : K) • v := by
  classical
  let W := Representation.invariants (ρ.comp P.subtype)
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hfixed
  have hinv (t : T) (v : V) (hv : v ∈ W) : ρ t v ∈ W := by
    intro p
    have hp : (t : G)⁻¹ * p * t ∈ P := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hnorm (t⁻¹).property) (p : G)).mp p.property
    have hh := hv ⟨(t : G)⁻¹ * p * t, hp⟩
    change ρ ((t : G)⁻¹ * p * t) v = v at hh
    change ρ (p : G) (ρ t v) = ρ t v
    rw [← Module.End.mul_apply, ← map_mul]
    calc
      ρ ((p : G) * t) v = ρ ((t : G) * ((t : G)⁻¹ * p * t)) v := by congr 2; group
      _ = ρ t v := by rw [map_mul, Module.End.mul_apply, hh]
  obtain ⟨t, ht⟩ := (IsCyclic.exists_zpow_surjective (G := T))
  obtain ⟨a, ha⟩ := exists_scalar_of_mem_center_of_absolutelyIrreducible ρ
    ((t : G) ^ 8) (hcentral t t.property)
  let f : Module.End K W := (ρ t).restrict (hinv t)
  have hpow (n : ℕ) (w : W) : ((f ^ n) w : V) = ρ ((t : G) ^ n) w := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, map_mul]
      change ρ t (((f ^ n) w : W) : V) = ρ t (ρ ((t : G) ^ n) w)
      rw [ih]
  have hf : f ^ 8 = a • 1 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [hpow, ha]
    rfl
  obtain ⟨c, w, hw, hcw⟩ := exists_eigenvector_of_eighth_power f a hf
  have hw' : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
  have hcw' : ρ t (w : V) = c • (w : V) := congrArg Subtype.val hcw
  have hc : c ≠ 0 := by
    intro hz
    apply hw'
    apply (Representation.apply_bijective ρ t).injective
    simp only [hcw', hz, zero_smul, map_zero]
  let L : Subgroup G :=
    { carrier := {g | ∃ a : Kˣ, ρ g (w : V) = (a : K) • (w : V)}
      one_mem' := ⟨1, by simp⟩
      mul_mem' := by
        rintro g h ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, ?_⟩
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul,
          Units.val_mul, mul_comm]
      inv_mem' := by
        rintro g ⟨a, ha⟩
        refine ⟨a⁻¹, ?_⟩
        apply (Representation.apply_bijective ρ g).injective
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply, map_smul, ha, smul_smul, Units.inv_mul, one_smul] }
  have hP : P ≤ L := fun p hp => ⟨1, by simpa using w.property ⟨p, hp⟩⟩
  have htL : (t : G) ∈ L := ⟨Units.mk0 c hc, hcw'⟩
  have hT : T ≤ L := by
    intro s hs
    obtain ⟨n, hn⟩ := ht ⟨s, hs⟩
    have hh := L.zpow_mem htL n
    simpa only [← Subgroup.coe_zpow, hn] using hh
  obtain ⟨χ, hχ⟩ := exists_character_of_eigenvector (ρ.comp (P ⊔ T).subtype)
    (w : V) hw' (fun b => by
      obtain ⟨a, ha⟩ := (sup_le hP hT) b.property
      exact ⟨(a : K), ha⟩)
  exact ⟨χ, w, hw', hχ⟩

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline
