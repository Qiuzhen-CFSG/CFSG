module
public import Theory.Representation.FirstCohomologySymplecticFour.BinaryField
public import Theory.Representation.FirstCohomologyCyclic

/-!
# Full binary symplectic cohomology for the AS91 overlap

Restriction to the actual derived subgroup is injective on cocycles: a
cocycle vanishing there has values fixed by that normal subgroup, and two
of its existing explicit generators have no common nonzero fixed vector.
The proved derived-group normal form therefore extends to all of Sp4(2),
with the same quadratic-defect cocycle and principal vector. Its
nonprincipality also follows by restriction. Thus H1 has dimension one
for the full group required in Section 8, including its outer coset.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
The native hexad and original overlap applications are in descendants.
This calculation does not assert the full automorphism classification.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
open Matrix Representation Representation.OneCohomology
open Representation.OneCohomology.SymplecticFour

abbrev Sp := Matrix.symplecticGroup (Fin 2) (ZMod 2)
abbrev V := (Fin 2 ⊕ Fin 2) → ZMod 2
abbrev natural : Representation (ZMod 2) Sp V := symplecticNatural 2
abbrev derivedNatural : Representation (ZMod 2) (commutator Sp) V := symplecticDerivedNatural 2

/-- Restriction uses the actual commutator inclusion in Sp4(2). -/
def restrict : cocycles natural →ₗ[ZMod 2] cocycles derivedNatural where
  toFun f := ⟨fun g => f.val g.val, fun g h => f.property g.val h.val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem derived_fixed_zero (v : V)
    (hv : ∀ g : commutator Sp, derivedNatural g v = v) : v = 0 := by
  have h0 := hv (BinaryField.generator 0)
  have h1 := hv (BinaryField.generator 1)
  change (BinaryField.generator 0).val.val *ᵥ v = v at h0
  change (BinaryField.generator 1).val.val *ᵥ v = v at h1
  rw [BinaryField.generator_val] at h0 h1
  have hc : ∀ v : V, BinaryField.generatorMatrix 0 *ᵥ v = v →
      BinaryField.generatorMatrix 1 *ᵥ v = v → v = 0 := by decide +kernel
  exact hc v h0 h1

/-- A cocycle vanishing on the normal derived subgroup is zero on the full group. -/
theorem zero_of_restrict_zero (f : cocycles natural) (hf : restrict f = 0) : f = 0 := by
  have hz (n : commutator Sp) : f.val n.val = 0 :=
    congrArg (fun c : cocycles derivedNatural => c.val n) hf
  apply Subtype.ext
  funext g
  apply derived_fixed_zero
  intro n
  let m : commutator Sp := ⟨g⁻¹*n.val*g,
    by simpa only [inv_inv] using
      (inferInstance : (commutator Sp).Normal).conj_mem n.val n.property g⁻¹⟩
  have he : g*m.val = n.val*g := by dsimp [m]; group
  have hc := congrArg f.val he
  rw [f.property g m.val, f.property n.val g, hz m, hz n, map_zero, zero_add, add_zero] at hc
  exact hc.symm

/-- Restriction is injective already on cocycles, not only on their classes. -/
theorem restrict_injective : Function.Injective restrict := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro f hf
  exact zero_of_restrict_zero f hf

@[simp] theorem restrict_quadratic : restrict quadraticCocycle = derivedQuadraticCocycle := rfl
@[simp] theorem restrict_principal (v : V) :
    restrict (principal natural v) = principal derivedNatural v := rfl

/-- The full symplectic cocycles have exactly the same quadratic normal form. -/
theorem full_normal_form (f : cocycles natural) :
    ∃ (t : ZMod 2) (v : V), f = t • quadraticCocycle + principal natural v := by
  obtain ⟨t,v,hv⟩ := BinaryField.exists_normal_form_zmod_two (restrict f)
  refine ⟨t,v,restrict_injective ?_⟩
  simpa only [map_add,map_smul,restrict_quadratic,restrict_principal] using hv

/-- The full quadratic cocycle is nonprincipal, as seen on its derived restriction. -/
theorem full_quadratic_not_principal :
    ¬ ∃ v, principal natural v = quadraticCocycle := by
  rintro ⟨v,hv⟩
  exact derivedQuadraticCocycle_not_principal ⟨v,congrArg restrict hv⟩

/-- The full Sp4(2), rather than only A6, has the required dimension-one H1. -/
theorem full_finrank_H1 : Module.finrank (ZMod 2) (H1 natural) = 1 :=
  finrank_H1_of_cyclicNormalForm natural quadraticCocycle
    full_quadratic_not_principal full_normal_form

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
