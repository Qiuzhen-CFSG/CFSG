module

public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRoots
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Elimination
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Symbolic

/-!
# The scalar commutant of the genuine triality fixed roots

In characteristic two, a matrix commuting with the signed central root curves
and signed folded three-arm curves is scalar. Four curves at parameter 1 leave
five possible entries in the commutant. A folded curve at a parameter with
three distinct Frobenius conjugates removes the four extra freedoms.

The calculation uses the actual Geck matrices on the full 28-dimensional
lattice. It applies to every parameter of characteristic two, including q = 2;
it uses neither simplicity, Bruhat decomposition, nor centerlessness. This is
the scalar input for the elementary central-kernel argument, whose separate
scalar-rigidity input belongs to the parent assembly.

Source: GLS3 Theorem 2.2.6, the root parametrizations in §2.4, and the kernel
paragraph in the proof of 2.3.4–5 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.ElementaryCentralKernel
open Parabolics Parabolics.RankOneMatrices
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

namespace FixedRootCommutant

/-- Five explicit matrix commutation conditions already force scalarness. -/
theorem scalar_of_constant_and_folded {F : Type*} [Field F] [CharP F 2]
    (A : Matrix (Fin 28) (Fin 28) F) (a b c : F)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hconstant : ∀ k, Commute A (constantMatrix k))
    (hfolded : Commute A
      (rootMatrix 0 true a * rootMatrix 2 true b * rootMatrix 3 true c)) :
    A = A 0 0 • (1 : Matrix (Fin 28) (Fin 28) F) := by
  have hn := eq_normalForm A hconstant
  exact hn.trans (normalForm_scalar_of_folded A a b c hab hac hbc (hn ▸ hfolded))

/-- The actual split-group matrices in the numerical Geck coordinates. -/
def coordinateHom (P : Parameters) :
    SplitGroup P →* Matrix (Fin 28) (Fin 28) (ExtensionField P) where
  toFun g := g.val.val.submatrix coordinates coordinates
  map_one' := Matrix.submatrix_one_equiv coordinates
  map_mul' g h := (Matrix.submatrix_mul_equiv g.val.val h.val.val
    coordinates coordinates coordinates).symm

private lemma coordinateHom_simpleRoot (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (i : Fin 4) (t : ExtensionField P) :
    coordinateHom P (simpleRoot P s i t) = rootMatrix i s t := by
  let : CharP (ExtensionField P) 2 := by rw [← hp]; infer_instance
  cases s
  · exact negativeMatrix_coordinates i t
  · exact positiveMatrix_coordinates i t

private lemma coordinateHom_foldedRoot (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (t : ExtensionField P) :
    coordinateHom P (foldedRoot P s t) =
      rootMatrix 0 s t * rootMatrix 2 s (fieldFrobenius P t) *
        rootMatrix 3 s (fieldFrobenius P (fieldFrobenius P t)) := by
  simp only [foldedRoot, map_mul, coordinateHom_simpleRoot P hp]

private lemma commute_coordinates (P : Parameters) (g : SplitGroup P)
    (hg : g ∈ Subgroup.centralizer (fixedRootGenerators P))
    (x : SplitGroup P) (hx : x ∈ fixedRootGenerators P) :
    Commute (coordinateHom P g) (coordinateHom P x) :=
  (show Commute g x from (Subgroup.mem_centralizer_iff.mp hg x hx).symm).map
    (coordinateHom P)

end FixedRootCommutant

/-- Every split-group element centralizing the genuine fixed root generators
has scalar Geck matrix, for all characteristic-two parameters including q = 2. -/
theorem fixedRootCentralizer_is_scalar (P : Parameters) (hp : P.prime = 2)
    (g : SplitGroup P) (hg : g ∈ Subgroup.centralizer (fixedRootGenerators P)) :
    ∃ c : ExtensionField P, g.val.val = c • 1 := by
  let : CharP (ExtensionField P) 2 := by rw [← hp]; infer_instance
  let A := FixedRootCommutant.coordinateHom P g
  have hcentral (s : Bool) :
      Commute A (FixedRootCommutant.constantMatrix (if s then 0 else 1)) := by
    have h := FixedRootCommutant.commute_coordinates P g hg (simpleRoot P s 1 1)
      (Or.inl ⟨s, 1, map_one _, rfl⟩)
    simpa only [FixedRootCommutant.coordinateHom_simpleRoot P hp,
      FixedRootCommutant.central_constant] using h
  have hfolded (s : Bool) (t : ExtensionField P) : Commute A
      (FixedRootCommutant.rootMatrix 0 s t *
        FixedRootCommutant.rootMatrix 2 s (fieldFrobenius P t) *
        FixedRootCommutant.rootMatrix 3 s (fieldFrobenius P (fieldFrobenius P t))) := by
    have h := FixedRootCommutant.commute_coordinates P g hg (foldedRoot P s t)
      (Or.inr ⟨s, t, rfl⟩)
    simpa only [FixedRootCommutant.coordinateHom_foldedRoot P hp] using h
  have hfolded_one (s : Bool) :
      Commute A (FixedRootCommutant.constantMatrix (if s then 2 else 3)) := by
    simpa only [map_one, FixedRootCommutant.folded_constant] using hfolded s 1
  have hconstant : ∀ k, Commute A (FixedRootCommutant.constantMatrix k) := by
    intro k
    fin_cases k
    · exact hcentral true
    · exact hcentral false
    · exact hfolded_one true
    · exact hfolded_one false
  obtain ⟨t, ht⟩ := exists_frobenius_moved P
  obtain ⟨h₁, h₂, h₃⟩ := frobenius_orbit_pairwise P t ht
  have hscalar := FixedRootCommutant.scalar_of_constant_and_folded A t
    (fieldFrobenius P t) (fieldFrobenius P (fieldFrobenius P t))
    h₁ h₂ h₃ hconstant (hfolded true t)
  refine ⟨A 0 0, ?_⟩
  ext r c
  obtain ⟨r, rfl⟩ := FixedRootCommutant.coordinates.surjective r
  obtain ⟨c, rfl⟩ := FixedRootCommutant.coordinates.surjective c
  have he := congrArg (fun M : Matrix (Fin 28) (Fin 28) (ExtensionField P) => M r c) hscalar
  simpa only [A, FixedRootCommutant.coordinateHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
    FixedRootCommutant.coordinates.injective.eq_iff] using he

end
end Triality.Standard.ElementaryCentralKernel
