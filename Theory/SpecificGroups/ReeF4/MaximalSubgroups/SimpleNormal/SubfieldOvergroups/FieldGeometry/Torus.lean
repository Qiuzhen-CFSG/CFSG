module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldGeometry.Coefficients
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic

/-!
# Descent of the actual diagonal F₄ torus

The inverse Cartan matrix solves the four simple-root character equations.
Over the finite coefficient field this implies that the characters, and hence
the diagonal matrix, determine all four torus parameters. Frobenius-fixed
matrix entries therefore give Frobenius-fixed parameters. Lifting those
parameters to the embedded coefficient field and using the proved coroot-word
realization gives a preimage in the smaller root-generated split group.

Source: the split torus and Chevalley normal form in GLS3 1.11.5 and 1.12.1,
`refs/KGroup/GLS3/Chapter1.tex`, used in Malle's subfield construction.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4 ReeF4.Subfield ReeF4.Parabolics
open ReeF4.LocalBlockInput.PairRigidity.BlockParameters

namespace ReeF4.Subfield
noncomputable section

theorem torus_parameters_injective (m : ℕ) :
    Function.Injective (fun u : TorusParameter m =>
      fun i : Fin 4 => rootScale u (typeF4SimpleRootIndex i)) := by
  let F : TorusParameter m → TorusParameter m := fun u q =>
    rootScale u (typeF4SimpleRootIndex (typeF4RootPairing_baseEquiv.symm q))
  have hsurj : Function.Surjective F := by
    intro c
    refine ⟨torusParametersOfSimpleScales (fun i => c (typeF4RootPairing_baseEquiv i)), ?_⟩
    funext q
    dsimp [F]
    rw [rootScale_torusParametersOfSimpleScales, Equiv.apply_symm_apply]
  intro u v huv
  apply (Finite.injective_iff_surjective.mpr hsurj)
  funext q
  exact congrFun huv (typeF4RootPairing_baseEquiv.symm q)

theorem diagonalTorusHom_root_entry (m : ℕ) (u : TorusParameter m)
    (r : F4Chevalley.Root) :
    (diagonalTorusHom m u).val (.inr r) (.inr r) =
      ((rootScale u r)⁻¹ : (CoefficientField m)ˣ) := by
  change (Matrix.diagonal fun a =>
    (chevalleyBasisTorusUnit (P := typeF4RootPairing) u a : CoefficientField m)) _ _ = _
  simp [chevalleyBasisTorusUnit, chevalleyBasisWeight, rootScale,
    integralChevalleyRootScale]

theorem diagonalTorusHom_injective (m : ℕ) : Function.Injective (diagonalTorusHom m) := by
  intro u v huv
  apply torus_parameters_injective m
  funext i
  apply inv_injective
  apply Units.ext
  simpa only [diagonalTorusHom_root_entry] using
    congrArg (fun z : MatrixUnits m => z.val
      (.inr (typeF4SimpleRootIndex i)) (.inr (typeF4SimpleRootIndex i))) huv

theorem unitsMap_diagonalTorusHom {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (u : TorusParameter k) :
    unitsMap f (diagonalTorusHom k u) =
      diagonalTorusHom m (fun q => Units.map f.toMonoidHom (u q)) := by
  apply Units.ext
  ext i j
  change f ((Matrix.diagonal fun a =>
    (chevalleyBasisTorusUnit (P := typeF4RootPairing) u a : CoefficientField k)) i j) =
    (Matrix.diagonal fun a =>
      (chevalleyBasisTorusUnit (P := typeF4RootPairing)
        (fun q => Units.map f.toMonoidHom (u q)) a : CoefficientField m)) i j
  simp [Matrix.diagonal_apply, apply_ite f, chevalleyBasisTorusUnit]

theorem unit_mem_range_of_val {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) (u : (CoefficientField m)ˣ)
    (hu : u.val ∈ Set.range f) : u ∈ Set.range (Units.map f.toMonoidHom) := by
  obtain ⟨a, ha⟩ := hu
  have ha0 : a ≠ 0 := by
    intro h
    have hz : u.val = 0 := by rw [← ha, h, map_zero]
    exact u.ne_zero hz
  exact ⟨Units.mk0 a ha0, Units.ext ha⟩

theorem torus_mem_range_of_entries {k m : ℕ}
    (f : CoefficientField k →+* CoefficientField m) {x : SplitGroup m}
    (ht : x ∈ splitTorus m) (hx : ∀ i j, x.val.val i j ∈ Set.range f) :
    x ∈ (splitMap f).range := by
  classical
  rw [splitTorus_eq_diagonalTorus] at ht
  obtain ⟨u, hu⟩ := ht
  change diagonalTorusHom m u = x.val at hu
  let F := iterateFrobenius (CoefficientField m) 2 (2*k+1)
  have hfix : unitsMap F (diagonalTorusHom m u) = diagonalTorusHom m u := by
    rw [hu]
    apply Units.ext
    ext i j
    exact (coefficient_mem_range_iff f _).mp (hx i j)
  rw [unitsMap_diagonalTorusHom] at hfix
  have hup := diagonalTorusHom_injective m hfix
  have hurange (q : typeF4RootPairing_base.support) : u q ∈ Set.range (Units.map f.toMonoidHom) := by
    apply unit_mem_range_of_val
    apply (coefficient_mem_range_iff f _).mpr
    exact congrArg Units.val (congrFun hup q)
  choose v hv using hurange
  obtain ⟨y, _, hy⟩ := diagonalTorusHom_mem_splitTorus_map k v
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change unitsMap f y.val = x.val
  rw [show y.val = diagonalTorusHom k v from hy, unitsMap_diagonalTorusHom]
  exact (congrArg (diagonalTorusHom m) (funext hv)).trans hu

end
end ReeF4.Subfield
