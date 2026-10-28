module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData

/-!
# Comparing the two full Ree parabolic conventions

The converse uses the torus word `n_r(t)n_r(1)⁻¹`; the amalgam uses
`n_r(t)n_r(-1)`. Inversion of the actual root matrices identifies these
words. Consequently both constructions give exactly the same split torus,
full fixed parabolics and positive subgroup. This permits reuse of the
existing root geometry without replacing a full parabolic by its seed.

Source: the standard Chevalley Weyl and torus words, GLS3 §§2.3, 2.6,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem root_inv (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r (-t) :=
  Subtype.ext (F4Chevalley.rootCurve_inv r t)

/-- The two torus words are equal as elements of the concrete split matrix group. -/
theorem torusWord_eq_rootTorusWord (m : ℕ) (r : F4Chevalley.Root)
    (t : (CoefficientField m)ˣ) :
    ConverseParabolics.torusWord m r t = Parabolics.torusWord m r t := by
  simp only [ConverseParabolics.torusWord, ConverseParabolics.weylWord,
    Parabolics.torusWord, Parabolics.weylWord, Units.val_one, mul_inv_rev,
    root_inv, inv_one, inv_neg, neg_neg]
  group

/-- The full split torus is independent of the Weyl-word inverse convention. -/
theorem splitTorus_eq_rootSplitTorus (m : ℕ) :
    ConverseParabolics.splitTorus m = Parabolics.splitTorus m := by
  simp only [ConverseParabolics.splitTorus, Parabolics.splitTorus, torusWord_eq_rootTorusWord]

/-- Equality of the full fixed parabolics, including all torus generators. -/
theorem parabolic_eq_rootParabolic (m : ℕ) (s : LargeLocalSeeds.Side) :
    ConverseParabolics.parabolic m s = Parabolics.parabolic m s := by
  ext x
  change x.val ∈ ConverseParabolics.splitTorus m ⊔ LargeLocalSeeds.splitSeed m s ↔
    toSplitGroup m x ∈ LargeLocalSeeds.splitSeed m s ⊔ Parabolics.splitTorus m
  rw [toSplitGroup_apply, splitTorus_eq_rootSplitTorus, sup_comm]

/-- The two positive subgroups are the same fixed intersection. -/
theorem unipotent_eq_rootUnipotent (m : ℕ) :
    ConverseParabolics.unipotent m = Parabolics.unipotent m := by
  ext x
  change x.val ∈ LargeLocalSeeds.splitUnipotent m ↔
    toSplitGroup m x ∈ LargeLocalSeeds.splitUnipotent m
  rw [toSplitGroup_apply]

end ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
