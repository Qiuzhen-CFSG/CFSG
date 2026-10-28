module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.Grading
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.Bruhat
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.FixedSeparation
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.NormalizerWords

/-!
# Ree parabolic overlap and positive normalizer

The two split parabolics are triangular for complementary Levi gradings, so
their intersection is triangular for total root height. Uniform split Bruhat
coverage reduces Borel membership to recognizing triangular middle matrices.

For the fixed normalizer, uniform fixed Bruhat coverage removes the positive
outer factors. Constructed fixed positive words detect every simple root.
Consequently, a normalizing middle matrix with a specified Weyl monomial
presentation has trivial Weyl action and is height triangular.

The normalizer-word decomposition supplies the Weyl monomial presentations
and identifies height-triangular normalizer words with diagonal torus elements.
Substituting these results into the reductions proves the exact split parabolic
intersection and the fixed positive-normalizer bound. Only the torus comparison
`hT : splitTorus m = diagonalTorus m` remains an explicit hypothesis; its
coroot realization belongs to the unconditional assembly.

All arguments include `m = 0`, whose carrier is the full group ²F₄(2).
Source: the subgroup amalgam of Aschbacher–Smith F.1.4–5 and the Ree case
F.1.12(I)(5), printed pp.260,263–264 of `refs/quasithin.pdf`; split and fixed
Bruhat forms in GLS3 1.11.5 and 2.3.5, `refs/KGroup/GLS3/Chapter1.tex` and
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace ReeF4.Parabolics.Overlap
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup LargeLocalSeeds
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
noncomputable section

/-- Bruhat coverage reduces triangular Borel recognition to the middle matrix. -/
theorem mem_splitBorel_of_heightTriangular (m : ℕ)
    (hT : splitTorus m = diagonalTorus m)
    (hkernel : ∀ n ∈ splitNormalizerWords m, IsHeightTriangular n → n ∈ diagonalTorus m)
    {g : SplitGroup m} (hg : IsHeightTriangular g) : g ∈ splitBorel m := by
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := exists_split_normal_form m g
  have hntri : IsHeightTriangular n := by
    have h := ((splitUnipotent_heightTriangular hu).inv.mul hg).mul
      (splitUnipotent_heightTriangular hv.1).inv
    have hn' : u⁻¹ * g * v⁻¹ = n := by rw [he]; group
    rwa [hn'] at h
  have hnT : n ∈ splitTorus m := hT.symm ▸ hkernel n hn hntri
  have huB : u ∈ splitBorel m := (le_sup_left : splitUnipotent m ≤ splitBorel m) hu
  have hvB : v ∈ splitBorel m := (le_sup_left : splitUnipotent m ≤ splitBorel m) hv.1
  have hnB : n ∈ splitBorel m := (le_sup_right : splitTorus m ≤ splitBorel m) hnT
  rw [he]
  exact (splitBorel m).mul_mem ((splitBorel m).mul_mem huB hnB) hvB

/-- The exact split overlap follows once triangular normalizer words are
identified with the diagonal torus. The coroot comparison remains explicit. -/
theorem splitParabolic_inf_eq_splitBorel_of_triangular_normalizerWords (m : ℕ)
    (hT : splitTorus m = diagonalTorus m)
    (hkernel : ∀ n ∈ splitNormalizerWords m, IsHeightTriangular n → n ∈ diagonalTorus m) :
    splitParabolic m .suzuki ⊓ splitParabolic m .linear = splitBorel m := by
  apply le_antisymm
  · intro g hg
    exact mem_splitBorel_of_heightTriangular m hT hkernel
      (inf_splitParabolic_heightTriangular m hT.le hg)
  · exact le_inf (sup_le_sup_right (splitUnipotent_le_splitSeed m .suzuki) _)
      (sup_le_sup_right (splitUnipotent_le_splitSeed m .linear) _)

/-- Fixed Bruhat factors and the proved coordinate separation reduce the
normalizer bound to Weyl presentation and the triangular torus kernel. -/
theorem unipotent_normalizer_le_borel_of_normalizerWords (m : ℕ)
    (hT : splitTorus m = diagonalTorus m)
    (hkernel : ∀ n ∈ splitNormalizerWords m, IsHeightTriangular n → n ∈ diagonalTorus m)
    (hweyl : ∀ n ∈ splitNormalizerWords m,
      ∃ w : typeF4RootPairing.weylGroup, ∃ c : F4Chevalley.Root → (CoefficientField m)ˣ,
        RootMonomial n.val.val (typeF4RootPairing.weylGroupToPerm w) c) :
    normalizer (unipotent m : Set (Model m)) ≤ borel m := by
  intro g hg
  obtain ⟨u, hu, n, hn, v, hv, rfl⟩ := exists_fixed_normal_form m g
  have hnN : n ∈ normalizer (unipotent m : Set (Model m)) := by
    have h := (normalizer (unipotent m : Set (Model m))).mul_mem
      ((normalizer (unipotent m : Set (Model m))).mul_mem
        ((normalizer (unipotent m : Set (Model m))).inv_mem ((unipotent m).le_normalizer hu)) hg)
      ((normalizer (unipotent m : Set (Model m))).inv_mem ((unipotent m).le_normalizer hv))
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  obtain ⟨w, c, hmono⟩ := hweyl (toSplitGroup m n) hn
  have hntri := normalizer_heightTriangular_of_weyl_monomial n w c hmono hnN
  have hnT : toSplitGroup m n ∈ splitTorus m := hT.symm ▸ hkernel _ hn hntri
  have hnB : n ∈ borel m := (le_sup_right : splitTorus m ≤ splitBorel m) hnT
  exact (borel m).mul_mem ((borel m).mul_mem (unipotent_le_borel m hu) hnB)
    (unipotent_le_borel m hv)

/-- The two actual split parabolics meet in the independently defined split
Borel, assuming only the coroot-word and diagonal-torus comparison. -/
theorem splitParabolic_inf_eq_splitBorel (m : ℕ)
    (hT : splitTorus m = diagonalTorus m) :
    splitParabolic m .suzuki ⊓ splitParabolic m .linear = splitBorel m :=
  splitParabolic_inf_eq_splitBorel_of_triangular_normalizerWords m hT
    (fun _ hn htri => normalizerWord_mem_diagonalTorus_of_heightTriangular hT hn htri)

/-- In the full fixed Ree group, including `m = 0`, every element normalizing
the fixed positive subgroup belongs to the root Borel. The torus comparison
is the only additional hypothesis. -/
theorem unipotent_normalizer_le_borel (m : ℕ)
    (hT : splitTorus m = diagonalTorus m) :
    normalizer (unipotent m : Set (Model m)) ≤ borel m :=
  unipotent_normalizer_le_borel_of_normalizerWords m hT
    (fun _ hn htri => normalizerWord_mem_diagonalTorus_of_heightTriangular hT hn htri)
    (fun _ hn => normalizerWords_weylMonomial hT hn)

end
end ReeF4.Parabolics.Overlap
