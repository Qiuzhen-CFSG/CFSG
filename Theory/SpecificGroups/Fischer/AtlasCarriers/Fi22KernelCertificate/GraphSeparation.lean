module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GeneratorMaps
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphSeparation.Certificate

/-!
# Fi22 fixed-point signatures separate involution orbits

The 27 selected points are fixed by the packed map `fastA`. For every point,
its Boolean related-values on this list recover the unordered pair consisting
of the point and its `fastA` image. Consequently, equal related-values imply
that two points are equal or are exchanged by `fastA`.

The final theorem transports this finite certificate to the exact ATLAS
generator, taking the map comparison as an explicit hypothesis. It supplies
the separation premise of the fixed-point kernel argument for GLS3 Table 5.3t
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). The generator comparison and relation
invariance are independent obligations of the final kernel assembly.

Source data: ATLAS F22G1-p3510B0, retained in `AtlasCarriers/source/` and
`Fi22KernelCertificate/source/`. The recovery certificates are reproducible
using `GraphSeparation/source/generate.py` and checked by Lean's kernel.
-/

public section
namespace Sporadic.Fischer.Fi22.KernelCertificate

/-- All selected tests are fixed points of the packed map. -/
theorem separatingPoints_fixed_fastA : ∀ f ∈ separatingPoints, fastA f = f := by
  have h : separatingPoints.all (fun f => fastA f == f) = true := by decide +kernel
  simpa only [List.all_eq_true, beq_iff_eq] using h

private theorem signature_congr (x y : Fin 3510)
    (h : ∀ f ∈ separatingPoints, related x f = related y f) :
    GraphSeparation.signature x = GraphSeparation.signature y := by
  have aux (l : List (Fin 3510))
      (hl : ∀ f ∈ l, related x f = related y f) :
      l.foldr (fun f n => (related x f).toNat + 2 * n) 0 =
      l.foldr (fun f n => (related y f).toNat + 2 * n) 0 := by
    induction l with
    | nil => rfl
    | cons f l ih =>
      simp only [List.foldr_cons]
      rw [hl f (by simp), ih (fun a ha => hl a (by simp [ha]))]
  exact aux separatingPoints h

/-- The 27 specified tests separate points up to the packed map `fastA`. -/
theorem related_separates_fastA (x y : Fin 3510)
    (h : ∀ f ∈ separatingPoints, related x f = related y f) :
    y = x ∨ y = fastA x := by
  have hs := signature_congr x y h
  have hx := GraphSeparation.recoveryCorrect x
  have hy := GraphSeparation.recoveryCorrect y
  unfold GraphSeparation.RecoveryCorrect at hx hy
  rw [← hs] at hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (Fin.ext (congrArg Prod.fst (hy.symm.trans hx)))
  · exact Or.inr (Fin.ext (congrArg Prod.snd (hy.symm.trans hx)))
  · exact Or.inr (Fin.ext (congrArg Prod.fst (hy.symm.trans hx)))
  · exact Or.inl (Fin.ext (congrArg Prod.snd (hy.symm.trans hx)))

/-- Separation for the actual fixed-point action, conditional only on the
independently certified comparison of the packed map with the ATLAS generator. -/
theorem related_separates_of_fastA (hA : ∀ x, generatorA x = fastA x) :
    ∀ x y : Fin 3510,
      (∀ f : FixedPointsA, related x f.val = related y f.val) →
      y = x ∨ y = generatorA x := by
  intro x y h
  rw [hA]
  apply related_separates_fastA x y
  intro f hm
  have hfix : generatorA f = f := (hA f).trans (separatingPoints_fixed_fastA f hm)
  exact h ⟨f, hfix⟩

end Sporadic.Fischer.Fi22.KernelCertificate
