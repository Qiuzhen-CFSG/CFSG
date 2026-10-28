module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair

/-!
# Root transport and the split opposition cell

`RootTransport n` records the action of an actual matrix-group element on
every root curve, by a root permutation and nonzero parameter scalars. It
contains no coverage or disjointness assertion. The Bruhat construction must
supply such transport data for its normalizer representatives.

If the positive subgroup and its conjugate by `n` are disjoint, no positive
root can remain positive: the corresponding conjugate root curve would give
a nonidentity intersection element. Root-curve injectivity is inherited from
the integral representation. A finite-set argument then shows that the
positive roots map onto all negative roots, so the positive subgroup maps to
the actual negative root closure.

This is the root-intersection step of GLS3 2.3.8(b,c), using the concrete split
F₄ matrices. Source: `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Subgroup
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell

/-- Exact conjugation on the concrete split root curves. -/
structure RootTransport {m : ℕ} (n : SplitGroup m) where
  perm : Equiv.Perm F4Chevalley.Root
  scale : F4Chevalley.Root → (CoefficientField m)ˣ
  conj_root : ∀ r t, (MulAut.conj n) (rootGeneratorInGroup m r t) =
    rootGeneratorInGroup m (perm r) ((scale r : CoefficientField m) * t)

private theorem rootGenerator_injective (m : ℕ) (r : F4Chevalley.Root) :
    Function.Injective (rootGeneratorInGroup m r) := by
  intro s t h
  apply rootElement_injective (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (k := CoefficientField m) r
  simp only [rootElement, rootMorphismFamily, rootMorphism_apply]
  congr 1
  change Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r s) =
    Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r t)
  exact congrArg Matrix.GeneralLinearGroup.toLin (congrArg Subtype.val h)

private theorem rootGenerator_one_ne_one (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 1 ≠ 1 := by
  intro h
  have hz : rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)
  exact one_ne_zero (rootGenerator_injective m r (h.trans hz.symm))

private theorem transported_root_mem {m : ℕ} {n : SplitGroup m}
    (a : RootTransport n) (r : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (t : CoefficientField m) :
    rootGeneratorInGroup m (a.perm r) t ∈
      (LargeLocalSeeds.splitUnipotent m).map (MulAut.conj n).toMonoidHom := by
  refine ⟨rootGeneratorInGroup m r ((a.scale r)⁻¹ * t), subset_closure ⟨r, _, hr, rfl⟩, ?_⟩
  change (MulAut.conj n) _ = _
  rw [a.conj_root]
  simp

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem perm_positive_eq_negative (p : Equiv.Perm F4Chevalley.Root)
    (hp : ∀ r, typeF4RootPairing_base.IsPos r → ¬ typeF4RootPairing_base.IsPos (p r))
    (r : F4Chevalley.Root) (hr : ¬ typeF4RootPairing_base.IsPos r) :
    ∃ s, typeF4RootPairing_base.IsPos s ∧ p s = r := by
  let f : {s : F4Chevalley.Root // typeF4RootPairing_base.IsPos s} →
      {s : F4Chevalley.Root // typeF4RootPairing_base.IsPos s} := fun s =>
    ⟨-(p s), (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base _).mpr (hp s s.property)⟩
  have hf : Function.Injective f := by
    intro s t h
    exact Subtype.ext (p.injective (neg_injective (congrArg Subtype.val h)))
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hf
    ⟨-r, (RootPairing.Base.IsPos.neg_iff_not typeF4RootPairing_base r).mpr hr⟩
  exact ⟨s, s.property, neg_injective (congrArg Subtype.val hs)⟩

/-- A disjoint root-permuting representative sends the entire positive
subgroup to the negative subgroup. -/
theorem RootTransport.map_positive_eq_negative_of_disjoint {m : ℕ} {n : SplitGroup m}
    (a : RootTransport n)
    (hd : Disjoint (LargeLocalSeeds.splitUnipotent m)
      ((LargeLocalSeeds.splitUnipotent m).map (MulAut.conj n).toMonoidHom)) :
    (LargeLocalSeeds.splitUnipotent m).map (MulAut.conj n).toMonoidHom =
      splitNegativeUnipotent m := by
  have hp : ∀ r, typeF4RootPairing_base.IsPos r →
      ¬ typeF4RootPairing_base.IsPos (a.perm r) := by
    intro r hr hpr
    apply rootGenerator_one_ne_one m (a.perm r)
    exact Subgroup.disjoint_def.mp hd
      (subset_closure ⟨a.perm r, 1, hpr, rfl⟩) (transported_root_mem a r hr 1)
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    change (MulAut.conj n) (rootGeneratorInGroup m r t) ∈ splitNegativeUnipotent m
    rw [a.conj_root]
    exact subset_closure ⟨a.perm r, _, hp r hr, rfl⟩
  · apply (closure_le _).mpr
    rintro x ⟨r, t, hr, rfl⟩
    obtain ⟨s, hs, rfl⟩ := perm_positive_eq_negative a.perm hp r hr
    exact transported_root_mem a s hs t

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell
end
