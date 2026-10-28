module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.AtlasPort.OtherSporadic.Conway.NormalGenerationElement

/-!
# Mathieu-coordinate recognition for integral octad fusion

The existing exhaustive involution theorem for the native Witt-design M₂₄
has two classes. Its fixed-point-free representative cannot be conjugate
to an element fixing a coordinate. The proved Golay coordinate equivalence
preserves the actual permutation action, so the same distinction holds in
`Mathieu24CodeModel`. The nontrivial permutation of the sextet-conjugated
Golay sign fixes an octad and supplies the required representative.

This uses the concrete carrier equivalence and its action formula, not an
abstract family identification. Source context: Aschbacher, *Sporadic Groups*
(1994), 25.1–25.5 and 49.3–49.4; the native involution coverage is the
existing M₂₄ Sylow certificate. The coordinate equivalence reuses the
attributed ATLAS code construction under `LICENSES/ATLAS.txt`.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open Sporadic.Mathieu
open Sporadic.Mathieu.M24LocalGeometry.SextetCore
open Sporadic.Mathieu.M24InvolutionCentralizers

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

private theorem native_twoB_fixedFree (i : Fin 24) : involution2B.val i ≠ i := by
  revert i
  decide +kernel

private theorem native_fixed_involution_isConj (x : M24) (hx : orderOf x = 2)
    (hf : ∃ i : Fin 24, x.val i = i) : IsConj involution2A x := by
  rcases involution_classes x hx with h | h
  · exact h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    obtain ⟨i, hi⟩ := hf
    have he := congrArg (fun a : M24 => a.val i) hg
    change g.val (involution2B.val (g.val.symm i)) = x.val i at he
    rw [hi] at he
    exact (native_twoB_fixedFree (g.val.symm i)
      (g.val.injective (he.trans (g.val.apply_symm_apply i).symm))).elim

/-- A nonidentity Golay-coordinate involution with a fixed point belongs to
the fixed-point involution class of the native Witt-design group. -/
theorem mathieu_fixed_involution_isConj_native (p : Mathieu24CodeModel)
    (hp : Function.Involutive p.val.symm) (hne : p ≠ 1)
    (hf : ∃ i : Omega, p.val.symm i = i) : IsConj (groupEquiv involution2A) p := by
  let x := groupEquiv.symm p
  have hsq : p ^ 2 = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    change p.val (p.val i) = i
    simpa using (congrArg p.val (hp (p.val i))).symm
  have hxsq : x ^ 2 = 1 := by
    apply groupEquiv.injective
    simp only [map_pow, map_one, x, MulEquiv.apply_symm_apply, hsq]
  have hxne : x ≠ 1 := by
    intro h
    apply hne
    have hh := congrArg groupEquiv h
    simpa [x] using hh
  have hfx : ∃ i : Fin 24, x.val i = i := by
    obtain ⟨i, hi⟩ := hf
    refine ⟨MathieuCode.atlasPointEquiv i, ?_⟩
    have hpi : p.val i = i := by
      have h := congrArg p.val hi
      simpa using h.symm
    have he : groupEquiv x = p := groupEquiv.apply_symm_apply p
    have hi' : (groupEquiv x).val i = i := by rw [he]; exact hpi
    change MathieuCode.atlasPointEquiv.symm (x.val (MathieuCode.atlasPointEquiv i)) = i at hi'
    have hh := congrArg MathieuCode.atlasPointEquiv hi'
    simpa using hh
  have hc := native_fixed_involution_isConj x (orderOf_eq_prime hxsq hxne) hfx
  have hc' : IsConj (groupEquiv involution2A) (groupEquiv x) :=
    groupEquiv.toMonoidHom.map_isConj hc
  simpa only [x, MulEquiv.apply_symm_apply] using hc'

/-- The literal eight-fixed-point permutation in the sextet construction
is the unique nonidentity Mathieu involution class with fixed coordinates. -/
theorem mathieu_fixed_involution_isConj_normalGeneration (p : Mathieu24CodeModel)
    (hp : Function.Involutive p.val.symm) (hne : p ≠ 1)
    (hf : ∃ i : Omega, p.val.symm i = i) : IsConj p normalGenerationMonomial.right := by
  have hrep : IsConj (groupEquiv involution2A) normalGenerationMonomial.right :=
    mathieu_fixed_involution_isConj_native normalGenerationMonomial.right
      (by
        intro i
        exact congrArg (fun q : Equiv.Perm Omega => q i)
          normalGeneration_permutation_shape.2)
      normalGenerationMonomial_permutation_ne_one ⟨((1,1),0), rfl⟩
  exact (mathieu_fixed_involution_isConj_native p hp hne hf).symm.trans hrep

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
