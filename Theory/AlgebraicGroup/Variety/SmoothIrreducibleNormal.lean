module

public import Theory.AlgebraicGroup.CoordinateRing.SmoothDomainNormal
public import Theory.AlgebraicGroup.Variety.Complete
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Normality of smooth irreducible varieties

Every stalk of a smooth irreducible geometric variety is an integrally closed domain.
Irreducibility and the reducedness built into `Geometric` make every nonempty affine
section ring a domain. Smoothness makes that ring integrally closed by its local étale
presentations over polynomial rings. Both properties pass to its prime localizations,
which are the scheme stalks.

This is the smooth-variety consequence of Borel, *Linear Algebraic Groups*, AG.18.1
(`refs/KGroup/Bor1/ChapterAG.tex`, lines 1370–1374), used for the closed orbit in the
proof of §10.4 (`refs/KGroup/Bor1/Chapter3.tex`, lines 851–859).
-/

open CategoryTheory AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

/-- A smooth irreducible geometric variety is normal in the stalkwise sense of AG.18.1. -/
public theorem isNormal_of_isIrreducible_of_smooth
    {k : Type u} [Field k] [IsAlgClosed k] (V : Geometric k) (hV : IsIrreducible V)
    (hsm : AlgebraicGeometry.Smooth V.structureMap) : IsNormal V := by
  let _ : IrreducibleSpace V.toScheme := hV
  let _ : IsIntegral V.toScheme :=
    isIntegral_of_irreducibleSpace_of_isReduced V.toScheme
  let _ : AlgebraicGeometry.Smooth V.structureMap := hsm
  intro x
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : V.toScheme.Opens) from trivial)
  let _ : Nonempty U := ⟨⟨x, hx⟩⟩
  let ek : k ≃+* Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  let f : k →+* Γ(V.toScheme, U) :=
    (V.structureMap.appLE ⊤ U (by simp)).hom.comp ek.toRingHom
  have hf : f.Smooth := by
    exact (RingHom.Smooth.of_bijective ek.bijective).comp
      (V.structureMap.smooth_appLE (isAffineOpen_top _) hU (by simp))
  algebraize [f]
  let _ : Algebra.Smooth k Γ(V.toScheme, U) := hf
  let _ : IsIntegrallyClosed Γ(V.toScheme, U) :=
    Theory.AlgebraicGroup.isIntegrallyClosed_of_smooth_of_isDomain k Γ(V.toScheme, U)
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ : Algebra Γ(V.toScheme, U) (V.toScheme.presheaf.stalk x) :=
    V.toScheme.presheaf.algebra_section_stalk ⟨x, hx⟩
  let _ : IsLocalization.AtPrime (V.toScheme.presheaf.stalk x) p :=
    hU.isLocalization_stalk ⟨x, hx⟩
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ p.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

end Theory.AlgebraicGroup.Variety.Geometric
