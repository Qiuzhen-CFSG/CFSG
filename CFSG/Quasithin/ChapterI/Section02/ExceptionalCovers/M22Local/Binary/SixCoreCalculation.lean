module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Transport
public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual.Calculation

/-!
# Application of the six-letter calculation to a marked fixed hexad

An actual fixed-hexad isomorphism, with the ambient central line marked, turns
the model calculation into the unique square in the ambient central coset.
Noncentrality supplies the nonzero natural-module condition. The original
conditional interface is retained, and the final theorem discharges both
model subgroup identities. Only the actual marked fixed-hexad isomorphism
remains an input to this application.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
open BinaryPermutation BinaryPermutation.SixCoreExtension

variable {K : Type*} [Group K] [Finite K]

/-- Apply the model computation with the literal quotient and its marked central line. -/
theorem uniqueSquare_of_sixCore_model_of_identities
    (hres : centralizerTwoResidual (vector (Multiplicative.ofAdd pair)) = pairResidual)
    (hcore : pairResidual.pCoreIn 2 = pairCore)
    (e : (K ⧸ center K) ≃* M22) (u : K)
    (hu : orderOf u = 2) (hun : u ∉ center K)
    (f : hexadPreimage e (m22FixedPoints (projection e u)) ≃* Model)
    (hline : ((center K).subgroupOf
      (hexadPreimage e (m22FixedPoints (projection e u)))).map f.toMonoidHom = centralLine)
    (v : V) (hmark : f (fixedHexadElement e u) = vector (Multiplicative.ofAdd v)) :
    HasUniqueCoreSquareLift u := by
  have hv : coreToNatural (Fin 6) v ≠ 0 := by
    intro hz
    have hm : f (fixedHexadElement e u) ∈ centralLine := by
      rw [hmark]
      exact mem_map.mpr ⟨Multiplicative.ofAdd v, hz, rfl⟩
    rw [← hline, mem_map_equiv, f.symm_apply_apply] at hm
    exact hun hm
  apply uniqueSquare_of_fixedHexad_model e u hu hun f centralLine hline
  rw [hmark]
  exact unique_square_of_identities hres hcore v hv

/-- The six-letter calculation supplies the ambient unique square once the
actual fixed-hexad extension and ambient central line have been identified.
No residual or two-core computation remains as an extra premise. -/
theorem uniqueSquare_of_sixCore_model
    (e : (K ⧸ center K) ≃* M22) (u : K)
    (hu : orderOf u = 2) (hun : u ∉ center K)
    (f : hexadPreimage e (m22FixedPoints (projection e u)) ≃* Model)
    (hline : ((center K).subgroupOf
      (hexadPreimage e (m22FixedPoints (projection e u)))).map f.toMonoidHom = centralLine)
    (v : V) (hmark : f (fixedHexadElement e u) = vector (Multiplicative.ofAdd v)) :
    HasUniqueCoreSquareLift u :=
  uniqueSquare_of_sixCore_model_of_identities centralizerTwoResidual_pair
    pairResidual_pCoreIn e u hu hun f hline v hmark

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local
