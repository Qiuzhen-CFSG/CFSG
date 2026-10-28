module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry


/-!
# The compatible quintet line and the hexad commutator

The distinguished tetrad is {0,2,9,14}. Removing the pair {0,9} identifies
its cocode class with the pair {2,14}, both of whose points lie in the
marked octad. Hence its line lies in the hexad fixed cocode space, and
annihilation puts the actual code commutator inside its hyperplane.
The line is nonzero and is fixed by the actual quintet kernel. The earlier
quintet fixed dimension one therefore identifies it with the entire fixed
space. The earlier code fixed dimension four excludes containment of the
rank-five hexad commutator in that fixed space.

Source: Aschbacher--Smith, H.16.4(4), printed p.403, combined manuscript of
1 March 2004. This uses the compatible native sextet and actual two-cores;
no arbitrary flag-incidence premise is used. The two quintet fixed dimensions
remain explicit earlier inputs. No new ATLAS code is ported here; the reused
Golay minimum-distance provenance is recorded in CocodeLocal/Sextet/Geometry.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
namespace MathieuCode.Hexad.ChiefFlag

/-- The actual sextet tetrad class in the M22 cocode. -/
def quintetVector : M22Cocode := m22PairLine.mkQ (sextetVector m22SourceSextet)

theorem quintetVector_eq_pair : quintetVector = m22CocodePair 2 14 := by
  have he : sextetVector m22SourceSextet =
      codeInCore.mkQ (m22EvenPair 0 9) + codeInCore.mkQ (m22EvenPair 2 14) := by
    rw [sextetVector_eq m22SourceSextet m22SourceTetrad_mem, ← map_add]
    apply congrArg codeInCore.mkQ
    apply Subtype.ext
    ext i
    fin_cases i <;> decide +kernel
  rw [quintetVector, he, map_add]
  change m22CocodePair 0 9 + m22CocodePair 2 14 = m22CocodePair 2 14
  rw [m22CocodePair_distinguished, zero_add]


theorem quintetVector_ne_zero : quintetVector ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero m22PairLine).mp hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hp : m22PairClass = pairVector ⟨m22Pair, by decide +kernel⟩ := by
    apply congrArg codeInCore.mkQ
    exact Subtype.ext m22PairWord_eq_wordOfSet
  have hcases : c = 0 ∨ c = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c
  rcases hcases with rfl | rfl
  · exact sextetVector_ne_zero _ (by simpa using hc.symm)
  · exact pairVector_ne_sextetVector _ _ (by simpa [hp] using hc)


def quintetLine : Submodule (ZMod 2) M22Cocode :=
  Submodule.span (ZMod 2) {quintetVector}

theorem quintetLine_finrank : Module.finrank (ZMod 2) quintetLine = 1 :=
  finrank_span_singleton quintetVector_ne_zero

theorem quintetVector_fixed (g : m22OuterQuintetStabilizer m22SourceSextet) :
    m22OuterCocodeRepresentation g.val quintetVector = quintetVector := by
  change m22OuterCocodeRepresentation g.val
    (m22PairLine.mkQ (sextetVector m22SourceSextet)) = _
  rw [m22OuterCocodeRepresentation_mk,
    sextetVector_fixed m22SourceSextet ⟨g.val.val, g.property⟩]
  rfl

theorem quintetLine_le_quintet_fixed :
    quintetLine ≤ fixedSpace m22OuterCocodeRepresentation
      (m22OuterQuintetKernel m22SourceSextet) := by
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff]
  intro g
  obtain ⟨a, _, ha⟩ := g.property
  change m22OuterCocodeRepresentation g.val quintetVector = quintetVector
  rw [← ha]
  exact quintetVector_fixed a

/-- H.15.4's fixed dimension identifies the literal fixed space with the
marked tetrad line; no geometric flag compatibility is assumed. -/
theorem quintet_fixed_eq_line
    (hQ : Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation
      (m22OuterQuintetKernel m22SourceSextet)) = 1) :
    fixedSpace m22OuterCocodeRepresentation (m22OuterQuintetKernel m22SourceSextet) =
      quintetLine := by
  symm
  exact Submodule.eq_of_le_of_finrank_eq quintetLine_le_quintet_fixed
    (quintetLine_finrank.trans hQ.symm)

def quintetHyperplane : Submodule (ZMod 2) M22Code :=
  quintetLine.dualAnnihilator.comap m22CodeCocodeDuality.toLinearMap

theorem quintetHyperplane_finrank : Module.finrank (ZMod 2) quintetHyperplane = 9 := by
  have he : quintetHyperplane.map m22CodeCocodeDuality.toLinearMap =
      quintetLine.dualAnnihilator :=
    Submodule.map_comap_eq_of_surjective m22CodeCocodeDuality.surjective _
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq quintetLine
  rw [quintetLine_finrank, finrank_m22Cocode, ← he, LinearEquiv.finrank_map_eq] at hd
  omega


theorem quintetLine_le_hexad_fixed
    (h : OuterRestrictionInput m22SourceOctad) :
    quintetLine ≤ fixedSpace m22OuterCocodeRepresentation
      (m22OuterHexadKernel m22SourceOctad) := by
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff, quintetVector_eq_pair]
  exact cocodePair_mem_fixedSpace (MonoidHom.id m22PairStabilizer)
    (m22OuterHexadKernel m22SourceOctad) m22SourceOctad 2 14
    (by decide +kernel) (by decide +kernel) h.kernel_image

/-- The geometric containment, using the literal compatible tetrad. -/
theorem commutator_le_quintetHyperplane
    (h : OuterRestrictionInput m22SourceOctad) :
    codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤ quintetHyperplane := by
  rw [codeCommutator_eq_annihilator]
  exact Submodule.comap_mono
    ((Subspace.dualAnnihilator_le_dualAnnihilator_iff).mpr (quintetLine_le_hexad_fixed h))

theorem commutator_not_le_quintet_fixed
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hQ : Module.finrank (ZMod 2) (fixedSpace m22OuterCodeRepresentation
      (m22OuterQuintetKernel m22SourceSextet)) = 4) :
    ¬ codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤
      fixedSpace m22OuterCodeRepresentation (m22OuterQuintetKernel m22SourceSextet) := by
  intro hle
  have hd := Submodule.finrank_mono hle
  rw [codeCommutator_finrank _ (h.fixedSpace_finrank h24.displacement h24.fixed_finrank),
    hQ] at hd
  omega

end MathieuCode.Hexad.ChiefFlag
