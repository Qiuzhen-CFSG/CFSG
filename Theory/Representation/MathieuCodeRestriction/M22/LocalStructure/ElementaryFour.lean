module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.ElementaryFour.Quotient
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.ElementaryFour.ModuleCases
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The source alternatives for elementary subgroups in the outer M22

The ambient group is the literal setwise stabilizer of `{0,9}` in native M24.
The inner subgroup is the range of the published native M22 embedding. The
hexad and quintet kernels are the mapped intrinsic two-cores of their actual
stabilizers. A source-compatible Sylow arrangement includes a common M24 Sylow
stabilizing all three incident objects; incidence alone is not this condition.

The exceptional alternative uses the two-core inside the full centralizer,
its image in the ambient group, and an isomorphism of the intrinsic quotient
with the actual projective special linear group. The four-alternative predicate
below is a specification, not an assertion that it holds.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.14 setup,
printed p.396, and H.15.5, printed pp.400--401.
-/

@[expose] public section

noncomputable section
namespace MathieuCode.M22ElementaryFour

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Representation.BinaryOffender

abbrev Ambient := m22PairStabilizer
abbrev Inner : Subgroup Ambient := m22ToPairStabilizer.range
abbrev Hexad : Subgroup Ambient := m22OuterHexadStabilizer m22SourceOctad
abbrev HexadKernel : Subgroup Ambient := m22OuterHexadKernel m22SourceOctad
abbrev QuintetKernel : Subgroup Ambient := m22OuterQuintetKernel m22SourceSextet

/-- The actual common Sylow arrangement in the source's H.14 setup. -/
def SourceCompatible (T : Sylow 2 Ambient) : Prop :=
  ∃ T₀ : Sylow 2 M24,
    (T : Subgroup Ambient) = (T₀ : Subgroup M24).comap m22PairStabilizer.subtype ∧
    (T₀ : Subgroup M24) ≤ octadStabilizer m22SourceOctad ∧
    (T₀ : Subgroup M24) ≤ trioStabilizer m22SourceTrio ∧
    (T₀ : Subgroup M24) ≤ sextetStabilizer m22SourceSextet

theorem SourceCompatible.le_hexad {T : Sylow 2 Ambient} (hT : SourceCompatible T) :
    (T : Subgroup Ambient) ≤ Hexad := by
  obtain ⟨T₀, he, hO, _, _⟩ := hT
  rw [he]
  exact Subgroup.comap_mono hO

/-- The full ambient centralizer of the actual element. -/
def elementCentralizer (i : Ambient) : Subgroup Ambient :=
  Subgroup.centralizer ({i} : Set Ambient)

/-- Take the two-core intrinsically, then include it into the ambient group. -/
def elementCentralizerCore (i : Ambient) : Subgroup Ambient :=
  (pCore 2 (elementCentralizer i)).map (elementCentralizer i).subtype

theorem elementCentralizerCore_le (i : Ambient) :
    elementCentralizerCore i ≤ elementCentralizer i := Subgroup.map_subtype_le _

/-- Relative normality suffices: the full centralizer normalizes its embedded core. -/
theorem elementCentralizer_le_normalizer_core (i : Ambient) :
    elementCentralizer i ≤ Subgroup.normalizer (elementCentralizerCore i) := by
  have h := (pCore 2 (elementCentralizer i)).le_normalizer_map
    (elementCentralizer i).subtype
  simpa only [elementCentralizerCore, Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] using h

/-- An actual octad fixed pointwise, disjoint from the distinguished pair. -/
def FixesDisjointOctad (i : Ambient) : Prop :=
  ∃ O : Octad, Disjoint O.val m22Pair ∧ ∀ x ∈ O.val, i.val • x = x

/-- Fusion is witnessed by conjugation in the actual setwise pair stabilizer. -/
def FusedIntoQuintet (A : Subgroup Ambient) : Prop :=
  ∃ g : Ambient, A.map (MulAut.conj g).toMonoidHom ≤ QuintetKernel

/-- All group-theoretic clauses of the exceptional outer-centralizer branch. -/
def ExceptionalCore (A : Subgroup Ambient) : Prop :=
  ∃ i : Ambient, i ∈ A ∧ i ∉ Inner ∧ orderOf i = 2 ∧ FixesDisjointOctad i ∧
    A = elementCentralizerCore i ∧
    Nonempty ((elementCentralizer i ⧸ pCore 2 (elementCentralizer i)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))

/-- The complete four alternatives of H.15.5 on the literal cocode.
This definition does not assert exhaustive coverage. -/
def FourAlternatives (A : Subgroup Ambient) : Prop :=
  (A = HexadKernel ∧
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 5 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) = 1) ∨
  (FusedIntoQuintet A ∧
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 ∧
    fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤) ∨
  (ExceptionalCore A ∧
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 3 ∧
    fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤) ∨
  (Nat.card (A ⊓ HexadKernel : Subgroup Ambient) = 8 ∧
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 3 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸ fixedSpaceSpan m22OuterCocodeRepresentation A) ≤ 1)

/-- H.15.4(3) transfers from every order-sixteen subgroup of the quintet
kernel to every subgroup fused into it by the actual ambient action. -/
theorem quintet_module_case
    (hQ : ∀ B : Subgroup Ambient, B ≤ QuintetKernel → Nat.card B = 16 →
      Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation B) = 2 ∧
      fixedSpaceSpan m22OuterCocodeRepresentation B = ⊤)
    (A : Subgroup Ambient) (hA : Nat.card A = 16) (hfused : FusedIntoQuintet A) :
    Module.finrank (ZMod 2) (fixedSpace m22OuterCocodeRepresentation A) = 2 ∧
      fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ := by
  obtain ⟨g, hg⟩ := hfused
  have hcard : Nat.card (A.map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]
  obtain ⟨hfix, hspan⟩ := hQ _ hg hcard
  exact conjugate_module_case m22OuterCocodeRepresentation A g hfix hspan

/-- The exceptional span calculation uses the intrinsic core's relative
normality, a displaced three-space, and irreducibility above `C_V(i)`.
The local geometry and representation hypotheses are not asserted here. -/
theorem exceptional_module_case (i z : Ambient)
    (hi : i ∈ elementCentralizerCore i) (hi1 : i ≠ 1)
    (hz : z ∈ elementCentralizerCore i) (hz1 : z ≠ 1)
    (hfixed : fixedSpace m22OuterCocodeRepresentation (elementCentralizerCore i) =
      LinearMap.range (m22OuterCocodeRepresentation i - LinearMap.id))
    (hdisplaced : fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers i) = 3)
    (hnot : ¬ fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers z) ≤
      fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i))
    (hirr : ∀ U : Submodule (ZMod 2) M22Cocode,
      elementCentralizer i ≤ subspaceStabilizer m22OuterCocodeRepresentation U →
      fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i) ≤ U →
      U = fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers i) ∨ U = ⊤) :
    Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (elementCentralizerCore i)) = 3 ∧
      fixedSpaceSpan m22OuterCocodeRepresentation (elementCentralizerCore i) = ⊤ := by
  refine ⟨?_, fixedSpaceSpan_eq_top_of_irreducible_interval m22OuterCocodeRepresentation
    _ _ i z hi hi1 hz hz1 (elementCentralizer_le_normalizer_core i) hnot hirr⟩
  rw [hfixed, ← fixedCodim_zpowers_eq_displacement_rank]
  exact hdisplaced

end MathieuCode.M22ElementaryFour
