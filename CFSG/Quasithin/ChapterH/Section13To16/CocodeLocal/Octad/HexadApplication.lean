module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Octad.HexadInputs
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadInputs
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad

/-!
# Application of the octad theorem to the marked M22 hexad

The native H.14 kernel marking and the proved M24 inputs discharge the earlier
premises of the existing inner and outer hexad transfers. Thus both actual
M22 cocode fixed spaces have dimension five, their fixed-space spans are
hyperplanes, and their kernel actions contain every transvection with the
prescribed axis. The action comparison retains the literal pair-line quotient.

Source: Aschbacher--Smith H.15.2(2--6), printed pp.398--399.
-/

@[expose] public section
noncomputable section
open Sporadic.Mathieu MathieuCode Representation.BinaryOffender
open MathieuCode.Hexad.CocodeAction.Transvections
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal

/-- The inner source hexad now has its fixed-space dimension and hyperplane
without any earlier-M24 or group-marking premise. -/
theorem m22_hexad_fixed_dimensions :
    Module.finrank (ZMod 2)
      (fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) = 5 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸
      fixedSpaceSpan m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) = 1 := by
  have h := M22Local.Hexad.inner_fixed_clauses M22ChapterH.Hexad.innerRestriction
    (hexadAmbientFixedInput m22SourceOctad)
  exact ⟨h.1, h.2.1⟩

/-- The same application uses the full setwise pair stabilizer as its actor. -/
theorem m22_outer_hexad_fixed_dimensions :
    Module.finrank (ZMod 2)
      (fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) = 5 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸
      fixedSpaceSpan m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) = 1 := by
  have h := M22Local.Hexad.outer_fixed_clauses M22ChapterH.Hexad.outerRestriction
    (hexadAmbientFixedInput m22SourceOctad)
  exact ⟨h.1, h.2.1⟩

/-- The source weight-two avoidance bound in the literal native M22 fixed space. -/
theorem m22_hexad_avoiding_finrank_le (I : Submodule (ZMod 2) M22Cocode)
    (hI : I ≤ fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad))
    (ha : Disjoint (I : Set M22Cocode) m22WeightTwoFamily) : Module.finrank (ZMod 2) I ≤ 4 :=
  (M22Local.Hexad.inner_fixed_clauses M22ChapterH.Hexad.innerRestriction
    (hexadAmbientFixedInput m22SourceOctad)).2.2.1 I hI ha

/-- The inner kernel induces every transvection in the actual iterated quotient. -/
theorem m22_hexad_full_transvections
    (T : Module.End (ZMod 2) (M22Cocode ⧸
      fixed m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad))) :
    (∃ a : m22InnerHexadKernel m22SourceOctad,
      quotientAction M22ChapterH.Hexad.innerRestriction
        ⟨a.val, kernel_le M22ChapterH.Hexad.innerRestriction a.property⟩ = T) ↔
    ∃ b : axis m22ToPairStabilizer (m22InnerHexadKernel m22SourceOctad), ∀ x,
      T x = x + parity M22ChapterH.Hexad.innerRestriction
        (hexadAmbientFixedInput m22SourceOctad).displacement
        (hexadAmbientTransvectionInput m22SourceOctad) x • b.val :=
  full_image M22ChapterH.Hexad.innerRestriction
    (hexadAmbientFixedInput m22SourceOctad).displacement
    (hexadAmbientTransvectionInput m22SourceOctad) T

/-- The outer actor uses the same pair-line quotient and retains the full image. -/
theorem m22_outer_hexad_full_transvections
    (T : Module.End (ZMod 2) (M22Cocode ⧸
      fixed (MonoidHom.id MathieuCode.m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad))) :
    (∃ a : m22OuterHexadKernel m22SourceOctad,
      quotientAction M22ChapterH.Hexad.outerRestriction
        ⟨a.val, kernel_le M22ChapterH.Hexad.outerRestriction a.property⟩ = T) ↔
    ∃ b : axis (MonoidHom.id MathieuCode.m22PairStabilizer) (m22OuterHexadKernel m22SourceOctad), ∀ x,
      T x = x + parity M22ChapterH.Hexad.outerRestriction
        (hexadAmbientFixedInput m22SourceOctad).displacement
        (hexadAmbientTransvectionInput m22SourceOctad) x • b.val :=
  full_image M22ChapterH.Hexad.outerRestriction
    (hexadAmbientFixedInput m22SourceOctad).displacement
    (hexadAmbientTransvectionInput m22SourceOctad) T

/-- The source M24 pointwise-centralizer theorem descends through the pair
line to every nonidentity element of the marked inner hexad kernel. -/
theorem m22_hexad_pointwiseCentralizer (z : M22)
    (hz : z ∈ m22InnerHexadKernel m22SourceOctad) (hne : z ≠ 1) :
    subspaceKernel m22CocodeRepresentation
      (fixedSpace m22CocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z :=
  Hexad.CocodeAction.pointwiseCentralizer_of_conjugate_kernel
    M22ChapterH.Hexad.innerRestriction m22Pair_le_sourceOctad
    (hexadAmbientFixedInput m22SourceOctad).displacement
    (hexadAmbientCentralizerInput m22SourceOctad) z ⟨z, hz, hne, IsConj.refl z⟩

/-- The same conclusion holds in the full native pair stabilizer. -/
theorem m22_outer_hexad_pointwiseCentralizer (z : MathieuCode.m22PairStabilizer)
    (hz : z ∈ m22OuterHexadKernel m22SourceOctad) (hne : z ≠ 1) :
    subspaceKernel m22OuterCocodeRepresentation
      (fixedSpace m22OuterCocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z := by
  simpa only [Hexad.quotientRepresentation, MonoidHom.comp_id] using
    Hexad.CocodeAction.pointwiseCentralizer_of_conjugate_kernel
      M22ChapterH.Hexad.outerRestriction m22Pair_le_sourceOctad
      (hexadAmbientFixedInput m22SourceOctad).displacement
      (hexadAmbientCentralizerInput m22SourceOctad) z ⟨z, hz, hne, IsConj.refl z⟩

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
