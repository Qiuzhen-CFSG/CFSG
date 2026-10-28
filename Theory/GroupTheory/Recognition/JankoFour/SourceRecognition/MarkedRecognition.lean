module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.Native.LocalData
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicSplitting
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Recognition

/-!
# Ambient recognition from a genuine cocode marking

The source-side marked constructors already build the complete local package:
the marked cocode normalizer gives `LocalData`, and the same marking gives the
perfectness and involutory splitting clauses for its cubic normalizer.  The
literal Janko model supplies the corresponding native package, its generation
equality, and its cubic-normalizer data.  This module performs the final
source-base comparison under the one hypothesis that the ambient source is
simple.

The theorem is deliberately conditional on the actual cocode marking.  It is
the precise consumer needed by the eventual arbitrary `IsTypeJ4` construction;
it does not encode that construction as an interface or infer it from a group
family tag.

Source: Aschbacher--Segev, *The uniqueness of groups of type J4*, Invent.
Math. 105 (1991), (4.4)--(4.9) and section 8, pp.597--599,605--607,
DOI 10.1007/BF01232280.
-/

public noncomputable section
open Subgroup
open Sporadic.Mathieu MathieuCode M24LocalGeometry
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open LocalGeometry LocalGeometry.LocalSubgroups SourceComparison

variable {G : Type*} [Group G] [Finite G]

/-- A genuine marked cocode normalizer yields the ambient J₄ equivalence.

The marker `z` is retained in the source local data, while the target local
data and generation are constructed on the literal native model.  The source
simple-group instance is explicit because the comparison proof uses it to
exclude the top kernel of the extended local homomorphism.
-/
theorem exists_marked_cocode_recognition
    (W : Subgroup G) [IsElementaryAbelian 2 W]
    (f : normalizer (W : Set G) →* M24) (hf : Function.Surjective f)
    (hk : f.ker = W.subgroupOf (normalizer (W : Set G)))
    (E : Additive W ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)))
    (z : W) (sextet : Sextet)
    (hz : E (Additive.ofMul z) = sextetVector sextet)
    (h : IsTypeJ4 (z : G))
    (marked_hsimple : IsSimpleGroup G) :
    Nonempty (G ≃* Janko4.Model) := by
  let : IsSimpleGroup G := marked_hsimple
  obtain ⟨cubic⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (CubicLift.subgroup cubic)))
  obtain ⟨data, _, _, _, _, _, _⟩ :=
    marked_cocode_localData W f hf hk E hE z sextet hz h cubic X
  have source_normalizer : Nonempty (CubicNormalizerData data) := by
    obtain ⟨v, hv, hout, _⟩ :=
      marked_fullCubicNormalizer_split W f hf hk E hE z sextet hz h data.e data.X
    exact ⟨{
      perfect := marked_fullCubicCentralizer_perfect W f hf hk E hE z sextet hz h
        data.e data.X
      s := v.val
      s_mem := v.property
      s_sq := by
        have hh : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
        exact congrArg Subtype.val (by simpa only [pow_two] using hh)
      s_not_mem := hout }⟩
  obtain ⟨native, native_generate, native_normalizer⟩ :=
    NativeCocode.exists_first_local_geometry
  obtain ⟨_, _, _, _, _, F, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    SourceComparison.exists_recognition_equiv data native
      (Classical.choice source_normalizer) (Classical.choice native_normalizer) native_generate
  exact ⟨F⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
