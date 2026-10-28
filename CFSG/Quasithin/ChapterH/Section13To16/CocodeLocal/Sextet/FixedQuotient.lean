module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Sextet.Geometry
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.FixedQuotient

/-!
# The fixed-quotient reduction for the native sextet

The intrinsic two-core is normal in the sextet stabilizer. The general
irreducible-top-section argument therefore identifies the fixed vectors modulo
the geometric tetrad line once the middle-section action, top irreducibility,
and one element's displacement have been established. The result uses the
literal quotient of the native cocode and its geometric pair space.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(4),
printed p.400. The action and irreducibility inputs are explicit: this reduction
does not yet identify the tetrad line with the full two-core fixed space.
-/

@[expose] public section

noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open MathieuCode Representation.BinaryOffender

/-- Restriction to the local stabilizer preserves the individual fixed space. -/
lemma sextetRepresentation_cyclic_fixedSpace (S : Sextet) (a : sextetStabilizer S) :
    fixedSpace (sextetRepresentation S) (Subgroup.zpowers a) =
      fixedSpace cocodeRepresentation (Subgroup.zpowers a.val) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff, mem_fixedSpace_zpowers_iff]
  rfl

/-- The corresponding cyclic fixed codimension is independent of the local restriction. -/
lemma sextetRepresentation_cyclic_fixedCodim (S : Sextet) (a : sextetStabilizer S) :
    fixedCodim (sextetRepresentation S) (Subgroup.zpowers a) =
      fixedCodim cocodeRepresentation (Subgroup.zpowers a.val) := by
  unfold fixedCodim
  rw [sextetRepresentation_cyclic_fixedSpace]

/-- The native fixed quotient follows from the top chief factor and middle action,
using an element of displacement greater than one to exclude a trivial action. -/
lemma sextet_fixedQuotient_eq_pair_image_of_layers (S : Sextet)
    (hirr : Representation.IsIrreducible (sextetPairSubrepresentation S).quotientRepresentation)
    (hcomm : ∀ n ∈ sextetKernel S, ∀ w ∈ sextetPairSpace S,
      cocodeRepresentation n w - w ∈ sextetTetradLine S)
    (a : sextetStabilizer S) (ha : a ∈ pCore 2 (sextetStabilizer S))
    (hcodim : 1 < fixedCodim cocodeRepresentation (Subgroup.zpowers a.val)) :
    fixedSpace (sextetLineSubrepresentation S).quotientRepresentation
        (pCore 2 (sextetStabilizer S)) =
      (sextetPairSpace S).map (sextetTetradLine S).mkQ := by
  let := hirr
  apply fixedSpace_quotient_eq_image_of_fixedCodim (sextetRepresentation S)
    (sextetLineSubrepresentation S) (sextetPairSubrepresentation S)
    (sextetTetradLine_le_pairSpace S) (pCore 2 (sextetStabilizer S)) ?_ a ha ?_
  · intro n hn w hw
    exact hcomm n.val ⟨n, hn, rfl⟩ w hw
  · change Module.finrank (ZMod 2) (sextetTetradLine S) <
      fixedCodim (sextetRepresentation S) (Subgroup.zpowers a)
    rwa [sextetTetradLine_finrank, sextetRepresentation_cyclic_fixedCodim]

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
