module

public import Theory.Representation.HexacodeAction.ProjectiveLineNormalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.NormalizerTransport

/-!
# Applying the concrete projective-line obstruction to the covered-six block

An explicit `HexacodeModel` carries the literal binary subspaces of the
original block layer to the actual hexacode. Equivariant stabilizer transport,
combined with `ambientNormalizer_image`, identifies the image of the full
relative ambient normalizer with the full model stabilizer.

The concrete obstruction excludes an invariant subgroup of order four when
the order-sixteen plane is the fixed space of the marked four-group. Applied
to `l = [V,Lᵥ]`, `source_line_invariant_of_placement` supplies invariance and
binary dimension two, using the proved `source_commutator_card`.

This is a conditional source adapter: the representation model, marked
four-group, fixed-plane equality and placement in Mᵥ remain explicit inputs.
Their construction and the complete covered-six branch belong to the parent
`CoveredSix` assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.6.22,
printed p.932 (PDF p.949). The imported model theorem retains the actual
ATLAS-derived hexacode and its attribution; see `LICENSES/ATLAS.txt`.
-/

public section

open Subgroup CFSG.Quasithin.ChapterC Theory.GroupTheory Representation
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
variable {G : Type*} [Group G] (K : Subgroup G) (h : IsExceptionalAhat6Block K)
    [IsElementaryAbelian 2 (blockU K)] (e : HexacodeModel h)

/-- Both the actor isomorphism and vector coordinates transport the entire stabilizer. -/
theorem model_stabilizer_image (P : Submodule (ZMod 2) (Additive (blockU K))) :
    (subspaceStabilizer (binaryAction h) P).map e.quotientIso.toMonoidHom =
      subspaceStabilizer Hexacode.evenAction (P.map e.coordinates.toLinearMap) :=
  map_subspaceStabilizer_equivariant (binaryAction h) Hexacode.evenAction
    e.quotientIso e.coordinates e.intertwining P

/-- The literal relative normalizer maps onto the full hexacode stabilizer. -/
theorem ambientNormalizer_model_image (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) :
    (((K ⊓ normalizer (P : Set G)).subgroupOf K).map
      (QuotientGroup.mk' (pCore 2 K))).map e.quotientIso.toMonoidHom =
        subspaceStabilizer Hexacode.evenAction
          ((ambientSubspace K P).map e.coordinates.toLinearMap) := by
  rw [ambientNormalizer_image K h P hP]
  exact model_stabilizer_image K h e _

private theorem ambientSubspace_finrank_four (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) (hc : Nat.card P = 16) :
    Module.finrank (ZMod 2) (ambientSubspace K P) = 4 := by
  let : Finite P := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (ambientSubspace K P) :=
    Finite.of_equiv P (ambientSubspaceEquiv K P hP).symm
  have he := Nat.card_congr (ambientSubspaceEquiv K P hP)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hc] at he
  exact Nat.pow_right_injective (by decide : 1 < 2) he

private theorem model_no_invariant_two
    (P Q : Submodule (ZMod 2) (Additive (blockU K)))
    (hP : Module.finrank (ZMod 2) P = 4) (hQ : Module.finrank (ZMod 2) Q = 2)
    (A : Subgroup Atlas.Codes.HexEvenAutomorphisms) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hfix : P.map e.coordinates.toLinearMap = fixedSpace Hexacode.evenAction A) :
    ¬ subspaceStabilizer (binaryAction h) P ≤ subspaceStabilizer (binaryAction h) Q := by
  intro hN
  have hfixed : Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction A) = 4 := by
    rw [← hfix, e.coordinates.finrank_map_eq]
    exact hP
  apply Hexacode.ProjectiveLineNormalizer.fourGroup_no_invariant_two A hA hfixed
    (Q.map e.coordinates.toLinearMap) ((e.coordinates.finrank_map_eq Q).trans hQ)
  have hm := Subgroup.map_mono (f := e.quotientIso.toMonoidHom) hN
  rwa [model_stabilizer_image K h e P, model_stabilizer_image K h e Q, hfix] at hm

/-- A marked order-sixteen fixed plane has no invariant ambient subgroup of order four. -/
theorem ambientNormalizer_no_order_four (P Q : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) (hPcard : Nat.card P = 16)
    (hQ : Q ≤ (blockU K).map K.subtype) (hQcard : Nat.card Q = 4)
    (A : Subgroup Atlas.Codes.HexEvenAutomorphisms) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hfix : (ambientSubspace K P).map e.coordinates.toLinearMap =
      fixedSpace Hexacode.evenAction A) :
    ¬ K ⊓ normalizer (P : Set G) ≤ normalizer (Q : Set G) := by
  intro hn
  apply model_no_invariant_two K h e (ambientSubspace K P) (ambientSubspace K Q)
    (ambientSubspace_finrank_four K P hP hPcard)
    (ambientSubspace_finrank_two K Q hQ hQcard) A hA hfix
  intro g hg
  rw [← ambientNormalizer_image K h P hP] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  exact (ambientSubspace_stabilizer K h Q hQ k).mpr (hn hk)

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction

/-- The source commutator line contradicts placement of the marked plane normalizer in Mᵥ. -/
theorem source_line_contradiction [Finite G] {L M V : Subgroup G}
    (s : A5Module.Marking L V) (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) (hPcard : Nat.card P = 16)
    (A : Subgroup Atlas.Codes.HexEvenAutomorphisms) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hfix : (ambientSubspace K P).map e.coordinates.toLinearMap =
      fixedSpace Hexacode.evenAction A)
    (hl : ⁅V, Lv L (A5Module.markedV s)⁆ ≤ (blockU K).map K.subtype)
    (hNP : K ⊓ normalizer (P : Set G) ≤ Mv M (A5Module.markedV s))
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G)) : False := by
  obtain ⟨hd, hi⟩ := source_line_invariant_of_placement K h s P hP hl hNP hML hMV
  exact model_no_invariant_two K h e (ambientSubspace K P)
    (ambientSubspace K ⁅V, Lv L (A5Module.markedV s)⁆)
    (ambientSubspace_finrank_four K P hP hPcard) hd A hA hfix hi

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
