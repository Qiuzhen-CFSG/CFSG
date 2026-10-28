module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Marker

/-!+# The original extraspecial marking and central preimage

The marking is a noncentral cubic subgroup of the actual extraspecial
two-residual. Its fixed space, pointwise stabilizer and Sylow intersection
are kept in that same faithful action image. `ImageMarking` is an explicit
intermediate contract, whose existence still requires the source selection.
It assumes no ambient component or odd-core conclusion.

The central preimage is the literal X₀ in Aschbacher--Smith 15.1.24,
printed p.1101. The requested residual of R ∨ X₀ contains the printed
X₁ = O²(⟨R^{X₀}⟩), whose exponent is easily lost in text extraction.
The marked plane is the fixed subgroup from Notation 15.1.16(c), p.1092.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The full ambient preimage of the embedded residual center. -/
noncomputable def centralPreimage (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) : Subgroup G :=
  let P := pResidual 2 (internalActionImage M V hn)
  (((center P).map P.subtype).comap (actionHom M V hn).rangeRestrict).map M.subtype

/-- The requested residual of R ∨ X₀, before taking any component. -/
noncomputable def centralLiftResidual (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) : Subgroup G :=
  let H := (M ⊓ Mc).pCoreIn 2 ⊔ centralPreimage M V hn
  (pResidual 2 H).map H.subtype

/-- The literal printed X₁: the residual of the span of X₀-conjugates of R. -/
noncomputable def sourceCentralLiftResidual (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) : Subgroup G :=
  let H := conjugateSpanBy ((M ⊓ Mc).pCoreIn 2) (centralPreimage M V hn)
  (pResidual 2 H).map H.subtype

omit [Finite G] in
/-- A cubic lift in the exact source subgroup meets the requested containment. -/
theorem sourceCentralLiftResidual_le (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) :
    sourceCentralLiftResidual M Mc V hn ≤ centralLiftResidual M Mc V hn := by
  apply embedded_pResidual_mono 2
  apply conjugateSpanBy_le le_sup_left
  exact le_sup_right.trans ((M ⊓ Mc).pCoreIn 2 ⊔ centralPreimage M V hn).le_normalizer

/-- The fixed subgroup of the prescribed cubic subgroup in the original V. -/
noncomputable def fixedSubgroup (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (X : Subgroup (pResidual 2 (internalActionImage M V hn))) : Subgroup G :=
  (binarySubgroup (fixedSpace (imageRepresentation M V hn)
    (X.map (pResidual 2 (internalActionImage M V hn)).subtype))).map V.subtype

/-- Finite-image selection inputs. The residual identity identifies the
actual centralizer residual, rather than just its abstract isomorphism type. -/
structure ImageMarking (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) where
  X : Subgroup (pResidual 2 (internalActionImage M V hn))
  card_X : Nat.card X = 3
  noncentral : X ≠ center (pResidual 2 (internalActionImage M V hn))
  fixed_thompson : fixedSpace (imageRepresentation M V hn)
      (X.map (pResidual 2 (internalActionImage M V hn)).subtype) ≤
    fixedSpace (imageRepresentation M V hn)
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
  generates :
    let W := fixedSpace (imageRepresentation M V hn)
      (X.map (pResidual 2 (internalActionImage M V hn)).subtype)
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    K ⊔ ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict = ⊤
  sylow :
    let W := fixedSpace (imageRepresentation M V hn)
      (X.map (pResidual 2 (internalActionImage M V hn)).subtype)
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    ∃ Q : Sylow 2 K, (Q : Subgroup K).map K.subtype =
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict) ⊓ K
  sylow_normal :
    let W := fixedSpace (imageRepresentation M V hn)
      (X.map (pResidual 2 (internalActionImage M V hn)).subtype)
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let S := ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict
    ((S ⊓ K).subgroupOf S).Normal
  residual :
    let W := fixedSpace (imageRepresentation M V hn)
      (X.map (pResidual 2 (internalActionImage M V hn)).subtype)
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    (pResidual 2 K).map K.subtype =
      X.map (pResidual 2 (internalActionImage M V hn)).subtype

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
