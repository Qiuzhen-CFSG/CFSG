module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.A6Exclusion

/-!
# The literal marked triple-cover model

The marked subgroup is the two-residual of a binary point stabilizer in
the concrete hexacode triple cover. Its quotient by its own two-core has
two distinguished prospective cubic directions: the image of the cover's
center and the image of the point stabilizer's derived subgroup. These
are subgroup constructions; their orders, complementarity, and automizer
actions require proofs and are not included in the definitions.

The source module marking retains both the quotient equivalence and the
actual conjugation action on the four-dimensional binary module. It is
the triple-cover counterpart of `SimplePointModel`.

Source: Aschbacher–Smith, Notation 13.2.1 and Lemma 13.2.2, pp.877–878,
used in 13.8.16(1), p.952 (PDF p.969).
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymmetricSix

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

variable {G : Type*} [Group G]

/-- A compatible triple-cover quotient and the source's marked binary action. -/
structure CoverPointModel (L V : Subgroup G) (hLV : L ≤ normalizer (V : Set G)) where
  quotientEquiv : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms
  moduleEquiv : V ≃* Multiplicative NaturalModule
  equivariant : ∀ (l : L) (v : V),
    Multiplicative.toAdd (moduleEquiv (V.normalizerMonoidHom (inclusion hLV l) v)) =
      polarAction (Atlas.Codes.hexEvenCoordinate
        (quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))).val
        (Multiplicative.toAdd (moduleEquiv v))

/-- Ambient normalizers act on the concrete cover through their literal
conjugation action on L/O₂(L). No lift to the full hexacode group is assumed. -/
noncomputable def coverAction {L V : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}
    (d : CoverPointModel L V hLV) (M : Subgroup G)
    (hM : M ≤ normalizer (L : Set G)) : M →* MulAut Atlas.Codes.HexEvenAutomorphisms :=
  (MulAut.congr d.quotientEquiv).toMonoidHom.comp (quotientAction L M hM)

/-- The same exclusion retains the compatible module marking when it is
supplied in both branches of the earlier source alternative. -/
theorem coverPointModel_of_marked_rank [Finite G] (L T V V₁ : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G))
    (hmodels : Nonempty (SimplePointModel L V hLV) ∨ Nonempty (CoverPointModel L V hLV))
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (L : Set G))
    (hV₁V : V₁ ≤ V) (hV₁ : Nat.card V₁ = 2)
    (hrank : primeRank 3 (markedResidual L T V₁) = 2) :
    Nonempty (CoverPointModel L V hLV) := by
  rcases hmodels with hs | hc
  · obtain ⟨d⟩ := hs
    have h := simple_residual_rank L T V V₁ hLV d
      (markedResidual_le_left L T V₁ hT hn) hV₁V hV₁
    omega
  · exact hc

namespace Model

abbrev Cover := Atlas.Codes.HexEvenAutomorphisms
abbrev C3 := Multiplicative (ZMod 3)
abbrev CubicPlane := C3 × C3

/-- The preimage of the actual binary point stabilizer in A₆. -/
noncomputable def parabolic (x : BinaryPoint) : Subgroup Cover :=
  (MulAction.stabilizer A6 x).comap Atlas.Codes.hexEvenCoordinate

/-- The embedded two-residual of that parabolic. -/
noncomputable def residual (x : BinaryPoint) : Subgroup Cover :=
  (pResidual 2 (parabolic x)).map (parabolic x).subtype

/-- The literal quotient whose automizer must be calculated. -/
abbrev Section (x : BinaryPoint) := residual x ⧸ pCore 2 (residual x)

/-- The center's image in the marked section. -/
noncomputable def scalarLine (x : BinaryPoint) : Subgroup (Section x) :=
  ((center Cover).subgroupOf (residual x)).map (QuotientGroup.mk' (pCore 2 (residual x)))

/-- The image of the parabolic's derived subgroup in the marked section. -/
noncomputable def derivedLine (x : BinaryPoint) : Subgroup (Section x) :=
  (((commutator (parabolic x)).map (parabolic x).subtype).subgroupOf (residual x)).map
    (QuotientGroup.mk' (pCore 2 (residual x)))

/-- The first and second axes of the concrete elementary group of order nine. -/
def scalarAxis : Subgroup CubicPlane := (⊤ : Subgroup C3).prod ⊥
def derivedAxis : Subgroup CubicPlane := (⊥ : Subgroup C3).prod ⊤

/-- Restriction of an actual cover automorphism preserving the residual. -/
noncomputable def residualAut (x : BinaryPoint) (a : MulAut Cover)
    (ha : (residual x).map a.toMonoidHom = residual x) : MulAut (residual x) :=
  (a.subgroupMap (residual x)).trans (MulEquiv.subgroupCongr ha)

/-- Its induced action on the intrinsic two-core quotient. -/
noncomputable def sectionAut (x : BinaryPoint) (a : MulAut Cover)
    (ha : (residual x).map a.toMonoidHom = residual x) : MulAut (Section x) :=
  quotientAut (pCore 2 (residual x)) (residualAut x a ha)

/-- The restriction has the original automorphism as its underlying map. -/
theorem residualAut_coe (x : BinaryPoint) (a : MulAut Cover)
    (ha : (residual x).map a.toMonoidHom = residual x) (r : residual x) :
    (residualAut x a ha r : Cover) = a r := rfl

/-- Quotient representatives retain the original cover automorphism. -/
theorem sectionAut_mk (x : BinaryPoint) (a : MulAut Cover)
    (ha : (residual x).map a.toMonoidHom = residual x) (r : residual x) :
    sectionAut x a ha (QuotientGroup.mk' (pCore 2 (residual x)) r) =
      QuotientGroup.mk' (pCore 2 (residual x)) (residualAut x a ha r) :=
  quotientAut_apply_mk _ _ _

end Model
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

end
