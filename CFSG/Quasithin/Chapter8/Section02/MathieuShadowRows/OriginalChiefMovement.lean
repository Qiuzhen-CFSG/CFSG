module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.OriginalChiefFixedSpaces

public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CubicMovement

/-!
# Cubic movement in the original chief fixed spaces

The canonical injection of each original seed section intertwines every
original normalizer element. Its displacement consequently embeds in the
displacement of the same chief action restricted to the fixed space of any
subgroup centralizing the seed. Six dimensions of movement distributed over
two noncentral chief factors force at least three on one of those fixed
spaces. The whole fixed space may also have passive coordinates.
Source: Aschbacher--Smith, 3.1.9(6), printed p.578, refs/quasithin.pdf.
The original Thompson application is M22CodeCubicMovement in Chapter12.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD ChapterE
open MathieuCode.NormalizedShadowRows.CubicFiltration
section
variable {G : Type*} [Group G] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  (s : SeriesOn ((conjugateSpan H V).subgroupOf H)) (i : Fin s.series.length)

set_option backward.isDefEq.respectTransparency false

/-- The injection retains the action of every original element normalizing the seed. -/
theorem seedChiefInjection_equivariant (b : seedNormalizer H V) (v) :
    seedChiefInjection H V s i (originalSeedFactor H V s i b v) =
      s.factorRepresentation i (b : H) (seedChiefInjection H V s i v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
    change s.factorProjection i
      ((s.linearTerm i.succ).toRepresentation (b : H) ⟨w.val.val,w.property⟩) =
        s.factorRepresentation i (b : H) (s.factorProjection i ⟨w.val.val,w.property⟩)
    rw [← s.factorLinearEquiv_mk, ← s.factorLinearEquiv_mk,
      ← s.factorLinearEquiv_equivariant]
    rfl

variable [Finite G]

/-- The cubic only moves the part of the chief fixed space lying in its active coordinate.
This bound retains passive coordinates, which may make the whole fixed space larger. -/
theorem originalSeedFactor_codim_le_fixed_movement (A : Subgroup H)
    (hA : A.map H.subtype ≤ centralizer (V : Set G)) (b : seedNormalizer H V) :
    fixedCodim (originalSeedFactor H V s i) (zpowers b) ≤
      Module.finrank (ZMod 2) (LinearMap.range
        ((s.factorRepresentation i (b : H) - LinearMap.id).domRestrict
          (fixedSpace (s.factorRepresentation i) A))) := by
  exact MathieuCode.NormalizedShadowRows.CubicMovement.fixedCodim_le_range_on_subspace
    (originalSeedFactor H V s i) (s.factorRepresentation i) b (b : H)
    (seedChiefInjection H V s i) (seedChiefInjection_injective H V s i)
    (seedChiefInjection_equivariant H V s i b)
    (fixedSpace (s.factorRepresentation i) A) (seedChiefInjection_fixed H V s i A hA)

end

section
variable {G X : Type*} [Group G] [Finite G] [Group X] (H V : Subgroup G)
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  [IsElementaryAbelian 2 V]
set_option backward.isDefEq.respectTransparency false

/-- The same cubic and all its covering maps, with a large original chief displacement. -/
def CubicFixedMovement (A B : Subgroup H) (q : H →* X) : Prop :=
    ∃ b : B,
      orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (b : H)) = 3 ∧
      orderOf (q (b : H)) = 3 ∧
      ∃ hn : ((b : H) : G) ∈ normalizer (V : Set G),
        orderOf (V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩) = 3 ∧
        ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H),
          ∃ i : Fin s.series.length, ¬ s.Central i ∧
            3 ≤ fixedCodim (originalSeedFactor H V s i) (zpowers ⟨(b : H),hn⟩) ∧
            3 ≤ Module.finrank (ZMod 2) (LinearMap.range
                ((s.factorRepresentation i (b : H) - LinearMap.id).domRestrict
                  (fixedSpace (s.factorRepresentation i) A)))

/-- The same cubic forces movement of dimension at least three in the original
chief fixed space of every subgroup centralizing the seed. -/
theorem cubic_large_fixed_movement (hVH : V ≤ H)
    (A : Subgroup H) (hA : A.map H.subtype ≤ centralizer (V : Set G))
    (B : Subgroup H) (q : H →* X) (hcub : CubicOrbitChiefs (V := V) B q)
    (htwo : ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H), s.noncentralCount = 2) :
    CubicFixedMovement H V A B q := by
  obtain ⟨b,hb,hqb,hn,hz,hc,_⟩ := hcub
  refine ⟨b,hb,hqb,hn,hz,?_⟩
  intro s
  obtain ⟨i,hi,hlarge⟩ := exists_large_originalSeedFactor H V hVH (b : H) hn hb hz hc s (htwo s)
  exact ⟨i,hi,hlarge,hlarge.trans
    (originalSeedFactor_codim_le_fixed_movement H V s i A hA ⟨(b : H),hn⟩)⟩
end
end CFSG.Quasithin.Chapter8.MathieuShadowRows
