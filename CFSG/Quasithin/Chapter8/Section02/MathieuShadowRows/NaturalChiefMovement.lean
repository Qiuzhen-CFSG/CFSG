module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.OriginalChiefMovement
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialChiefActor
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.NaturalMovement

/-!
# Natural movement bounds on the literal original chief factors

The common action-image equivalence transports the original sharp actor's
rank lower bound to every noncentral chief factor. Its rank and fixed
codimension agree, so a three-dimensional moving seed section forces its
ambient chief factor to have dimension at least five.

The native single and paired natural-coordinate calculations apply through
the canonical injection of the original seed section. For a field-four
component element they bound that section's cubic displacement by two,
contradicting displacement at least three. The constructor retains the
original cubic, all original quotient maps and the original Thompson actor;
it proves an obstruction to such coordinates without assuming them. Their
construction from the chief classification remains to be discharged by the
same source argument.

Source: Aschbacher--Smith, proof of 3.1.9(6), printed p.578,
refs/quasithin.pdf. The actual Chapter12 application is
NonFFSourceMathieuShadowRows/M22CodeNaturalObstruction.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterD ChapterE
variable {G : Type*} [Group G] [Finite G] {H V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {S : Sylow 2 H} {hVH : V ≤ H}

omit [Finite G] in
set_option backward.isDefEq.respectTransparency false in
/-- The original actor retains rank at least two on every noncentral chief factor. -/
theorem EssentialChiefActor.chief_rank_ge_two
    (a : EssentialSeedAction H V S hVH) {A : Subgroup H} (ha : EssentialChiefActor a A)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    2 ≤ rank (actionSubgroup (s.factorRepresentation i) A) := by
  obtain ⟨e⟩ := (ha.chief s i hi).2
  have hr := rank_map_injective e.equiv.toMonoidHom e.equiv.injective
    (actionSubgroup a.representation A)
  rw [e.map_subgroup A] at hr
  rw [hr]
  exact ha.large

set_option backward.isDefEq.respectTransparency false in
/-- Sharpness leaves two dimensions beyond the induced seed displacement. -/
theorem originalSeedFactor_codim_add_two_le_finrank
    (a : EssentialSeedAction H V S hVH) {A : Subgroup H} (ha : EssentialChiefActor a A)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) (b : seedNormalizer H V) :
    fixedCodim (originalSeedFactor H V s i) (zpowers b) + 2 ≤
      Module.finrank (ZMod 2) (Additive (s.Factor i)) := by
  have hl := originalSeedFactor_codim_le_fixed H V s i A ha.centralizes b
  have hc := fixedCodim_add_finrank (s.factorRepresentation i) A
  have hs := ha.chief_sharp s i hi
  rw [fixedCodim_actionSubgroup] at hs
  have hr := ha.chief_rank_ge_two a s i hi
  omega

section Natural
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
open MathieuCode.NormalizedShadowRows.NaturalMovement

/-- The actual seed-section injection transports the component movement bound,
with the original centralizing actor, normalizer element and chief factor. -/
theorem originalSeedFactor_codim_le_two_of_natural_coordinates
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (A : Subgroup H)
    (hA : A.map H.subtype ≤ centralizer (V : Set G)) (b : seedNormalizer H V)
    (hF : Nat.card F = 4)
    (hcoord : HasComponentCoordinates (F := F) (s.factorRepresentation i) A (b : H)) :
    fixedCodim (originalSeedFactor H V s i) (zpowers b) ≤ 2 := by
  have hb := component_coordinates_movement_le (s.factorRepresentation i) A (b : H) hcoord
  rw [field_four_finrank hF] at hb
  exact (originalSeedFactor_codim_le_fixed_movement H V s i A hA b).trans hb

/-- A large induced section rules out those same natural component coordinates.
This is the two-versus-three contradiction; construction of the matching
coordinates from the source chief classification remains a separate obligation. -/
theorem originalSeedFactor_not_natural_coordinates_of_three_le
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (A : Subgroup H)
    (hA : A.map H.subtype ≤ centralizer (V : Set G)) (b : seedNormalizer H V)
    (hF : Nat.card F = 4)
    (hl : 3 ≤ fixedCodim (originalSeedFactor H V s i) (zpowers b)) :
    ¬ HasComponentCoordinates (F := F) (s.factorRepresentation i) A (b : H) := by
  intro hc
  have hu := originalSeedFactor_codim_le_two_of_natural_coordinates s i A hA b hF hc
  omega
end Natural

section Obstruction
variable {X F : Type*} [Group X] [Field F] [Finite F] [Algebra (ZMod 2) F]
  [IsElementaryAbelian 2 V]
open MathieuCode.NormalizedShadowRows.NaturalMovement

/-- The original cubic and full covering maps, with a chief section that
cannot have the field-four component coordinates required by the source. -/
@[expose] def CubicNaturalObstruction (J B : Subgroup H) (q : H →* X) : Prop :=
  ∃ b : B,
    orderOf (actionHom (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (b : H)) = 3 ∧
    orderOf (q (b : H)) = 3 ∧
    ∃ hn : ((b : H) : G) ∈ normalizer (V : Set G),
      orderOf (V.normalizerMonoidHom.rangeRestrict ⟨((b : H) : G),hn⟩) = 3 ∧
      ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H),
        ∃ i : Fin s.series.length, ¬ s.Central i ∧
          3 ≤ fixedCodim (originalSeedFactor H V s i) (zpowers ⟨(b : H),hn⟩) ∧
          5 ≤ Module.finrank (ZMod 2) (Additive (s.Factor i)) ∧
          ¬ HasComponentCoordinates (F := F) (s.factorRepresentation i) J (b : H)

set_option backward.isDefEq.respectTransparency false in
/-- The literal cubic filtration and the sharp source actor produce the
large-dimensional obstruction on the original chief series. -/
theorem cubic_natural_obstruction
    (a : EssentialSeedAction H V S hVH) {A : Subgroup H} (ha : EssentialChiefActor a A)
    (J : Subgroup H) (hJ : J.map H.subtype ≤ centralizer (V : Set G))
    (B : Subgroup H) (q : H →* X) (hcub : CubicOrbitChiefs (V := V) B q)
    (htwo : ∀ s : SeriesOn ((conjugateSpan H V).subgroupOf H), s.noncentralCount = 2)
    (hF : Nat.card F = 4) :
    CubicNaturalObstruction (V := V) (F := F) J B q := by
  obtain ⟨b,hb,hqb,hn,hz,hlarge⟩ :=
    cubic_large_fixed_movement H V hVH J hJ B q hcub htwo
  refine ⟨b,hb,hqb,hn,hz,?_⟩
  intro s
  obtain ⟨i,hi,hl,_⟩ := hlarge s
  refine ⟨i,hi,hl,?_,?_⟩
  · have hd := originalSeedFactor_codim_add_two_le_finrank a ha s i hi ⟨(b : H),hn⟩
    omega
  · exact originalSeedFactor_not_natural_coordinates_of_three_le s i J hJ ⟨(b : H),hn⟩ hF hl
end Obstruction

end CFSG.Quasithin.Chapter8.MathieuShadowRows
