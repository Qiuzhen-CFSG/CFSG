module

public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.FixedGeneration
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.CorankSpan

/-!
# The native M22 cocode spans on the original marked orbit

An injective marking of the full automizer transports four-subgroup fixed
spaces and element-fixed spans. The full-kernel lifts then identify their
ambient images with the exact corank-five offender span. Rank-five actors
give the whole original module; rank-four actors contained in native M22 give
corank at most one. The outer actor and the original module are retained.

These discharge the rank-five and inner rank-four fixed-span premises in the
M22 cocode argument of original 8.1.3. Source: Aschbacher--Smith,
printed pp.713--714, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender MathieuCode
open MathieuCode.M22Quintet
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterE Chapter7 MathieuCode.NormalizedShadowRows
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Source 8.1.3's rank-five span on the original orbit, using the exact
full-automizer marking and the full-kernel lifts of the corank-five family. -/
theorem marked_rank_five_span {T : Subgroup G} {g : G} (h : IsWOffenderAt V T g)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] M22Cocode)
    (hE : ∀ b v, E (automizerRepresentation V b v) = m22OuterCocodeRepresentation (a b) (E v))
    (hfive : rank (inducedAutomizer V (offenderNormalizer V g)) = 5)
    (hwpos : 1 ≤ (globalW V T).toNat) (hw : (globalW V T).toNat ≤ 2) :
    offenderCentralizerSpan V g 5 = V := by
  let I := inducedAutomizer V (offenderNormalizer V g)
  let := offender_inducedAutomizer_elementary V g
  let : IsElementaryAbelian 2 (I.map a) := IsElementaryAbelian.map a
  have hr : rank (I.map a) = 5 := (rank_map_injective a ha I).trans hfive
  have ht := fourFixedSpan_map_equivariant (automizerRepresentation V)
    m22OuterCocodeRepresentation a ha E hE I
  rw [rank_five_fourFixedSpan_eq_top (I.map a) hr] at ht
  have htop : fourFixedSpan (automizerRepresentation V) I = ⊤ := by
    apply Submodule.map_injective_of_injective E.injective
    rw [ht,Submodule.map_top,LinearMap.range_eq_top.mpr E.surjective]
  have hh := fourFixedSpan_le_offenderCentralizerSpan h hfive hwpos hw
  change ambientSubmodule V (fourFixedSpan (automizerRepresentation V) I) ≤ _ at hh
  rw [htop,ambientSubmodule,(moduleSubgroup V).map_top,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
  exact le_antisymm (offenderCentralizerSpan_le V g 5) hh

/-- At rank four, an inner actor gives the literal source corank at most one. -/
theorem marked_inner_rank_four_span {T : Subgroup G} {g : G} (h : IsWOffenderAt V T g)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] M22Cocode)
    (hE : ∀ b v, E (automizerRepresentation V b v) = m22OuterCocodeRepresentation (a b) (E v))
    (hfour : rank (inducedAutomizer V (offenderNormalizer V g)) = 4)
    (hw : (globalW V T).toNat = 2)
    (hi : (inducedAutomizer V (offenderNormalizer V g)).map a ≤ m22ToPairStabilizer.range) :
    subgroupCorank V (offenderCentralizerSpan V g 5) ≤ 1 := by
  let I := inducedAutomizer V (offenderNormalizer V g)
  let := offender_inducedAutomizer_elementary V g
  let : IsElementaryAbelian 2 (I.map a) := IsElementaryAbelian.map a
  have hr : rank (I.map a) = 4 := (rank_map_injective a ha I).trans hfour
  rw [rank_four_offenderCentralizerSpan_eq h hfour hw,offenderFixedSpan_corank]
  rw [fixedSpaceSpan_codim_map_equivariant (automizerRepresentation V)
    m22OuterCocodeRepresentation a ha E hE]
  exact outer_rank_four_fixedSpan_codim_of_inner (I.map a) hr hi
end CFSG.Quasithin.Chapter8.MathieuShadowRows
