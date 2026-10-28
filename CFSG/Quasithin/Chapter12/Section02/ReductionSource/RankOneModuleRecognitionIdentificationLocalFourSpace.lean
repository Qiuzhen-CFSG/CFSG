module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFourSpace
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalAction

/-!
# The actual binary three-space and elementary sixteen in the contrary branch

The chosen Chapter 12 module discharges the source plane-normalizer premise.
The genuine G.3 and G.6 arguments then identify the faithful action on the
literal U/⟨z⟩ as GL₃(2), with the original layer image equal to the radical
of Z_S/⟨z⟩. This also constructs the natural-module isomorphisms, proves
U elementary abelian of order sixteen, and identifies C_H(U/⟨z⟩) with C_H(U).

The order-four intersection is a contrary case, not an added final premise.
The ambient L₂(4)-block and A₇ contradiction, the graph exclusion in 6.2.8,
and final discharge of 6.1.5 remain with the local-analysis assembly owner.
No LocalAnalysis or later identification is used to prove these results.

Source: Aschbacher--Smith, 6.2.11, printed pp.685--686, applied to
[R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ} {z : G}

/-- The marked full action and literal common-center four-group in 6.2.11. -/
theorem source_local_four_intersection_three_space
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    letI := (LocalQuotientAction.reduced_space h611 hnatural hz ho hT).elementary
    let f := LocalQuotientAction.linearAction (T : Subgroup G) L (wholeReduced T L) z
    f.range = ⊤ ∧
      Module.finrank (ZMod 2) (Additive (LocalQuotientAction.space (T : Subgroup G) L (wholeReduced T L) z)) = 3 ∧
      (LocalQuotientAction.layerImage (P := T) (L := L) (R := wholeReduced T L) (z := z)).map f.range.subtype =
        BinaryLinear.radical (LocalQuotientAction.seedSubspace (T : Subgroup G) L (wholeReduced T L) z) :=
  LocalQuotientAction.four_image_three_space h611 hnatural hz ho hT
    (source_local_layer_normalizers D h h611 hnatural).1 hcard

/-- The actual GL₃(2) actor isomorphism and intertwining natural-module map. -/
theorem source_local_four_intersection_natural_three
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    letI := (LocalQuotientAction.reduced_space h611 hnatural hz ho hT).elementary
    ChapterG.Section06.HasModelOn
      (LocalQuotientAction.representation (T : Subgroup G) L (wholeReduced T L) z) ⊤ ⊤
      (ChapterG.Section06.binaryLinearAction 3) :=
  LocalQuotientAction.four_image_natural_three h611 hnatural hz ho hT
    (source_local_layer_normalizers D h h611 hnatural).1 hcard

/-- The original elementary four-space and the earlier kernel comparison,
with no 6.2.12 kernel equality or LocalAnalysis premise. -/
theorem source_local_four_intersection_four_space
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (ho : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcard : Nat.card (commutatorLayer T L ⊓ (centralizer ({z} : Set G)).pCoreIn 2 : Subgroup G) = 4) :
    Nat.card (sourceClosure (T : Subgroup G) L (wholeReduced T L) z) = 16 ∧
      IsElementaryAbelian 2 (sourceClosure (T : Subgroup G) L (wholeReduced T L) z) ∧
      LocalQuotientAction.kernel (T : Subgroup G) L (wholeReduced T L) z =
        centralizer ({z} : Set G) ⊓
          centralizer (sourceClosure (T : Subgroup G) L (wholeReduced T L) z : Set G) := by
  have hp := (source_local_layer_normalizers D h h611 hnatural).1
  exact ⟨LocalQuotientAction.four_closure_card h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_closure_elementary h611 hnatural hz ho hT hp hcard,
    LocalQuotientAction.four_kernel_eq_centralizer h611 hnatural hz ho hT hp hcard⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
