module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.HallCompletion
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.LocalJoinHall
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureEndgame
/-!
# The original A5 contradiction from the actual Hall placement

The weak-closure lower bound and actual Hall upper bound select the natural
SL2(4) marking and force generation parameter two. The completed natural
argument bounds the same parameter by one. The Hall's placement in the
original local join already implies the exact Borel placement required there.

The original chosen-quotient irreducibility, crossed-factor centralization,
point-centralizer control and Hall placement remain the earlier source inputs.
No natural-module, component, block, axis or generation premise is added.
Source: Aschbacher--Smith 10.2.3(4) and 10.2.12--13, pp.746--747,754--755.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance completionOriginalMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
variable {F : Type*} [Field F] [CharP F 2]
local instance completionFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Natural generation uses exactly the original local-join Hall placement. -/
theorem source_natural_generation_le_one_of_hall_placement
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hF : Nat.card F=4) (f : alternatingGroup (Fin 5) ≃* SL(2,F))
    (n : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (f.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) : generationParameter H ≤ 1 :=
  source_natural_generation_le_one_of_hall_borel D e hn ht htn hcross hF f n hi hH B hBM hHall
    (source_a5_hstar_hall_borel_of_localJoin D e hn hH B hBM hHall hBJ)

local instance completionStandardFieldAlgebra :
    Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2

/-- The same actual Hall placement closes the chosen A5 weak-closure branch. -/
theorem source_a5_hall_placement_contradiction
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (hHall : IsHallSubgroup Subgroup.OddHall.oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)))
    (hBJ : B.map H.subtype ≤ localJoin T L) : False := by
  obtain ⟨_,hgen,f,⟨n⟩⟩ := source_a5_natural_and_parameters_eq_two_of_hall_placement
    D e hi hn ht htn hcross hcent hH B hBM hHall hBJ
  have hb := source_natural_generation_le_one_of_hall_placement D e hn ht htn hcross
    (show Nat.card (OrthogonalFourMinus.FiniteModel.Field 1)=4 from GaloisField.card 2 2 (by decide))
    f n hi hH B hBM hHall hBJ
  omega
end CFSG.Quasithin.Chapter10
