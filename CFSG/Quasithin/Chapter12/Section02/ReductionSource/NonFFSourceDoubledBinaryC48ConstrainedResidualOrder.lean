module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Bridge

/-!
# The original binary-three residual and its star image have no factor five

The original residual modulo its two-core is the marked SL3(2), of order168.
Its full order and every actual star image therefore remain prime to five.
No replacement of the residual by an abstract quotient is made.
Source: Aschbacher--Smith C.4.8 and 12.1.11, pp.154,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual residual and its actual component-star image have no factor five. -/
theorem sourceOrbit_binary_witness_residual_star_five_free
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U) (K : Subgroup H) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let Kg := K.map H.subtype
    let B := (LH.subgroupOf Kg).map (toStarImage Kg (J.pCoreIn 2))
    Nat.Coprime 5 (Nat.card LH) ∧ Nat.Coprime 5 (Nat.card B) := by
  intro LH Kg B
  obtain ⟨_,_,_,_,_,_,e,_,_,_,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  obtain ⟨m,hm⟩ := (pCore_isPGroup (p := 2) (G := LH)).exists_card_eq
  have hcard := card_eq_card_quotient_mul_card_subgroup (pCore 2 LH)
  rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_SL,hm] at hcard
  have hfive : Nat.Coprime 5 (Nat.card LH) := by
    rw [hcard]
    exact (by decide : Nat.Coprime 5 168).mul_right
      ((by decide : Nat.Coprime 5 2).pow_right m)
  refine ⟨hfive,hfive.of_dvd_right ?_⟩
  exact ((LH.subgroupOf Kg).card_map_dvd _).trans
    (LH.card_comap_dvd_of_injective Kg.subtype Kg.subtype_injective)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
