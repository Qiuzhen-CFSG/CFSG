module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SmallAlternatingExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SymplecticExclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.G2Exclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.BinaryFiveExclusion

/-!
# Only A₇ survives in the literal fixed-component star quotient

A proper Sylow overgroup in every binary SL₂ is solvable, contradicting the
actual perfect A₅ residual. Together with the linear, symplectic, G₂,
small alternating and central-cover exclusions, this eliminates every row
of the proved full B.5.1 group catalogue except A₇. The equivalence is on
Lᵤ* itself. No geometric alternative or block recognition is an input.

Source: Aschbacher--Smith C.2.7, displayed (!), p.146, specialized to
the original fixed-centralizer argument in 14.7.68(2), pp.1071--1072.
The original block-module reconstruction remains with this source family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_C27_linearTwo_row_impossible
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    (k : ChapterB.QuasisimpleSource.BinaryField)
    (e : starImage Lu (d.fixedCore u) Lu ≃* SL(2,k.Carrier)) : False := by
  let A := starImage Lu (d.fixedCore u) Lu
  let M := starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)
  obtain ⟨S,hS⟩ := d.fixedStarM_contains_sylow u h
  have hs : ChapterF.Source.RankOneSylowFacts S :=
    ChapterF.Source.rankOneSylowFacts_of_equiv S e
      (ChapterF.Source.Linear.all_sylows _
        (ChapterF.Source.Linear.standard_facts k.Carrier k.degree k.degree_pos k.card_eq) _)
  have hM : M.subgroupOf A < ⊤ := lt_top_iff_ne_top.mpr
    (ChapterC.C27Source.starM_subgroupOf_ne_top
      (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
        d.point_mem_U_commutator_K))
  have hMN := hs.unique_maximal (M.subgroupOf A) hS hM
  let : Group.IsSolvable (normalizer (S : Set A)) := hs.solvable
  let : Group.IsSolvable (M.subgroupOf A) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hMN)
  let : Group.IsSolvable M := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe (starM_le Lu (d.fixedCore u)
      (F.H ⊓ d.fixedCentralizer u))).toMonoidHom)
    (subgroupOfEquivOfLe (starM_le _ _ _)).surjective
  exact (d.fixedStarM_hasA5TwoResidual_of_source u h).not_isSolvable

theorem fixedComponent_C27_star_alternatingSeven
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Nonempty (starImage Lu (d.fixedCore u) Lu ≃* alternatingGroup (Fin 7)) := by
  have hm := ChapterC.C27Source.star_model_from_source
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)
  cases hm with
  | linearTwo k e => exact (d.fixedComponent_C27_linearTwo_row_impossible u h k e).elim
  | linearThree k e => exact (d.fixedComponent_C27_linearThree_row_impossible u h k.Carrier e).elim
  | symplectic k hk e =>
    have hk4 : 4 ≤ Nat.card k.Carrier := by
      rw [k.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k.degree)
    exact (d.fixedComponent_C27_symplectic_row_impossible u h e hk4).elim
  | g2 k hk e =>
    have hk4 : 4 ≤ Nat.card k.Carrier := by
      rw [k.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k.degree)
    exact (d.fixedComponent_C27_g2_large_row_impossible u h k.Carrier hk4 e).elim
  | g2DerivedTwo e => exact (d.fixedComponent_C27_g2_derived_row_impossible u h (ZMod 2) e).elim
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact (d.fixedComponent_C27_alternatingFive_row_impossible u h e).elim
    · exact (d.fixedComponent_C27_alternatingSix_row_impossible u h e).elim
    · exact ⟨e⟩
    · exact (d.fixedComponent_C27_alternatingEight_row_impossible u h e).elim
  | linearFiveTwo e => exact (d.fixedComponent_C27_binaryFive_row_impossible u h e).elim
  | tripleSix _ e => exact (d.fixedComponent_C27_tripleSix_row_impossible u h e).elim

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
