module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenOffenders
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SplitMovedCard
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# The natural six-space in the original fixed-component star action

Apply the proved full B.5 theorem to the actual star module. The fixed
Sylow and perfect A₅ residual exclude every model except the seven-letter
natural and exceptional rows. The outer best offender excludes the latter.
The natural row splits by the proved odd-permutation cohomology theorem.
Consequently the original subgroup [Ω₁Z(O₂(LᵤRᵤ)),Lᵤ] has order 64,
with the marked natural action retained on its literal moved section.

No block or shortness hypothesis enters this recognition. Reconstruction
of the whole core commutator remains separate; SevenShort applies the
order calculation to the actual Rudvalis/D consumers once shortness holds.
Source: Aschbacher--Smith B.5.1, C.2.7 and 14.7.68(2), pp.99--103,
145--147 and1071--1072.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Nonquasisimple
structure SevenNaturalAction (d : Data T L V F W) (u : F.U) (Lu : Subgroup G) where
  contained : starImage Lu (d.fixedCore u) Lu ≤ offenderSubgroup (starRepresentation Lu (d.fixedCore u))
  sectionData : MovedSection
    ((starRepresentation Lu (d.fixedCore u)).comp (offenderSubgroup (starRepresentation Lu (d.fixedCore u))).subtype)
    ((starImage Lu (d.fixedCore u) Lu).subgroupOf (offenderSubgroup (starRepresentation Lu (d.fixedCore u))))
  splitting : IsCompl sectionData.space.toSubmodule
    (fixedSpace ((starRepresentation Lu (d.fixedCore u)).comp
      (offenderSubgroup (starRepresentation Lu (d.fixedCore u))).subtype)
      ((starImage Lu (d.fixedCore u) Lu).subgroupOf
        (offenderSubgroup (starRepresentation Lu (d.fixedCore u)))))
  natural : MarkedActionEquiv sectionData.action (offenderSubgroup sectionData.action)
    ((starImage Lu (d.fixedCore u) Lu).subgroupOf (offenderSubgroup (starRepresentation Lu (d.fixedCore u))))
    (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7))
  ratio : quadraticRatio sectionData.action = 1
end Nonquasisimple

namespace Data
variable (d : Data T L V F W)

private def binarySymplecticSix :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private theorem fixed_binary_linear_false
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : starImage Lu (d.fixedCore u) Lu ≃* SL(n,ZMod 2)) : False := by
  rcases hn with rfl | rfl
  · exact d.fixedComponent_C27_alternatingEight_row_impossible u h
      (e.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm))
  · exact d.fixedComponent_C27_binaryFive_row_impossible u h e

theorem fixedComponent_C27_natural_moved
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Nonempty (Nonquasisimple.SevenNaturalAction d u Lu) := by
  obtain ⟨hCJ,⟨c⟩⟩ := ChapterC.C27Source.star_moved_section_from_source
    (d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
      d.point_mem_U_commutator_K)
  let e := (subgroupOfEquivOfLe hCJ).symm
  cases c.clause_one with
  | doubleThree k _ a _ _ =>
    exact (d.fixedComponent_C27_linearThree_row_impossible u h k.Carrier
      (e.trans a.groupEquiv)).elim
  | naturalDual n hn _ ha =>
    obtain ⟨a⟩ := ha
    exact (d.fixed_binary_linear_false u h hn (e.trans a.groupEquiv)).elim
  | repeatedNatural n r hn _ _ _ ha =>
    obtain ⟨a⟩ := ha
    exact (d.fixed_binary_linear_false u h hn (e.trans a.groupEquiv)).elim
  | irreducible hi hf hirr source hext =>
    cases source with
    | linearTwo k _ a _ _ =>
      exact (d.fixedComponent_C27_linearTwo_row_impossible u h k (e.trans a.groupEquiv)).elim
    | linearThree k _ a _ =>
      exact (d.fixedComponent_C27_linearThree_row_impossible u h k.Carrier
        (e.trans a.groupEquiv)).elim
    | symplectic k hk _ a _ =>
      have hc : 4 ≤ Nat.card k.Carrier := by
        rw [k.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k.degree)
      exact (d.fixedComponent_C27_symplectic_row_impossible u h (e.trans a.groupEquiv) hc).elim
    | symplecticTwo a _ =>
      exact (d.fixedComponent_C27_alternatingSix_row_impossible u h
        (e.trans (a.subgroupEquiv.trans binarySymplecticSix))).elim
    | g2 k hk _ a _ _ =>
      have hc : 4 ≤ Nat.card k.Carrier := by
        rw [k.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k.degree)
      exact (d.fixedComponent_C27_g2_large_row_impossible u h k.Carrier hc
        (e.trans a.groupEquiv)).elim
    | g2Two a _ _ =>
      exact (d.fixedComponent_C27_g2_derived_row_impossible u h (ZMod 2)
        (e.trans a.subgroupEquiv)).elim
    | symmetric n hn a _ ratio =>
      rcases hn with rfl | rfl
      · exact (d.fixedComponent_C27_alternatingFive_row_impossible u h
          (e.trans a.subgroupEquiv)).elim
      · exact ⟨⟨hCJ,c.sectionData,
          ExtensionConsequences.symmetricOdd_isCompl c.sectionData hi (Or.inr rfl) a,
          a,ratio⟩⟩
    | alternatingSix _ a _ _ =>
      exact (d.fixedComponent_C27_alternatingSix_row_impossible u h (e.trans a.groupEquiv)).elim
    | alternatingSeven _ whole _ _ _ _ =>
      exact (d.fixedComponent_C27_offender_not_le_component u h
        (subgroupOf_eq_top.mp whole)).elim
    | tripleSix _ a _ =>
      have hc : (center (starImage Lu (d.fixedCore u) Lu)).map e.toMonoidHom = center _ := by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact (centerCongr e ⟨y,hy⟩).property
        · intro hx
          exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩
      exact (d.fixedComponent_C27_tripleSix_row_impossible u h
        ((QuotientGroup.congr _ _ e hc).trans a.quotientEquiv)).elim
    | binaryLinear n hn _ a _ =>
      exact (d.fixed_binary_linear_false u h hn (e.trans a.groupEquiv)).elim
    | orthogonalSix _ _ a _ _ =>
      exact (d.fixedComponent_C27_alternatingEight_row_impossible u h (e.trans a.groupEquiv)).elim
    | symmetricEight _ a _ =>
      exact (d.fixedComponent_C27_alternatingEight_row_impossible u h (e.trans a.subgroupEquiv)).elim
    | exteriorFive _ _ a _ _ _ =>
      exact (d.fixedComponent_C27_binaryFive_row_impossible u h (e.trans a)).elim

theorem fixedComponent_C27_moved_card
    (u : F.U) {Lu : Subgroup G} (h : Nonquasisimple.Case d u Lu) :
    Nat.card (⁅starV Lu (d.fixedCore u),Lu.subgroupOf (Lu ⊔ d.fixedCore u)⁆ :
      Subgroup (Lu ⊔ d.fixedCore u : Subgroup G)) = 64 := by
  obtain ⟨a⟩ := d.fixedComponent_C27_natural_moved u h
  have hd := a.natural.action.linearEquiv.finrank_eq
  rw [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide)] at hd
  norm_num only [Fintype.card_fin] at hd
  exact ChapterC.C27Source.star_moved_commutator_card Lu (d.fixedCore u)
    a.contained a.sectionData a.splitting 6 hd

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
