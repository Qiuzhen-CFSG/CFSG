module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Saturated
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Source
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank.Five
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.Mathieu.M24.Properties.AutomorphismTwoRank
public import Theory.SpecificGroups.Held.TwoRank.Automorphisms
public import Theory.SpecificGroups.Rudvalis.Model.AutomorphismTwoRank
/-!
# Six-dimensional reduced sections in the complementary point carriers

Every remaining carrier except J₄ has automorphism two-rank at most six.
The literal reduced section therefore fills that rank bound, so the
opposite elementary factor centralizes the containing component. The
source moved-normalizer bound excludes it. All quotient maps, fixed
kernels and the original module are retained.

Quasisimple.Source removes the rank-two premise and applies this to the
natural-plus-dual row. Its actual J₄ comparison remains open.
Source: Aschbacher--Smith 10.2.9, printed pp.750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02 Representation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) L W}
  (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) ρ)
  (h64 : 64 ≤ Nat.card W)
include D c d h64

/-- Both higher binary-linear carriers are excluded by their full automorphism ranks. -/
theorem not_binary_linear_of_large_section [Group.IsPerfect I]
    {r : ℕ} (hr : r = 4 ∨ r = 5)
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) r 2) : False := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
  let := Fintype.ofFinite F
  let k : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := eI.trans (Atlas.fieldEquivPSL r k)
  apply not_of_saturated_section D c d (m := 6) h64 e
  rcases hr with rfl | rfl
  · exact BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le.trans (by decide)
  · exact BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le

/-- The five complementary sporadic carriers of automorphism rank at most six. -/
theorem not_small_sporadic_of_large_section [IsQuasisimple I]
    (name : ClassificationModels.SporadicName)
    (hn : name = .m23 ∨ name = .m24 ∨ name = .hs ∨ name = .he ∨ name = .ru)
    (e : (I ⧸ center I) ≃* name.Carrier) : False := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · change (I ⧸ center I) ≃* Sporadic.Mathieu.M23 at e
    exact not_of_saturated_section D c d (m := 6) h64 e
      (Sporadic.Mathieu.m23_automorphism_twoRank_le_four.trans (by decide))
  · change (I ⧸ center I) ≃* Sporadic.Mathieu.M24 at e
    have hz : center Sporadic.Mathieu.M24 = ⊥ := by
      apply bot_unique
      intro x hx
      have hh : e.symm x ∈ center (I ⧸ center I) := by
        apply mem_center_iff.mpr
        intro y
        apply e.injective
        simpa only [map_mul,e.apply_symm_apply] using (mem_center_iff.mp hx (e y))
      rw [Group.IsPerfect.center_quotient_center_eq_bot,mem_bot] at hh
      exact mem_bot.mpr (e.symm.map_eq_one_iff.mp hh)
    exact not_of_saturated_section D c d (m := 6) h64 e
      (Sporadic.Mathieu.m24_automorphism_rank_le_six hz)
  · change (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier at e
    exact not_of_saturated_section D c d (m := 6) h64 e
      (Sporadic.LeechRelated.HS.automorphism_twoRank_le_five.trans (by decide))
  · change (I ⧸ center I) ≃* Held.He at e
    exact not_of_saturated_section D c d (m := 6) h64 e Held.automorphism_rank_le_six
  · change (I ⧸ center I) ≃* Rudvalis.Model at e
    let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
    let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
    exact not_of_saturated_section D c d (m := 6) h64 e Rudvalis.automorphism_rank_le_six

/-- A reduced binary-three section of order at least 64 leaves only J₄. -/
theorem remaining_janko_four_of_large_binary_three_section [IsQuasisimple I]
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (hr : ¬ ∃ n, ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    Nonempty ((I ⧸ center I) ≃* Janko4.Model) := by
  rcases remaining_of_binary_three D c dL hr with ⟨r,hr,hI⟩ | ⟨name,hn,⟨e⟩⟩
  · exact (not_binary_linear_of_large_section D c d h64 hr hI).elim
  · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (not_small_sporadic_of_large_section D c d h64 .m23 (by simp) e).elim
    · exact (not_small_sporadic_of_large_section D c d h64 .m24 (by simp) e).elim
    · exact ⟨e⟩
    · exact (not_small_sporadic_of_large_section D c d h64 .hs (by simp) e).elim
    · exact (not_small_sporadic_of_large_section D c d h64 .he (by simp) e).elim
    · exact (not_small_sporadic_of_large_section D c d h64 .ru (by simp) e).elim
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
