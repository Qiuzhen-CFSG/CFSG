module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.NativeSourceAssembly
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization.OmegaNormalizer.Models
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M23.Properties.TwoRank
public import GorensteinWalter.PSL2Center
/-!
# The even-center residue of the actual 2.3.9 catalogue

All direct models have trivial center; the alternating covers have odd center.
Thus the genuine refined catalogue with nontrivial two-group center retains
only the quotient PSL₃(4) alternative. The binary M₂₂ residue remains separate
and is excluded by the original natural-block rank calculation.
Source: Aschbacher–Smith 2.3.9(7) and 2.4.11, printed pp.525–526, 532.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open scoped MatrixGroups
private lemma center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb := (centerCongr e ⟨a,ha⟩).property
  change e a ∈ center B at hb
  rw [h,mem_bot] at hb
  exact e.injective (hb.trans e.map_one.symm)
private lemma psl_center {K : Type*} [Group K] {m q : ℕ}
    (hm : 3 ≤ m) (h : ClassicalGroup.IsPSL K m q) : center K = ⊥ := by
  obtain ⟨F,_,_,_,⟨e⟩⟩ := h
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) F) := Atlas.sl_perfect m hm
  exact center_transport e (Group.IsPerfect.center_quotient_center_eq_bot _)
private lemma symplectic_center {K : Type*} [Group K]
    (h : LieType.IsDerivedSymplecticFour K) : center K = ⊥ := by
  obtain ⟨n,hn,F,_,_,hF,⟨e⟩⟩ := h
  by_cases h1 : n = 1
  · have he := Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (by simpa only [h1,pow_one] using hF)
    exact center_transport (e.trans he) (alternatingGroup.center_eq_bot (by norm_num))
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact center_transport (e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF (by omega)))
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot

variable {G : Type*} [Group G] [Finite G] (K M S : Subgroup G) (z : G)
    [IsQuasisimple K]
omit [Finite G] in
lemma psl_four_of_refined_even_center
    (h : RefinedIntersection K M S z) (hZ : center K ≠ ⊥)
    (h2 : 2 ∣ Nat.card (center K)) : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have h3 : Nat.card (center K) ≠ 3 := by
    intro hh
    rw [hh] at h2
    norm_num at h2
  cases h with
  | bender h => exact (hZ (BenderFusion.OmegaNormalizerModels.centerless_of_bender_model h)).elim
  | case_b h =>
    rcases h with h | ⟨n,_,h⟩ | h | h
    · exact (hZ (symplectic_center h)).elim
    · exact (hZ (psl_center (by decide) h)).elim
    · exact h
    · exact (h3 h.2.1).elim
  | alternating h =>
    rcases h.1 with he | h
    · obtain ⟨e⟩ := he
      exact (hZ (center_transport e (alternatingGroup.center_eq_bot (by norm_num)))).elim
    · obtain ⟨e⟩ := h.2.1
      exact (h3 ((Nat.card_congr e.toEquiv).trans (by norm_num))).elim
  | linear_three h _ =>
    obtain ⟨e⟩ := h
    exact (hZ (center_transport (e.trans Matrix.PSL3Three.equiv.symm) Matrix.PSL3Three.center_eq_bot)).elim
  | linear_two p _ h _ =>
    obtain ⟨F,_,_,_,⟨e⟩⟩ := h
    exact (hZ (center_transport e (GorensteinWalter.psl2_center_eq_bot F))).elim
  | sporadic h =>
    rcases h with ⟨⟨e⟩,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
    · exact (hZ (center_transport e Sporadic.Mathieu.m11_center_eq_bot)).elim
    · exact (hZ (center_transport e Sporadic.Mathieu.m22_center_eq_bot)).elim
    · exact (hZ (center_transport e Sporadic.Mathieu.M23Geometry.m23_center_eq_bot)).elim
  | case_g h =>
    obtain ⟨e,_⟩ := h
    exact (hZ (LieType.Binary.center_eq_bot e)).elim
end CFSG.Quasithin.Chapter2.ComponentRefinement
