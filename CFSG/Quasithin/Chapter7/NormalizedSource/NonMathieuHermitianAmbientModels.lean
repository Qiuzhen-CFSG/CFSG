module
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SeedCore
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SelfDualModels
public import Theory.Mathieu.M22.ReeExclusion
public import Theory.Mathieu.M22.Properties.ComponentCentralizer
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
public import Theory.GroupTheory.SolvableOuterQuotient
import all CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Models

/-!
# Simple sections containing the full Hermitian Mathieu seed

A perfect seed with quasisimple two-core quotient and an actual M₂₂ radical
quotient restricts its containing Theorem C simple section to M₂₂, M₂₃,
M₂₄, HS or J₄. The section exclusions eliminate the classical rows; the
remaining rank-two rows are excluded by the perfect-cover and Ree embedding
results. Each surviving model has a two-group outer automorphism group.
Consequently odd-order actions on the containing quasisimple two-core
quotient are inner, retaining its full center and the original seed kernel.

This extracts the section-only part of the comparison used in
Aschbacher--Smith 4.4.3, printed p.623, for the ordinary branch needed in
8.2.7, p.718 (refs/quasithin.pdf). It does not require an outside actor to
centralize the seed. The literal chosen-module application is in
NonFFSourceNonMathieuHermitianFieldFourAmbientAction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterA.Section02 Chapter4.Section04.OddLocalMathieu Sporadic.Mathieu

private theorem section_rank_two_rows {S : Type*} [Group S]
    (h : IsSectionOf M22 S) {f : ℕ} (hm : IsTheoremCRankTwoModel S f) :
    RemainingOddLocalRankTwoModel S := by
  cases hm with
  | linear hn hm => exact (not_binary_linear_three_section h hm).elim
  | symplectic hn hm => exact (not_binary_symplectic_section h hm).elim
  | g2 hn hm => exact Or.inl ⟨f,hn,hm⟩
  | triality hn hm => exact Or.inr (Or.inl ⟨f,hn,hm⟩)
  | ree_f4 m hm hf iso => exact Or.inr (Or.inr ⟨m,hm,iso⟩)
  | symplectic_derived hf iso =>
    have hd := section_card_dvd (h.ambient_injective
      (iso.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toMonoidHom
      (iso.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).injective)
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  | g2_derived hf iso =>
    have hd := section_card_dvd (h.ambient_injective iso.some.toMonoidHom iso.some.injective)
    rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits hf iso =>
    have hd := section_card_dvd (h.ambient_injective iso.some.toMonoidHom iso.some.injective)
    rw [Tits.parrottGroup_card] at hd
    norm_num at hd

/-- A full perfect M22 seed forces one of five actual simple sections.
No centralization of that seed by an outside actor is required. -/
theorem hermitian_seed_simple_section_models
    {P S : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    [IsQuasisimple (P ⧸ pCore 2 P)] [Group S] [Finite S]
    (hm : IsTheoremCModel S) (f : P →* S) (hne : f.range ≠ ⊥)
    (e : (f.range ⧸ solvableRadical f.range) ≃* M22) :
    Nonempty (S ≃* M22) ∨ Nonempty (S ≃* M23) ∨ Nonempty (S ≃* M24) ∨
      Nonempty (S ≃* Sporadic.LeechRelated.HS.Carrier) ∨ Nonempty (S ≃* Janko4.Model) := by
  let g := e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : IsSectionOf M22 S := ⟨f.range,g,hg⟩
  cases hm with
  | alternating n hn iso => exact (not_alternating_section hs (by omega) iso.some).elim
  | odd hm =>
    cases hm with
    | linear_two q n hq ho hn he => exact (not_odd_linear_two_section hs ho.pow he).elim
    | linear_three q hq ho he => exact (not_odd_linear_three_section hs ho he).elim
    | unitary_three q hq ho he => exact (not_odd_unitary_three_section hs ho he).elim
  | bender hm => exact (not_bender_section hs hm).elim
  | rank_two n hm =>
    have hr := section_rank_two_rows hs hm
    obtain ⟨_,hq,⟨eq⟩⟩ := rank_two_seed_quasisimple hr f hne e
    let := hq
    obtain ⟨m,hm,⟨er⟩⟩ := rank_two_mathieu_cover_is_ree hr f.range eq
    exact (M22LocalSections.no_embedding_ree g hg hm
      (er.toMonoidHom.comp f.range.subtype) (er.injective.comp f.range.subtype_injective)).elim
  | linear_binary n hn hm => exact (not_binary_linear_section hs hn hm).elim
  | sporadic hm =>
    have hd := section_card_dvd hs
    rcases hm with ⟨name,hn,⟨a⟩⟩ | ⟨a⟩
    · cases name with
      | m11 =>
        rw [Nat.card_congr a.toEquiv] at hd
        change 443520 ∣ Nat.card M11 at hd
        rw [m11_order] at hd
        norm_num at hd
      | m12 =>
        rw [Nat.card_congr a.toEquiv] at hd
        change 443520 ∣ Nat.card M12 at hd
        rw [m12_order] at hd
        norm_num at hd
      | m22 => exact .inl ⟨a⟩
      | m23 => exact .inr (.inl ⟨a⟩)
      | m24 => exact .inr (.inr (.inl ⟨a⟩))
      | hs => exact .inr (.inr (.inr (.inl ⟨a⟩)))
      | j4 => exact .inr (.inr (.inr (.inr ⟨a⟩)))
      | j2 =>
        rw [Nat.card_congr a.toEquiv] at hd
        change 443520 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
        rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
        norm_num at hd
      | j3 => exact (hn rfl).elim
      | he =>
        rw [Nat.card_congr a.toEquiv] at hd
        have hb := hd.trans (Held.OddOrderBound.card_dvd_of_graph_and_pair_bound
          Held.NormalizerGraph.Orbital.held_le_preservingGroup
          (Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer_card_dvd
            Held.NormalizerGraph.Orbital.held_le_preservingGroup))
        norm_num at hb
      | ru =>
        rw [Nat.card_congr a.toEquiv] at hd
        change 443520 ∣ Nat.card Rudvalis.Model at hd
        rw [Rudvalis.model_card] at hd
        norm_num at hd
    · rw [Nat.card_congr a.some.toEquiv,Janko1.card_model] at hd
      norm_num at hd

private theorem outer_two_of_conj_surjective {S : Type*} [Group S]
    (h : Function.Surjective (MulAut.conj : S →* MulAut S)) : IsPGroup 2 (MulAut.Outer S) := by
  have he : MulAut.innerSubgroup S = ⊤ := MonoidHom.range_eq_top.mpr h
  let : Subsingleton (MulAut S ⧸ (⊤ : Subgroup (MulAut S))) :=
    QuotientGroup.subsingleton_quotient_top
  have ht : IsPGroup 2 (MulAut S ⧸ (⊤ : Subgroup (MulAut S))) :=
    IsPGroup.of_subsingleton _ _
  exact ht.of_equiv (QuotientGroup.quotientMulEquivOfEq he).symm

/-- The same five sections have two-group outer automorphisms. -/
theorem hermitian_seed_outer_two
    {P S : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    [IsQuasisimple (P ⧸ pCore 2 P)] [Group S] [Finite S]
    (hm : IsTheoremCModel S) (f : P →* S) (hne : f.range ≠ ⊥)
    (e : (f.range ⧸ solvableRadical f.range) ≃* M22) : IsPGroup 2 (MulAut.Outer S) := by
  rcases hermitian_seed_simple_section_models hm f hne e with a | a | a | a | a
  · have ho : IsPGroup 2 (MulAut.Outer M22) := IsPGroup.of_card_dvd_pow (n := 1)
      (by simpa only [pow_one,←index_eq_card] using m22_inner_index_dvd_two)
    exact ho.of_equiv (MulAut.outerCongr a.some).symm
  · exact (outer_two_of_conj_surjective m23_conj_surjective).of_equiv (MulAut.outerCongr a.some).symm
  · exact (outer_two_of_conj_surjective M24OuterRestriction.conj_surjective).of_equiv
      (MulAut.outerCongr a.some).symm
  · open Sporadic.LeechRelated.HS in
    exact (outer_isPGroup_two_of_pointStabilizer_map pointStabilizer_map
      normalizer_relIndex_dvd_two_pow).of_equiv (MulAut.outerCongr a.some).symm
  · exact Janko4.AdequateLocal.outer_isPGroup_two.of_equiv (MulAut.outerCongr a.some).symm

/-- Odd-order automorphisms of the actual containing simple section are inner. -/
theorem hermitian_seed_odd_action_inner
    {P S : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    [IsQuasisimple (P ⧸ pCore 2 P)] [Group S] [Finite S]
    (hm : IsTheoremCModel S) (f : P →* S) (hne : f.range ≠ ⊥)
    (e : (f.range ⧸ solvableRadical f.range) ≃* M22)
    (a : MulAut S) {n : ℕ} (hn : Odd n) (ha : a^n=1) :
    ∃ x : S, a = MulAut.conj x := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup S)
  obtain ⟨k,hk⟩ := hermitian_seed_outer_two hm f hne e (q a)
  have hpow : (q a)^n=1 := by rw [←map_pow,ha,map_one]
  have hqa : q a=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (hn.coprime_two_left.pow_left k) (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hpow))
  obtain ⟨x,hx⟩ := (QuotientGroup.eq_one_iff a).mp hqa
  exact ⟨x,hx.symm⟩
/-- Lift innerness to the full quasisimple two-core quotient. The central
kernel of that quotient is retained, using faithful perfect central descent. -/
theorem hermitian_seed_odd_twoCore_action_inner
    {P Q : Type*} [Group P] [Finite P] [Group.IsPerfect P] [Nontrivial P]
    [IsQuasisimple (P ⧸ pCore 2 P)] [Group Q] [Finite Q]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Q)
    (j : P →* Q) (hj : Function.Injective j)
    (e : (P ⧸ solvableRadical P) ≃* M22)
    (a : MulAut Q) {n : ℕ} (hn : Odd n) (ha : a^n=1) :
    ∃ x : Q, quotientAut (pCore 2 Q) a =
      MulAut.conj (QuotientGroup.mk' (pCore 2 Q) x) := by
  let f := (projection Q).comp j
  obtain ⟨hfn,_,⟨ef⟩⟩ := seed_image j hj e
  let a2 := quotientAut (pCore 2 Q) a
  let b := MulAut.centralQuotientAction (MulEquiv.refl _) a2
  have hb : b^n=1 := by
    change (MulAut.centralQuotientAction (MulEquiv.refl _)
      (quotientAut (pCore 2 Q) a))^n=1
    rw [←map_pow,←map_pow,ha,map_one,map_one]
  obtain ⟨y,hy⟩ := hermitian_seed_odd_action_inner (simpleSection_model hQ) f hfn ef b hn hb
  obtain ⟨x,hx⟩ := (MulAut.centralQuotientAction_inner_iff (MulEquiv.refl _) a2).mp ⟨y,hy⟩
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 Q) x
  exact ⟨z,hx⟩

end CFSG.Quasithin.Chapter7.NormalizedSource
