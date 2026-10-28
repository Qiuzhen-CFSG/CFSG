module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPushingUp
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianOrdinary
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpOrdinary
import all CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianOrdinary
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPushingUp

/-!
# Ordinary field-four Hermitian components

The actual PSL₃(4) quotient has cubic rank two. Cyclic Sylow lifting
retains that lower bound through the full original core and central kernels.
The literal C.3 radical normalizer then excludes the linear, symplectic,
G₂ and triality rows. The full quotient order excludes the small derived
models, and the existing fifteen-free normalizer argument excludes Ree.
At binary rank at least eight the remaining ordinary component is an actual
central cover of J₄. This conclusion does not exclude that last component.

The Chapter 12 FieldFourComponents extension applies the sieve to the original
chosen nine-space and residual, discharging the rank bound by its fixed-free
embedding in the same component quotient.
Source: Aschbacher--Smith C.3.2--5 and 4.4.12, printed pp.149--150,621--623,
as used in 8.2.7, printed p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterA.Section02 ClassificationModels Chapter7.NormalizedSource.NonMathieuHermitian
variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
variable {H M B R W : Subgroup G}

/-- Cubic rank survives both original quotient kernels. -/
theorem field_four_span_three_rank
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    2 ≤ primeRank 3 (conjugateSpanBy B M) := by
  have hr := field_four_projective_three_rank hc
  have hB : 2 ≤ primeRank 3 B := by
    by_contra! hB
    let P : Sylow 3 B := Classical.choice inferInstance
    let f := e.toMonoidHom.comp ((QuotientGroup.mk' (center (B ⧸ pCore 2 B))).comp
      (QuotientGroup.mk' (pCore 2 B)))
    have hf : Function.Surjective f := e.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
    have hu := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) f hf
    omega
  exact hB.trans (Theory.GroupTheory.primeRank_le_of_injective 3
    (inclusion (le_conjugateSpanBy B M)) (inclusion_injective _))

/-- No rank-two Theorem C model contains this original ordinary configuration. -/
theorem field_four_no_ordinary_rankTwo
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K) {f : ℕ}
    (hm : IsTheoremCRankTwoModel (K ⧸ center K) f) : False := by
  have hr := field_four_span_three_rank (M := M) hc e
  have hd : 20160 ∣ Nat.card (K ⧸ center K) := by
    have hh := ordinary_hermitian_quotient_card_dvd h e K hK
    norm_num [Matrix.PSL3.LinearThree.card_projective,hc] at hh
    exact hh
  cases hm with
  | linear hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    by_cases hf1 : f = 1
    · rw [Nat.card_congr a.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hf1] at hd
      norm_num at hd
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hu : primeRank 3 (conjugateSpanBy B M) ≤ 1 := by
      apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK a (by decide : Odd 3)
      intro A P hA hP hne hN
      let := hA
      by_contra! hb
      obtain ⟨g,point,hg⟩ := MainConverse.LinearThreeGeometry.twoLocal_conjugate_le F
        (by omega) hF (normalizer (P : Set _)) ⟨P,hne,hP,rfl⟩
      let j := (MulAut.conj g).toMonoidHom.comp A.subtype
      have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic F point := by
        refine le_trans ?_ hg
        rintro _ ⟨x,rfl⟩
        exact mem_map_of_mem _ (hN x.property)
      apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic F
        (by decide : Odd 3) (by omega) (by
          rw [hF]
          exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 2 ≤ f))
        j ((MulAut.conj g).injective.comp A.subtype_injective)
      cases point
      · exact Or.inr hj
      · exact Or.inl hj
    omega
  | symplectic hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hu := h.ordinary_span_primeRank_le_one_of_sp4 K hK
      (a.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm) (by decide : Odd 3)
    omega
  | g2 hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2^2)
        (Nat.pow_le_pow_right (by decide) hf)
    have hu := h.ordinary_span_primeRank_le_one_of_g2 K hK a hlarge (by decide : Odd 3)
    omega
  | triality hf hm =>
    have hu := h.ordinary_span_primeRank_le_one_of_isTrialityGroupAt K hK hf hm (by decide : Odd 3)
    omega
  | ree_f4 m hm hf a =>
    exact no_hermitian_fifteen_free_local (n := 1) h (by simpa using hc) e K hK a.some
      (fun P hne hp => ReeF4.ConverseParabolics.normalizer_fifteen_free hm P hne hp)
  | symplectic_derived hf a =>
    rw [Nat.card_congr (a.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd
    norm_num at hd
  | g2_derived hf a =>
    rw [Nat.card_congr a.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits hf a =>
    rw [Nat.card_congr a.some.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd


/-- The original large ordinary component has an actual J₄ central quotient. -/
theorem field_four_ordinary_janko_four
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : Nat.card E = 4)
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : IsComponent H K)
    (hr : 8 ≤ primeRank 2 (K ⧸ center K)) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    theoremA_knownSimple theoremC_knownSimple
  cases hm with
  | alternating m hm a =>
    exact (no_small_alternating_of_twoRank_ge_eight hr (by omega) a).elim
  | odd hm => exact (h.no_ordinary_component_of_theoremC_odd_model K hK hm).elim
  | bender hm =>
    exfalso
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact h.no_ordinary_component_sl2_central_quotient K hK
        (a.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
    | unitary f hf hm => exact h.no_ordinary_component_binary_unitary_three K hK hf hm
    | suzuki m hm a => exact h.no_ordinary_component_suzuki_central_quotient K hK hm a.some
  | rank_two f hm => exact (field_four_no_ordinary_rankTwo h hc e K hK hm).elim
  | linear_binary m hm a => exact (no_binary_linear_of_twoRank_ge_eight hr hm a).elim
  | sporadic hm => exact theoremBSporadic_j4_of_twoRank_ge_eight hr hm.toTheoremBSporadicModel

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
