module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFourNormalizer
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingProjectiveSource
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFullAffine
public import Theory.SpecificGroups.PSL3Four.FieldExtension.SemilinearInclusion

/-! The actual original projective residual has index at most two in the
normalizer of the original point four. Index four would put an ambient Sylow
two-subgroup in that normalizer, contrary to the original noncentrality. -/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_four_normalizer_index_dvd_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let W := B ⊔ tripleSixScalarResidual K
    let N := normalizer (B : Set G)
    Nat.card W = 241920 ∧ W.relIndex N ∣ 2 := by
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let W := B ⊔ tripleSixScalarResidual K
  let N := normalizer (B : Set G)
  let V := tripleSixPoint D a t
  obtain ⟨_,hcenter,_,_,_⟩ := original_tripleSix_point_identification_at
    h structural D a t ht heven hout
  obtain ⟨_,hNV,_,_,_,_,_,hi,e,hWN,f,hf,hker,_⟩ :=
    original_tripleSix_escaping_projective_geometry h structural D a t ht heven hout
  have hVW : V ≤ W := by
    rw [show V = centerIn B from hcenter.symm]
    exact inf_le_left.trans le_sup_left
  have hWc : Nat.card W = 241920 := by
    have hc := card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      Matrix.PSL3Four.card_PGL,hker,
      Nat.card_congr (subgroupOfEquivOfLe hVW).toEquiv,
      (tripleSixPoint_properties D a t ht).2.2.1] at hc
    exact hc
  refine ⟨hWc,?_⟩
  have hi4 : W.relIndex N ≠ 4 := by
    intro hi4
    have hNc := relIndex_mul_relIndex (⊥ : Subgroup G) W N bot_le hWN
    rw [relIndex_bot_left,relIndex_bot_left] at hNc
    rw [hWc,hi4] at hNc
    have hd : 2^10 ∣ Nat.card N := by rw [←hNc]; norm_num
    obtain ⟨Q,hQc⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd
    let Q' := Q.map N.subtype
    have hQ'c : Nat.card Q' = 2^10 :=
      (card_map_of_injective N.subtype_injective).trans hQc
    obtain ⟨S,hQS⟩ := (IsPGroup.of_card hQ'c).exists_le_sylow
    have hSc : Nat.card S = 1024 :=
      (Nat.card_congr (S.equiv T).toEquiv).trans
        (original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout).1
    have hQS' : Q' = (S : Subgroup G) :=
      eq_of_le_of_card_ge hQS (by rw [hQ'c,hSc]; norm_num)
    apply original_tripleSix_escaping_four_normalizer_no_sylow
      h structural D a t ht heven hout S
    rw [←hNV,←hQS']
    exact map_subtype_le Q
  have hchoices : W.relIndex N = 1 ∨ W.relIndex N = 2 ∨ W.relIndex N = 4 := by
    have hm := Nat.mem_divisors.mpr ⟨hi,(by decide : 4≠0)⟩
    rw [show Nat.divisors 4 = {1,2,4} from rfl] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  rcases hchoices with hi1 | hi2 | hi4'
  · rw [hi1]; exact one_dvd _
  · rw [hi2]
  · exact (hi4 hi4').elim

end CFSG.Quasithin.Chapter12.Section07
