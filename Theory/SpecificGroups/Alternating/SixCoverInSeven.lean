module
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# An A₆ central quotient inside a two-extension of A₇

For a perfect group embedded in a two-extension of A₇, its quotient by
its own two-core has order dividing 2520. If its central quotient is A₆,
its odd center has order one or three. The latter gives order 1080,
which does not divide 2520, so the actual two-core quotient is A₆.

The injective map need not have normal image. The proof uses the map
onto its image and removes both intrinsic two-cores; it never assumes
that intersection with the ambient two-core is the whole intrinsic core.

Source application: Aschbacher–Smith, 3.3.22, printed p.597. The odd
central-cover alternatives are GLS III, Theorem 5.2.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating
variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

/-- A perfect subgroup with central A₆ quotient cannot be a triple cover
inside a two-extension of A₇: its core quotient order divides 2520. -/
theorem six_core_quotient_of_injective_seven_extension
    (i : K →* G) (hi : Function.Injective i) [Group.IsPerfect K]
    (eG : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 7))
    (eK : ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃*
      alternatingGroup (Fin 6)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
  let Q := K ⧸ pCore 2 K
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple Q := { simple := eK.isSimpleGroup }
  have ho : Odd (Nat.card (center Q)) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot (G := K) 2) _ le_rfl
  have hdiv : Nat.card Q ∣ 2520 := by
    let f := (QuotientGroup.mk' (pCore 2 G)).comp i
    have hk : IsPGroup 2 f.ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_of_injective i hi
    have hkr : IsPGroup 2 f.rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hk
    let e := f.rangeRestrict.pCoreQuotientEquiv f.rangeRestrict_surjective hkr
    have hd : Nat.card Q ∣ Nat.card (G ⧸ pCore 2 G) := by
      rw [Nat.card_congr e.toEquiv]
      exact dvd_trans (card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 f.range))
        (QuotientGroup.mk'_surjective _)) f.range.card_subgroup_dvd_card
    rw [Nat.card_congr eG.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hd
    exact hd
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) eK ho with
    hc | ⟨_,hc⟩
  · exact ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 eK hc⟩
  · have hcard : Nat.card (Q ⧸ center Q) = 360 := by
      rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hm := (center Q).index_mul_card
    rw [Subgroup.index_eq_card, hcard, hc] at hm
    rw [← hm] at hdiv
    norm_num at hdiv
end Theory.SpecificGroups.Alternating
