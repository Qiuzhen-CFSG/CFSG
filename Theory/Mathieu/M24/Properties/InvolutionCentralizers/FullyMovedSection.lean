module
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.IrreducibleSection
public import Theory.GroupAction.PerfectMovedSmallCenter

/-!
# Odd centralizers of fully moved sections in M₂₄

An even centralizer supplies an involution centralized by the full Sylow.
The native involution-centralizer geometry gives a self-centralizing two-core
whose center has order at most two. The commuting fixed-point argument
excludes the original nonzero fully moved elementary section, without any
irreducibility assumption or choice of coordinates.

Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--751.
The non-A₅ point-component comparison is the actual consumer.
-/

public section
namespace Sporadic.Mathieu.M24InvolutionCentralizers
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer

theorem centralizer_odd_of_fully_moved_section
    (S : Sylow 2 M24) (B E : Subgroup M24) [Group.IsPerfect B] (hB : IsPPerfect 2 B)
    (hSB : (S : Subgroup M24) ≤ normalizer (B : Set M24))
    (hSE : (S : Subgroup M24) ≤ normalizer (E : Set M24))
    (hE : IsElementaryAbelian 2 E) (hEB : E ≤ B) (hc : 2 < Nat.card E)
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set M24)) (hmove : ⁅E,B⁆ = E)
    :
    ¬ 2 ∣ Nat.card (centralizer (B : Set M24)) := by
  intro heven
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group
    B (S : Subgroup M24) S.isPGroup' hSB heven
  let K := centralizer ({z} : Set M24)
  have hBK : B ≤ K := le_sup_left.trans h
  have hSK : (S : Subgroup M24) ≤ K := le_sup_right.trans h
  obtain ⟨hzS,hzcomm⟩ := MulAut.involution_mem_sylow_of_centralizes S z
    ((orderOf_eq_prime_iff.mp hz).1) (by
      intro s hs
      apply mul_inv_eq_iff_eq_mul.mpr
      exact (mem_centralizer_singleton_iff.mp (hSK hs)).symm)
  have hzc : TwoCentral z := ⟨S,hzS,mem_center_iff.mpr (fun s =>
    Subtype.ext (hzcomm s s.property).eq.symm)⟩
  obtain ⟨g,hg⟩ := isConj_iff.mp (isConj_twoA_of_twoCentral z hz hzc).symm
  have hmap : K.map (MulAut.conj g).toMonoidHom = centralizer2A := by
    rw [map_centralizer_equiv,Set.image_singleton,MulAut.conj_apply,hg]
  let e : K ≃* centralizer2A := ((MulAut.conj g).subgroupMap K).trans
    (MulEquiv.subgroupCongr hmap)
  have hchar : centralizer (pCore 2 centralizer2A : Set centralizer2A) ≤
      pCore 2 centralizer2A := by
    rw [←TwoA.kernel_eq_twoCore]
    exact TwoA.kernel_selfCentralizing
  have hbound := Theory.GroupAction.fully_moved_eq_bot_of_overgroup_small_core_center
    S B E K hB hSB hSE hE hEB hcore hmove hBK hSK
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hchar)
  let eP : pCore 2 K ≃* pCore 2 centralizer2A :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  have hh := TwoA.core_center_card_le_two
  rw [← Nat.card_congr (centerCongr eP).toEquiv] at hh
  have he := hbound (hh.trans (by decide))
  rw [he,card_bot] at hc
  omega

end Sporadic.Mathieu.M24InvolutionCentralizers
