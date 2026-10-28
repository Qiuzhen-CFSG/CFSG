module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Quotient

/-!
# Sylow subgroups of Held's noncentral centralizer and its central quotient

The known centralizer P = C_C(pi) has order 64. If a Sylow two-subgroup
of C were any larger, its image would be a Sylow subgroup of G, of order
128. Then mu would be a central involution in that Sylow subgroup.
Conjugacy of Sylow subgroups and the cyclic center of D.sylow would make
mu conjugate to D.z. Nonfusion excludes this case, so P itself is Sylow.
Its image is C_Q(p), and is a Sylow subgroup of Q of order 32.

These are the Sylow assertions in Held's proof of Lemma 4.2, printed
p.233, Illinois J. Math. 13 (1969), DOI 10.1215/ijm/1256053756.
Neither simplicity nor additional ambient fusion information is used here.
-/

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem central_sylow_involution_isConj (T : Sylow 2 G)
    (x : center T) (hx : orderOf x = 2) : IsConj D.z ((x : T) : G) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G D.sylow T
  let f := D.sylow.equivSMul g
  let fc := centerCongr f
  let := D.cyclic_center
  have horder : orderOf (fc.symm x) = 2 := (fc.symm.orderOf_eq x).trans hx
  have hsame : fc.symm x = D.involution :=
    IsCyclic.eq_of_orderOf_eq_two horder D.involution_order
  have heq : fc D.involution = x := (fc.symm_apply_eq.mp hsame).symm
  exact isConj_iff.mpr ⟨g, congrArg
    (fun a : center ↥(g • D.sylow : Sylow 2 G) => ((a : ↥(g • D.sylow : Sylow 2 G)) : G)) heq⟩

public theorem exists_sylow_eq_P
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ∃ S : Sylow 2 (C D e), (S : Subgroup (C D e)) = P D e := by
  have hp : IsPGroup 2 (P D e) := IsPGroup.of_card (n := 6) (by rw [P_card]; decide)
  obtain ⟨S, hPS⟩ := hp.exists_le_sylow
  let R : Subgroup G := (S : Subgroup (C D e)).map (C D e).subtype
  obtain ⟨T, hRT⟩ := (S.isPGroup'.map (C D e).subtype).exists_le_sylow
  have hScard : Nat.card R = Nat.card S := card_map_of_injective (C D e).subtype_injective
  have hTcard : Nat.card T = 128 :=
    (Nat.card_congr (T.equiv D.sylow).toEquiv).trans (D.sylow_card)
  have hSle : Nat.card S ≤ 128 := by
    rw [← hScard, ← hTcard]
    exact card_le_of_le hRT
  have hSne : Nat.card S ≠ 128 := by
    intro h128
    have hRT' : R = (T : Subgroup G) := eq_of_le_of_card_ge hRT (by omega)
    have hTC : (T : Subgroup G) ≤ C D e := hRT' ▸ map_subtype_le _
    have hmuS : mu D e ∈ (S : Subgroup (C D e)) :=
      hPS (Z_le_P D e (mem_zpowers (mu D e)))
    have hmuT : D.a10NoncentralInvolution e ∈ T :=
      hRT (mem_map_of_mem (C D e).subtype hmuS)
    let x : center T := ⟨⟨D.a10NoncentralInvolution e, hmuT⟩,
      mem_center_iff.mpr (fun t => Subtype.ext
        (mem_centralizer_singleton_iff.mp (hTC t.property)))⟩
    exact hfusion (central_sylow_involution_isConj D T x
      (by simpa only [x, Subgroup.orderOf_mk] using D.a10NoncentralInvolution_order e))
  have hSge : 64 ≤ Nat.card S := (P_card D e) ▸ card_le_of_le hPS
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hnle : n ≤ 7 := by
    by_contra hn'
    have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← hn] at this
    omega
  have hScard64 : Nat.card S = 64 := by
    interval_cases n <;> norm_num only [pow_succ, pow_zero] at hn <;> omega
  exact ⟨S, (eq_of_le_of_card_ge hPS (by rw [P_card, hScard64])).symm⟩

public theorem exists_quotient_sylow_eq_centralizer
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    ∃ T : Sylow 2 (Q D e),
      (T : Subgroup (Q D e)) = centralizer ({p D e} : Set (Q D e)) := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_P D e hfusion
  refine ⟨Sylow.mapSurjective (QuotientGroup.mk'_surjective (Z D e)) S, ?_⟩
  change (S : Subgroup (C D e)).map (q D e) = _
  rw [hS, ← centralizer_p_eq_map D e hfusion]

public theorem p_order
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) : orderOf (p D e) = 2 := by
  apply orderOf_eq_prime
  · change q D e (pi D e) ^ 2 = 1
    rw [← map_pow]
    have hpi : pi D e ^ 2 = 1 := by
      apply Subtype.ext
      simpa only [pi, Subgroup.coe_pow, Subgroup.coe_one, D.z_order] using
        pow_orderOf_eq_one D.z
    rw [hpi, map_one]
  · intro hp
    have hZ : pi D e ∈ Z D e := (QuotientGroup.eq_one_iff _).mp hp
    have heq : (pi D e : G) = (mu D e : G) := by
      let : IsCyclic (Z D e) := by unfold Z; infer_instance
      have h1 : orderOf (⟨pi D e, hZ⟩ : Z D e) = 2 := by
        simp only [Subgroup.orderOf_mk, pi, D.z_order]
      have hmuZ : mu D e ∈ Z D e := mem_zpowers (mu D e)
      have h2 : orderOf (⟨mu D e, hmuZ⟩ : Z D e) = 2 := by
        simp only [Subgroup.orderOf_mk, mu_order]
      exact congrArg (fun z : Z D e => ((z : C D e) : G))
        (IsCyclic.eq_of_orderOf_eq_two h1 h2)
    exact hfusion (isConj_iff.mpr ⟨1, by
      simpa only [one_mul, inv_one, mul_one, pi, mu] using heq⟩)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
