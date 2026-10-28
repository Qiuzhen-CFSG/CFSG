module

public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence
public import GorensteinWalter.PGL2LowReflectedToriCard
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
public import Theory.GroupTheory.CentralizerIndexBound
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
/-!
# A marked involution centralizer bound for odd PGL₂

An inner involution has a centralizer in the index-two PSL₂ subgroup
of order at most q+1. For an outer involution, fusion transports the actual
low reflected torus, whose normalizer has order at most 2(q+1).

This excludes proper PGL₂ subfield overgroups of an involution centralizer
in PSL₂(p²), in Aschbacher–Smith E.2.2(2c), printed pp.215–216.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PGL2
/-- An involution centralizer in odd PGL₂ has order at most twice the field plus one. -/
theorem involution_centralizer_card_le
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hc : 3 < Nat.card F)
    (t : PGL2 F) (ht : IsInvolution t) :
    Nat.card (centralizer ({t} : Set (PGL2 F))) ≤ 2 * (Nat.card F + 1) := by
  classical
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let J := commutator (PGL2 F)
  have hJ : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hc
  have hi : J.index = 2 := hJ ▸ pgl2_psl2Range_index_eq_two F hF
  by_cases htJ : t ∈ J
  · let e : J ≃* PSL(2,F) := (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      F hF hc (MulEquiv.refl (PGL2 F))).some
    let tJ : J := ⟨t, htJ⟩
    have hI : IsInvolution (e tJ) := by
      constructor
      · intro h
        exact ht.1 (congrArg (fun y : J => (y : PGL2 F))
          (e.injective (show e tJ = e 1 by simpa only [map_one] using h)))
      · simpa only [← map_pow, map_one] using congrArg e
          (show tJ ^ 2 = 1 from Subtype.ext ht.2)
    have heq : (centralizer ({t} : Set (PGL2 F))).subgroupOf J = centralizer ({tJ} : Set J) := by
      ext y
      simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hmap : (centralizer ({tJ} : Set J)).map e.toMonoidHom = centralizer ({e tJ} : Set (PSL(2,F))) := by
      rw [map_centralizer_equiv, Set.image_singleton]
    have hbound : Nat.card ((centralizer ({t} : Set (PGL2 F))).subgroupOf J) ≤ Nat.card F + 1 := by
      rw [heq, ← card_map_of_injective (K := centralizer ({tJ} : Set J)) (f := e.toMonoidHom) e.injective, hmap]
      rcases Theory.PSL2.involution_centralizer_card_cases hF (e tJ) hI with h | h <;> omega
    have hind : J.relIndex (centralizer ({t} : Set (PGL2 F))) ≤ 2 := by
      apply Nat.le_of_dvd (by decide)
      simpa only [hi] using relIndex_dvd_index_of_normal J (centralizer ({t} : Set (PGL2 F)))
    have hb := card_le_centralizer_card_mul_relIndex (centralizer ({t} : Set (PGL2 F))) J {t} le_rfl
    exact hb.trans (by nlinarith)
  · let P : Sylow 2 (PGL2 F) := Classical.choice inferInstance
    obtain ⟨m, _, ⟨d⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hF P
    obtain ⟨D⟩ := pgl2_low_reflected_tori_card_four F hF hc P d
    obtain ⟨g, hg⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate_of_odd_prime_power
      F hF D.s_involution ht (hJ ▸ D.s_not_mem_commutator) (hJ ▸ htJ))
    have heq : (centralizer ({D.s} : Set (PGL2 F))).map (MulAut.conj g).toMonoidHom =
        centralizer ({t} : Set (PGL2 F)) := by
      rw [map_centralizer_equiv, Set.image_singleton]
      change centralizer ({g * D.s * g⁻¹} : Set (PGL2 F)) = _
      rw [hg]
    rw [← heq, card_map_of_injective (MulAut.conj g).injective, D.centralizer_eq]
    have hn : zpowers D.w ≤ normalizer (D.U : Set (PGL2 F)) := by
      apply zpowers_le.mpr
      apply mem_normalizer_iff.mpr
      intro u
      constructor
      · intro hu
        rw [D.w_inverts_U u hu]
        exact D.U.inv_mem hu
      · intro hu
        have hh := D.U.inv_mem hu
        have hiw : D.w⁻¹ = D.w := inv_eq_of_mul_eq_one_right D.w_involution
        rw [← D.w_inverts_U _ hu, hiw] at hh
        have hu : D.w * (D.w * u * D.w) * D.w = u := by
          calc
            _ = (D.w * D.w) * u * (D.w * D.w) := by group
            _ = u := by rw [D.w_involution]; simp
        rwa [hu] at hh
    have hw : orderOf D.w = 2 := orderOf_eq_prime
      (by simpa only [pow_two] using D.w_involution)
      (fun h => D.w_not_mem_U (h ▸ D.U.one_mem))
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D.U (zpowers D.w) hn
    rw [Nat.card_zpowers, hw] at hprod
    have hpos : 1 ≤ Nat.card (D.U ⊓ zpowers D.w : Subgroup (PGL2 F)) := Nat.card_pos
    have hU : Nat.card D.U ≤ Nat.card F + 1 := by rcases D.U_card with h | h <;> omega
    nlinarith
end Theory.PGL2
