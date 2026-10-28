module
public import Stellmacher.TwoResidualCommutatorSupplement
public import Stellmacher.ResidualCoreTripleCentralization
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts
/-!
# A normal star-center join centralizes the residual core

Let MZ be normal in a finite ambient group, with Z normal. Suppose the
group has two two-group supplements: A together with T generates it, as
does B together with U. Assume [M,A] lies in Z while B centralizes M.
If the core Q of the odd residual R normalizes M, Z centralizes Q, and
R/Q has odd order, then M centralizes Q.

Modulo Z the first supplement makes R centralize MZ. Since [MZ,Q]=[M,Q],
this latter commutator is normal in the whole group and lies in M. The
second supplement therefore makes R centralize it. The other triple
commutator vanishes through Z, and the residual-core three-subgroup theorem
kills [M,Q]. No chosen conjugator or factor-support identification is needed.

This is the final commutator calculation of source (8) in Stellmacher
(8.4), Journal of Algebra 190 (1997), printed p.39, stated inside the
actual endpoint stabilizer for its later graph application.
-/

namespace Stellmacher.SectionEight
open scoped commutatorElement

public theorem eight_four_normal_star_core_centralization
    {G : Type*} [Group G] [Finite G]
    (M Z A B T U : Subgroup G) [Z.Normal] [(M ⊔ Z).Normal]
    (hAT : A ⊔ T = ⊤) (hBU : B ⊔ U = ⊤)
    (hT : IsPGroup 2 T) (hU : IsPGroup 2 U)
    (hMA : ⁅M,A⁆ ≤ Z) (hMB : ⁅M,B⁆ = ⊥)
    (hQM : (pCore 2 (twoResidualAmbient (⊤ : Subgroup G))).map
      (twoResidualAmbient (⊤ : Subgroup G)).subtype ≤ Subgroup.normalizer M)
    (hZQ : ⁅Z,(pCore 2 (twoResidualAmbient (⊤ : Subgroup G))).map
      (twoResidualAmbient (⊤ : Subgroup G)).subtype⁆ = ⊥)
    (hodd : Odd (Nat.card ((twoResidualAmbient (⊤ : Subgroup G)) ⧸
      pCore 2 (twoResidualAmbient (⊤ : Subgroup G))))) :
    ⁅M,(pCore 2 (twoResidualAmbient (⊤ : Subgroup G))).map
      (twoResidualAmbient (⊤ : Subgroup G)).subtype⁆ = ⊥ := by
  let R := twoResidualAmbient (⊤ : Subgroup G)
  let Q := (pCore 2 R).map R.subtype
  let C := M ⊔ Z
  have hAC : ⁅A,C⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro a ha c hc
    obtain ⟨m,hm,z,hz,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [mul_assoc,mul_assoc]
    exact Z.mul_mem
      ((by rw [Subgroup.commutator_comm]; exact hMA : ⁅A,M⁆ ≤ Z)
        (Subgroup.commutator_mem_commutator ha hm))
      (by simpa only [mul_assoc] using ((inferInstance : Z.Normal).conj_mem _
        (Subgroup.commutator_le_right A Z (Subgroup.commutator_mem_commutator ha hz)) m))
  have hRC : ⁅R,C⁆ ≤ Z := twoResidual_commutator_le_of_normalizing_two_supplement
    C Z A T ⊤ Subgroup.le_normalizer_of_normal hAT hT hAC
  have hMR : ⁅M,R⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl le_sup_left).trans hRC
  have hCQ : ⁅C,Q⁆ = ⁅M,Q⁆ := by
    apply le_antisymm _ (Subgroup.commutator_mono le_sup_left le_rfl)
    apply Subgroup.commutator_le.mpr
    intro c hc q hq
    obtain ⟨m,hm,z,hz,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
    have hzq : ⁅z,q⁆ = 1 := by
      have hh := Subgroup.commutator_mem_commutator hz hq
      rw [hZQ] at hh
      exact hh
    rw [commutatorElement_mul_left_eq_conj_mul,hzq]
    simpa using Subgroup.commutator_mem_commutator hm hq
  have hQn : Q.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer (show Q ≤ ⊤ from le_top)).mp
    exact SectionsFiveToSeven.SevenSix.twoCoreIn_normal_of_normal R ⊤
      (Subgroup.map_subtype_le _) (SectionsFiveToSeven.SevenSix.twoResidualIn_normal ⊤)
  let N := ⁅M,Q⁆
  have hNn : N.Normal := by
    change (⁅M,Q⁆).Normal
    rw [← hCQ]
    let _ : Q.Normal := hQn
    infer_instance
  have hNM : N ≤ M := Subgroup.le_normalizer_iff_commutator_le_left.mp hQM
  have hBN : ⁅B,N⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hNM le_rfl).trans_eq hMB)
  let _ : N.Normal := hNn
  have hRN := twoResidual_centralizes_of_normalizing_two_supplement N B U ⊤
    Subgroup.le_normalizer_of_normal hBU hU hBN
  apply residual_core_centralizes_of_triple_commutators M R
    (twoResidualAmbient_has_top_twoResidual ⊤) hodd
  · exact le_bot_iff.mp ((Subgroup.commutator_mono hMR le_rfl).trans_eq hZQ)
  · simpa only [Subgroup.commutator_comm] using hRN
end Stellmacher.SectionEight
