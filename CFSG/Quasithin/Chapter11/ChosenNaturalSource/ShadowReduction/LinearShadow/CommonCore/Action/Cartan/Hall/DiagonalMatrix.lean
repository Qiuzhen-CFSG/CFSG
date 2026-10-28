module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
/-!
# A split diagonal from an odd subgroup in a lifted Borel

Above a two-group kernel, Sylow conjugacy places the original subgroup
in the upper Borel. Its odd order excludes the unipotent kernel. A shear
then removes the upper-right entry of a nonidentity element. The same
conjugator is retained in the literal matrix equation used by natural
coordinate transport in 11.3.7(3).

Source: Aschbacher--Smith, 11.3.7, printed p.773; elementary SL2 calculation.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
variable {F : Type*} [Field F] [CharP F 2]
private theorem triangular_diagonal (g : SL(2,F)) (hg : g ∈ rankOneBorel F)
    (ha : g.val 0 0 ≠ 1) :
    ∃ b : SL(2,F), (b*g*b⁻¹).val = !![g.val 0 0,0;0,(g.val 0 0)⁻¹] := by
  have h10 := (mem_rankOneBorel_iff g).mp hg
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [det_fin_two,h10,mul_zero,sub_zero] using g.property
  have hz : g.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have h11 : g.val 1 1 = (g.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  have hdiff : g.val 0 0 - (g.val 0 0)⁻¹ ≠ 0 := by
    intro hh
    have he := sub_eq_zero.mp hh
    have hs : (g.val 0 0)^2 = 1 := by
      calc
        _ = g.val 0 0 * (g.val 0 0)⁻¹ := by rw [sq,←he]
        _ = 1 := mul_inv_cancel₀ hz
    have hsq : (g.val 0 0-1)^2 = 0 := by
      have htwo : (2:F)=0 := CharP.cast_eq_zero F 2
      calc
        _ = (g.val 0 0)^2 - 2*g.val 0 0 + 1 := by ring
        _ = 0 := by rw [hs,htwo,zero_mul,sub_zero]; exact CharTwo.add_self_eq_zero 1
    exact ha (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  let b := transvection (i := (0:Fin 2)) (j := 1) zero_ne_one
    (g.val 0 1 / (g.val 0 0 - (g.val 0 0)⁻¹))
  refine ⟨b,?_⟩
  have he : b*g = diag2 (g.val 0 0) hz * b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b,mul_apply,Fin.sum_univ_two,transvection_coe,diag2_coe',h10,h11]
    linear_combination -(div_mul_cancel₀ (g.val 0 1) hdiff)
  rw [he,mul_assoc,mul_inv_cancel,mul_one]
  exact diag2_coe' hz
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
open Subgroup
variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]
private theorem odd_sylow_disjoint (P : Sylow 2 A) (C : Subgroup A)
    (ho : Odd (Nat.card C)) : Disjoint (P : Subgroup A) C := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [hn]
  exact (Nat.coprime_two_left.mpr ho).pow_left n

/-- The element, conjugator and nontrivial scalar are constructed from the actual odd subgroup. -/
theorem exists_conjugate_diagonal (q : A →* SL(2,F)) (hq : Function.Surjective q)
    (P : Sylow 2 A) (hk : q.ker ≤ (P : Subgroup A)) (C : Subgroup A)
    (hn : C ≤ normalizer (P : Set A)) (ho : Odd (Nat.card C)) (hne : C ≠ ⊥) :
    ∃ d ∈ C, ∃ b : SL(2,F), ∃ a : F, a ≠ 1 ∧
      (b * q d * b⁻¹).val = !![a,0;0,a⁻¹] := by
  obtain ⟨d,hd,hd1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hd1 : d ≠ 1 := by simpa only [mem_bot] using hd1
  let R := P.mapSurjective hq
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq SL(2,F) R (upperUnipotentSylow F 2)
  let q' := (MulAut.conj b).toMonoidHom.comp q
  have hq' : Function.Surjective q' := (MulAut.conj b).surjective.comp hq
  have hP : (P : Subgroup A).map q' = upperUnipotent F := by
    dsimp only [q']
    rw [← Subgroup.map_map]
    change ((b • R : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [hb]
    rfl
  have hk' : q'.ker ≤ (P : Subgroup A) := by
    intro x hx
    apply hk
    exact (MulAut.conj b).map_eq_one_iff.mp hx
  have hroot : (upperUnipotent F).comap q' = P := by
    rw [←hP, comap_map_eq_self hk']
  have hB : q' d ∈ rankOneBorel F := by
    have hh := (P : Subgroup A).le_normalizer_map q' (mem_map_of_mem q' (hn hd))
    rwa [hP] at hh
  have ha : (q' d).val 0 0 ≠ 1 := by
    intro he
    have h10 := (mem_rankOneBorel_iff (q' d)).mp hB
    have h11 : (q' d).val 1 1 = 1 := by
      simpa only [det_fin_two,he,h10,one_mul,mul_zero,sub_zero] using (q' d).property
    have hdroot : q' d ∈ upperUnipotent F := by
      refine (mem_upperUnipotent F _).mpr ⟨(q' d).val 0 1, ?_⟩
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [transvection_coe,he,h10,h11]
    have hdP : d ∈ P := by
      change d ∈ (P : Subgroup A)
      rw [← hroot]
      exact hdroot
    exact hd1 (disjoint_def.mp (odd_sylow_disjoint P C ho) hdP hd)
  obtain ⟨u,hu⟩ := triangular_diagonal (q' d) hB ha
  refine ⟨d,hd,u*b,(q' d).val 0 0,ha,?_⟩
  have he : (u*b)*q d*(u*b)⁻¹ = u*(q' d)*u⁻¹ := by
    change (u*b)*q d*(u*b)⁻¹ = u*(b*q d*b⁻¹)*u⁻¹
    group
  rw [he]
  exact hu
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
