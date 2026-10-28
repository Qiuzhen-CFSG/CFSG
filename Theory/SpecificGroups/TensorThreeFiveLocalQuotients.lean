module

public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Structure
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Small local quotients of the S₃ times five-point tensor actors

The quotient S₄ → S₃ acts on the three double transpositions. Its two-group
kernel gives (S₃ × S₄)/O₂(S₃ × S₄) ≃ S₃ × S₃. In the alternating case,
(C₂ × A₄)/O₂(C₂ × A₄) has order three. Both S₃ × S₅ and S₃ × A₅ have
three-core of order three, by the normal subgroup structure of their factors.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 14.4.10(1),(5), printed pp.1010–1011. The placement of the actual
subgroups in these models is a separate, source-specific obligation.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.TensorThreeFive
abbrev S3 := Equiv.Perm (Fin 3)
abbrev S4 := Equiv.Perm (Fin 4)
abbrev C2 := Equiv.Perm (Fin 2)
abbrev A4 := alternatingGroup (Fin 4)

/-- The identity on S₃ times the action of S₄ on its three double transpositions. -/
def overlapMap : S3 × S4 →* S3 × S3 :=
  (MonoidHom.id S3).prodMap Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom

theorem overlapMap_surjective : Function.Surjective overlapMap := by
  rintro ⟨x,y⟩
  obtain ⟨z,rfl⟩ := Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective y
  exact ⟨(x,z),rfl⟩

theorem overlapMap_kernel : overlapMap.ker =
    (⊥ : Subgroup S3).prod Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
  ext x
  change (x.1, Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom x.2) = 1 ↔ _
  simp only [Prod.mk_eq_one, mem_prod, mem_bot, MonoidHom.mem_ker]

theorem overlapMap_kernel_isP : IsPGroup 2 overlapMap.ker := by
  apply IsPGroup.of_card (n := 2)
  rw [overlapMap_kernel, Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
    Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]
  simp

theorem overlapMap_kernel_eq : overlapMap.ker = pCore 2 (S3 × S4) := by
  have h := overlapMap.comap_pCore_of_ker_isPGroup overlapMap_surjective overlapMap_kernel_isP
  rw [SymmetricThreeProduct.twoCore_eq_bot] at h
  exact h

/-- The whole two-core quotient of S₃ × S₄, with its natural coordinate map. -/
noncomputable def overlapEquiv : (S3 × S4) ⧸ pCore 2 (S3 × S4) ≃* S3 × S3 :=
  (QuotientGroup.quotientMulEquivOfEq overlapMap_kernel_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective overlapMap overlapMap_surjective)

theorem twoCore_C2 : pCore 2 C2 = ⊤ := by
  apply top_unique
  apply le_sSup
  refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
  rw [Nat.card_congr (topEquiv : (⊤ : Subgroup C2) ≃* C2).toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The two-core quotient of C₂ × A₄ has order three, so cannot be S₃. -/
theorem small_quotient_card : Nat.card ((C2 × A4) ⧸ pCore 2 (C2 × A4)) = 3 := by
  have hc : Nat.card (pCore 2 (C2 × A4)) = 8 := by
    rw [pCore_prod, twoCore_C2, AlternatingFourPair.twoCore_eq_kleinFour,
      Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
      alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num),
      Nat.card_congr (topEquiv : (⊤ : Subgroup C2) ≃* C2).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hg : Nat.card (C2 × A4) = 24 := by
    rw [Nat.card_prod, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have h := (pCore 2 (C2 × A4)).card_mul_index
  rw [index_eq_card, hc, hg] at h
  omega

/-- The normal alternating three-subgroup is the three-core of S₃ in order. -/
theorem s3_threeCore_card : Nat.card (pCore 3 S3) = 3 := by
  have hA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup]; norm_num
  have hle : alternatingGroup (Fin 3) ≤ pCore 3 S3 :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa using hA)⟩
  have hlo := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hd : Nat.card (pCore 3 S3) ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      (pCore 3 S3).card_subgroup_dvd_card
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := S3)).exists_card_eq
  have hcop : Nat.Coprime (Nat.card (pCore 3 S3)) 2 := by
    rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_left n
  have hd3 : Nat.card (pCore 3 S3) ∣ 3 := hcop.dvd_mul_left.mp hd
  have hhi := Nat.le_of_dvd (by decide : 0 < 3) hd3
  rw [hA] at hlo
  exact le_antisymm hhi hlo

/-- A nontrivial normal subgroup of S₅ contains A₅, whose order is even. -/
theorem s5_threeCore_eq_bot : pCore 3 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 3 (Equiv.Perm (Fin 5))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]; norm_num
  have hd : 60 ∣ Nat.card (pCore 3 (Equiv.Perm (Fin 5))) := hc ▸ card_dvd_of_le hle
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := Equiv.Perm (Fin 5))).exists_card_eq
  have hh : 2 ∣ 3 ^ n := hn ▸ dvd_trans (by decide : 2 ∣ 60) hd
  exact (by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow hh)

/-- Simplicity and even order exclude a nontrivial normal three-subgroup of A₅. -/
theorem a5_threeCore_eq_bot : pCore 3 (alternatingGroup (Fin 5)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : (pCore 3 (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := alternatingGroup (Fin 5))).exists_card_eq
    rw [h, Nat.card_congr (topEquiv : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≃* _).toEquiv,
      nat_card_alternatingGroup] at hn
    norm_num at hn
    have hh : 2 ∣ 3 ^ n := hn ▸ (by decide : 2 ∣ 60)
    exact False.elim ((by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow hh))

/-- Both concrete tensor actors have a three-core of order three. The
identification uses a genuine group isomorphism. -/
theorem tensor_threeCore_card {D : Type*} [Group D]
    (he : Nonempty (D ≃* S3 × Equiv.Perm (Fin 5)) ∨
      Nonempty (D ≃* S3 × alternatingGroup (Fin 5))) : Nat.card (pCore 3 D) = 3 := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr ((e.subgroupMap (pCore 3 D)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 3 e))).toEquiv,
      pCore_prod, s5_threeCore_eq_bot,
      Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, s3_threeCore_card]
    simp
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr ((e.subgroupMap (pCore 3 D)).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 3 e))).toEquiv,
      pCore_prod, a5_threeCore_eq_bot,
      Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, s3_threeCore_card]
    simp
end Theory.SpecificGroups.TensorThreeFive

end
