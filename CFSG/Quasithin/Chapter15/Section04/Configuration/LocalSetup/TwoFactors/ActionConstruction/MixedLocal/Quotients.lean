module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.LocalSylow
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The symmetric quotients and intersection of the mixed local groups

The source factor quotient has order three. Its two-core lies in the earlier
Sylow subgroup `S`, hence in the stabilizer `U`. The normalized-product index
formula gives `[YU:U]=3`. The identity `Y=[Y,J(T)]` excludes a normal Sylow
subgroup, so the faithful three-coset action identifies `YU/O₂(YU)` with `S₃`.
Two distinct overgroups with the same subgroup of index three intersect exactly
in that subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 15.4.12(4),(6) and the first three paragraphs of
15.4.18, printed pp.1160–1162. The earlier Sylow witness is for `YS`, not for
the mixed centralizer or generated group.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem index_join_of_normalizes {Y U : Subgroup G}
    (hn : U ≤ normalizer (Y : Set G)) : U.relIndex (Y ⊔ U) = U.relIndex Y := by
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes Y U hn
  have hY := relIndex_mul_relIndex (⊥ : Subgroup G) (Y ⊓ U) Y bot_le inf_le_left
  have hU := relIndex_mul_relIndex (⊥ : Subgroup G) U (Y ⊔ U) bot_le le_sup_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left] at hY
  rw [relIndex_bot_left, relIndex_bot_left] at hU
  rw [← hY, ← hU] at hp
  have hpos : 0 < Nat.card (Y ⊓ U : Subgroup G) * Nat.card U :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  nlinarith [hp]

omit [Finite G] in
/-- The earlier Sylow witness in `YS` places the actual two-core of `Y`
in `S`, using only normality inside `YS`. -/
theorem factor_core_le_earlier_sylow {Y S : Subgroup G}
    (hn : S ≤ normalizer (Y : Set G))
    (P : Sylow 2 (Y ⊔ S : Subgroup G))
    (hP : (P : Subgroup (Y ⊔ S : Subgroup G)).map (Y ⊔ S : Subgroup G).subtype = S) :
    Y.pCoreIn 2 ≤ S := by
  have hcore : Y.pCoreIn 2 ≤ (Y ⊔ S : Subgroup G).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y)
      ((pCoreIn_le 2 Y).trans le_sup_left)
      ((sup_le Y.le_normalizer hn).trans
        (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)))
  have hs := pCoreIn_le_sylow (Y ⊔ S) P
  rw [hP] at hs
  exact hcore.trans hs

/-- A factor with cyclic-three two-core quotient and `Y=[Y,J]` yields the
actual symmetric-three quotient of `YU`. The earlier Sylow witness concerns
`YS`; the required Sylow subgroup of `YU` and its coset action are constructed. -/
theorem factor_join_symmetric_quotient {Y S U J : Subgroup G}
    (hU : IsPGroup 2 U) (hSU : S ≤ U) (hJS : J ≤ S)
    (hn : U ≤ normalizer (Y : Set G))
    (hY : ⁅Y, J⁆ = Y) (hindex : (pCore 2 Y).index = 3)
    (P : Sylow 2 (Y ⊔ S : Subgroup G))
    (hP : (P : Subgroup (Y ⊔ S : Subgroup G)).map (Y ⊔ S : Subgroup G).subtype = S) :
    U.relIndex (Y ⊔ U) = 3 ∧
    (∃ Q : Sylow 2 (Y ⊔ U : Subgroup G),
      (Q : Subgroup (Y ⊔ U : Subgroup G)).map (Y ⊔ U : Subgroup G).subtype = U) ∧
    Nonempty (((Y ⊔ U : Subgroup G) ⧸ pCore 2 (Y ⊔ U : Subgroup G)) ≃*
      Equiv.Perm (Fin 3)) := by
  have hcU := (factor_core_le_earlier_sylow (hSU.trans hn) P hP).trans hSU
  have hnot : ¬ Y ≤ U := by
    intro hy
    obtain ⟨n, hcard⟩ := (hU.to_le hy).exists_card_eq
    have hd : 3 ∣ Nat.card Y := hindex ▸ (pCore 2 Y).index_dvd_card
    rw [hcard] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hd : U.relIndex Y ∣ 3 := by
    rw [← hindex]
    apply index_dvd_of_le
    intro y hy
    exact hcU (mem_map.mpr ⟨y, hy, rfl⟩)
  have hi : U.relIndex (Y ⊔ U) = 3 := by
    rw [index_join_of_normalizes hn]
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact (hnot (relIndex_eq_one.mp h)).elim
    · exact h
  obtain ⟨Q, hQ⟩ := hU.exists_sylow_sup_of_coprime_index Y U hn (pCore 2 Y)
    (by rw [hindex]; decide) hcU
  have hQU : (Q : Subgroup (Y ⊔ U : Subgroup G)) = U.subgroupOf (Y ⊔ U) := by
    have he := congrArg (fun A : Subgroup G => A.subgroupOf (Y ⊔ U)) hQ
    change ((Q : Subgroup (Y ⊔ U : Subgroup G)).map (Y ⊔ U : Subgroup G).subtype).comap
      (Y ⊔ U : Subgroup G).subtype = U.subgroupOf (Y ⊔ U) at he
    rw [comap_map_eq_self_of_injective (Y ⊔ U : Subgroup G).subtype_injective] at he
    exact he
  have hQi : (Q : Subgroup (Y ⊔ U : Subgroup G)).index = 3 := by
    rw [hQU]
    exact hi
  have hproper : pCore 2 (Y ⊔ U : Subgroup G) < (Q : Subgroup (Y ⊔ U : Subgroup G)) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal Q)
    intro heq
    have hcore : (Y ⊔ U : Subgroup G).pCoreIn 2 = U := by
      change (pCore 2 (Y ⊔ U : Subgroup G)).map (Y ⊔ U : Subgroup G).subtype = U
      rw [heq, hQ]
    have hnormU : Y ⊔ U ≤ normalizer (U : Set G) := by
      have hncore : Y ⊔ U ≤ normalizer ((Y ⊔ U : Subgroup G).pCoreIn 2 : Set G) := by
        simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
          using (pCore 2 (Y ⊔ U : Subgroup G)).le_normalizer_map (Y ⊔ U : Subgroup G).subtype
      rwa [hcore] at hncore
    apply hnot
    rw [← hY]
    exact (commutator_mono le_rfl (hJS.trans hSU)).trans
      (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hnormU))
  exact ⟨hi, ⟨Q, hQ⟩, sylow_index_three_core_quotient Q hQi hproper⟩

omit [Finite G] in
/-- Two distinct groups with the same subgroup of index three intersect
in precisely that subgroup. -/
theorem intersection_of_common_index_three {A B U : Subgroup G}
    (hUA : U ≤ A) (hUB : U ≤ B)
    (hiA : U.relIndex A = 3) (hiB : U.relIndex B = 3) (hne : A ≠ B) :
    A ⊓ B = U := by
  have hUI : U ≤ A ⊓ B := le_inf hUA hUB
  have hA := relIndex_mul_relIndex U (A ⊓ B) A hUI inf_le_left
  have hB := relIndex_mul_relIndex U (A ⊓ B) B hUI inf_le_right
  rw [hiA] at hA
  rw [hiB] at hB
  have hd : U.relIndex (A ⊓ B) ∣ 3 := dvd_of_mul_right_eq _ hA
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact le_antisymm (relIndex_eq_one.mp h) hUI
  · rw [h] at hA hB
    have ha : (A ⊓ B).relIndex A = 1 := by omega
    have hb : (A ⊓ B).relIndex B = 1 := by omega
    exact (hne (le_antisymm ((relIndex_eq_one.mp ha).trans inf_le_right)
      ((relIndex_eq_one.mp hb).trans inf_le_left))).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
