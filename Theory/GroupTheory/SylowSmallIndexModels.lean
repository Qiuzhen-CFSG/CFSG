module

public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.SpecificGroups.SymmetricFive.NoForty
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki

/-!
# Models of nonnormal Sylow two-subgroups of index three or five

The coset action has kernel equal to the two-core. For index five its
faithful quotient embeds in S₅; Sylow counting and the absence of an
order-forty subgroup leave orders ten and twenty. The former is dihedral:
an involution must invert the normal subgroup of order five, since
centralization would give a nontrivial normal two-subgroup. The latter is
the concrete Sz(2), by the five-normalizer recognition.

Source application: Aschbacher–Smith 14.3.5, printed p.991.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A group of order ten with trivial two-core is the dihedral group. -/
theorem equiv_dihedral_of_card_ten (hGcard : Nat.card G = 10) (hcore : pCore 2 G = ⊥) :
    Nonempty (G ≃* DihedralGroup 5) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 (hGcard ▸ (by decide : 5 ∣ 10))
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (hGcard ▸ (by decide : 2 ∣ 10))
  have hgen : closure ({c,t} : Set G) = ⊤ := by
    apply eq_top_of_card_eq
    apply Nat.dvd_antisymm
    · exact card_subgroup_dvd_card _
    · rw [hGcard]
      apply (by decide : Nat.Coprime 2 5).mul_dvd_of_dvd_of_dvd
      · simpa only [orderOf_mk, ht] using
          orderOf_dvd_natCard (⟨t,subset_closure (by simp)⟩ : closure ({c,t} : Set G))
      · simpa only [orderOf_mk, hc] using
          orderOf_dvd_natCard (⟨c,subset_closure (by simp)⟩ : closure ({c,t} : Set G))
  have hi : (zpowers c).index = 2 := by
    have hh := (zpowers c).card_mul_index
    rw [Nat.card_zpowers,hc,hGcard] at hh
    omega
  let : (zpowers c).Normal := normal_of_index_eq_two hi
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hinv : t * c * t⁻¹ = c⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one (zpowers c)
      (by rw [Nat.card_zpowers,hc]; decide) t ht2
      (show t ∈ normalizer (zpowers c : Set G) from le_normalizer_of_normal (mem_top t)) with hh | hh
    · have hct : Commute c t := (hh c (mem_zpowers c)).symm
      have hn : (zpowers t).Normal := by
        apply normalizer_eq_top_iff.mp
        apply top_unique
        rw [←hgen]
        apply (closure_le _).mpr
        intro x hx
        rcases Set.mem_insert_iff.mp hx with rfl | hx
        · apply centralizer_le_normalizer
          intro y hy
          obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
          exact (hct.zpow_right n).eq.symm
        · rw [Set.mem_singleton_iff.mp hx]
          exact le_normalizer (mem_zpowers t)
      have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers,ht]; decide)
      have hle : zpowers t ≤ pCore 2 G := le_sSup ⟨hn,hp⟩
      have ht1 : t = 1 := (show t ∈ (⊥ : Subgroup G) from hcore ▸ hle (mem_zpowers t))
      simp [ht1] at ht
    · exact hh c (mem_zpowers c)
  exact dihedralGroup_equiv_of_presentation (by decide) c t hc ht2 hinv hgen hGcard

/-- A nonnormal Sylow two-subgroup of index five gives D₁₀ or the actual Sz(2). -/
theorem sylow_index_five_core_quotient (S : Sylow 2 G)
    (hi : S.index = 5) (hproper : pCore 2 G < (S : Subgroup G)) :
    Nonempty ((G ⧸ pCore 2 G) ≃* DihedralGroup 5) ∨
      Nonempty ((G ⧸ pCore 2 G) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  classical
  let K := pCore 2 G
  have hcore : (S : Subgroup G).normalCore = K := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance,S.isPGroup'.to_le (S : Subgroup G).normalCore_le⟩
    · exact normal_le_normalCore.mpr (pCore_isPGroup.le_sylow_of_normal S)
  let pts := G ⧸ (S : Subgroup G)
  let action := MulAction.toPermHom G pts
  have hk : action.ker = K := (S : Subgroup G).normalCore_eq_ker.symm.trans hcore
  let f := QuotientGroup.lift K action hk.ge
  have hf : Function.Injective f := (QuotientGroup.injective_lift_iff K action hk.ge).mpr hk.symm
  have hp : Nat.card pts = 5 := hi
  let _ := Fintype.ofFinite pts
  have hperm : Nat.card (Equiv.Perm pts) = 120 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,←Nat.card_eq_fintype_card,hp]
    decide
  have hd : Nat.card (G ⧸ K) ∣ 120 := hperm ▸ card_dvd_of_injective f hf
  have hnot40 : Nat.card (G ⧸ K) ≠ 40 := by
    have hh := SymmetricFive.subgroup_card_ne_forty_of_card_five hp f.range
    rwa [Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨(fun x y h => hf (congrArg Subtype.val h)),f.rangeRestrict_surjective⟩).toEquiv.symm] at hh
  let P := S.mapSurjective (QuotientGroup.mk'_surjective K)
  have hPi : P.index = 5 := ((S : Subgroup G).index_map_eq
    (QuotientGroup.mk'_surjective K) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)).trans hi
  have hcount := (P : Subgroup (G ⧸ K)).index_mul_card
  rw [hPi] at hcount
  have hPdvd : Nat.card P ∣ 24 := by
    rw [←hcount] at hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 5)).mp hd
  have hcop : (Nat.card P).Coprime 3 := by
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hPdvd8 : Nat.card P ∣ 8 := hcop.dvd_mul_right.mp hPdvd
  have hlarge : 5 < Nat.card (G ⧸ K) := by
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hKcard : Nat.card K < Nat.card (S : Subgroup G) := by
      apply lt_of_not_ge
      intro hh
      exact hproper.ne (eq_of_le_of_card_ge hproper.le hh)
    have hKcount := K.index_mul_card
    change Nat.card (G ⧸ K) * Nat.card K = Nat.card G at hKcount
    have hScount := (S : Subgroup G).index_mul_card
    rw [hi] at hScount
    nlinarith
  have hcard : Nat.card (G ⧸ K) = 10 ∨ Nat.card (G ⧸ K) = 20 := by
    obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card P ∣ 2 ^ 3 from hPdvd8)
    interval_cases n <;> norm_num only [pow_zero, pow_succ, Nat.reduceMul] at he <;>
      rw [he] at hcount <;> omega
  have hqcore : pCore 2 (G ⧸ K) = ⊥ := by
    let q := QuotientGroup.mk' K
    have hq := QuotientGroup.mk'_surjective K
    have hh := q.comap_pCore_of_ker_isPGroup hq
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    have hm := congrArg (map q) hh
    rw [map_comap_eq_self_of_surjective hq] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  exact hcard.elim (fun h => Or.inl (equiv_dihedral_of_card_ten h hqcore))
    (fun h => Or.inr (Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.equiv_suzuki_of_card_twenty h hqcore))
/-- The three actual quotient models for nonnormal Sylow index three or five. -/
theorem sylow_small_index_core_quotient (S : Sylow 2 G)
    (hi : S.index = 3 ∨ S.index = 5) (hproper : pCore 2 G < (S : Subgroup G)) :
    Nonempty ((G ⧸ pCore 2 G) ≃* DihedralGroup 5) ∨
      Nonempty ((G ⧸ pCore 2 G) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
      Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) := by
  rcases hi with hi | hi
  · exact Or.inr (Or.inr (sylow_index_three_core_quotient S hi hproper))
  · exact (sylow_index_five_core_quotient S hi hproper).elim Or.inl (Or.inr ∘ Or.inl)

end Theory.GroupTheory
