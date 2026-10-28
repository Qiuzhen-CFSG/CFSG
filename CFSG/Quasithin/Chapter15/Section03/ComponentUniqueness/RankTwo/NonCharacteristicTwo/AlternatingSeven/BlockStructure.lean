module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.AlternatingSeven.PartitionReduction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.AlternatingSeven.FourPoint
public import Theory.GroupTheory.PPerfectHom

/-!
# The actual A₄ × C₃ subgroup in the (4,3)-partition

Two-perfectness kills both block signs. The factor of nine puts the normal
three-point factor in the subgroup, so it splits as its four-point projection
times C₃. That projection contains a nonidentity cubic element and is invariant
under (01)(23); the bounded four-point calculation makes it all of A₄.

The permutation identification uses exactly the coordinate change supplied
by the solvable Sylow-overgroup theorem. Its center has order three, so it
is characteristic and supplies the actual normal subgroup used by 15.3.42.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.42,
printed p.1138.
-/

public section

open Subgroup Equiv Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven
open LocalGeometry.PermutationOvergroups PartitionObstruction

@[expose] def blockAlternating : Subgroup FourThree :=
  (alternatingGroup (Fin 4)).prod (alternatingGroup (Fin 3))

@[expose] def blockAlternatingImage : Subgroup S7 := blockAlternating.map fourThreeHom

private theorem card_a3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num

private theorem twoPerfect_le_blockAlternating (U : Subgroup FourThree)
    (hp : IsPPerfect 2 U) : U ≤ blockAlternating := by
  have h2 : IsPGroup 2 ℤˣ := IsPGroup.of_card (by
    rw [Nat.card_eq_fintype_card]
    decide : Nat.card ℤˣ = 2 ^ 1)
  have h₁ := hp.hom_eq_one_of_isPGroup h2
    (Perm.sign.comp ((MonoidHom.fst _ _).comp U.subtype))
  have h₂ := hp.hom_eq_one_of_isPGroup h2
    (Perm.sign.comp ((MonoidHom.snd _ _).comp U.subtype))
  intro u hu
  exact ⟨Perm.mem_alternatingGroup.mpr (DFunLike.congr_fun h₁ ⟨u, hu⟩),
    Perm.mem_alternatingGroup.mpr (DFunLike.congr_fun h₂ ⟨u, hu⟩)⟩

private theorem product_of_contains_threeFactor (U : Subgroup FourThree)
    (hU : U ≤ blockAlternating) (hC : threeFactor ≤ U) :
    U = (U.map (MonoidHom.fst _ _)).prod (alternatingGroup (Fin 3)) := by
  apply le_antisymm
  · intro u hu
    exact ⟨mem_map_of_mem _ hu, (hU hu).2⟩
  · rintro ⟨g, c⟩ ⟨⟨u, hu, hgu⟩, hc⟩
    change u.1 = g at hgu
    have hm : (1, u.2⁻¹ * c) ∈ U := hC ⟨rfl,
      (alternatingGroup (Fin 3)).mul_mem
        ((alternatingGroup (Fin 3)).inv_mem (hU hu).2) hc⟩
    have hprod := U.mul_mem hu hm
    simpa only [Prod.mul_def, mul_one, mul_inv_cancel_left, hgu] using hprod

private theorem firstProjection_eq_alternating (U : Subgroup FourThree)
    (hU : U ≤ blockAlternating) (hC : threeFactor ≤ U) (h9 : 9 ∣ Nat.card U)
    (hn : (doubleSwap, 1) ∈ normalizer (U : Set FourThree)) :
    U.map (MonoidHom.fst _ _) = alternatingGroup (Fin 4) := by
  let F := U.map (MonoidHom.fst _ _)
  have hprod := product_of_contains_threeFactor U hU hC
  have h3 : 3 ∣ Nat.card F := by
    have hc : Nat.card U = Nat.card F * 3 := by
      rw [hprod, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, card_a3]
    obtain ⟨k, hk⟩ := h9
    refine ⟨k, ?_⟩
    rw [hc] at hk
    omega
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := F) 3 h3
  have hf3 : (f.val : Perm (Fin 4)) ^ 3 = 1 := by
    have h : f ^ 3 = 1 := hf ▸ pow_orderOf_eq_one f
    exact congrArg Subtype.val h
  have hfne : f.val ≠ 1 := by
    intro he
    have : f = 1 := Subtype.ext he
    simp only [this, orderOf_one] at hf
    omega
  obtain ⟨u, hu, huf⟩ := f.property
  have hconj : doubleSwap * f.val * doubleSwap⁻¹ ∈ F := by
    refine ⟨(doubleSwap, 1) * u * (doubleSwap, 1)⁻¹, (hn u).mp hu, ?_⟩
    change doubleSwap * u.1 * doubleSwap⁻¹ = _
    rw [show u.1 = f.val from huf]
  apply le_antisymm
  · rintro g ⟨u, hu, rfl⟩
    exact (hU hu).1
  · intro g hg
    obtain ⟨i, j, k, he⟩ := fourPoint_generation f.val hf3 hfne g
      (Perm.mem_alternatingGroup.mp hg)
    rw [he]
    exact F.mul_mem (F.mul_mem (F.pow_mem f.property _) (F.pow_mem hconj _))
      (F.pow_mem f.property _)

/-- The intrinsic product is forced by two-perfectness, nine, and one
specified Sylow involution. No product structure is included in the inputs. -/
theorem block_structure (U : Subgroup FourThree)
    (hp : IsPPerfect 2 U) (hC : threeFactor ≤ U) (h9 : 9 ∣ Nat.card U)
    (hn : (doubleSwap, 1) ∈ normalizer (U : Set FourThree)) : U = blockAlternating := by
  have hU := twoPerfect_le_blockAlternating U hp
  rw [product_of_contains_threeFactor U hU hC,
    firstProjection_eq_alternating U hU hC h9 hn]
  rfl

/-- The source A₄ × C₃ structure as an actual permutation subgroup,
assuming only already established compatible partition placement. -/
theorem image_eq_blockAlternating (H : Subgroup S7)
    (hH : H ≤ fourThreeStabilizer) (hp : IsPPerfect 2 H) (h9 : 9 ∣ Nat.card H)
    (hn : standardEvenTwo.map (alternatingGroup (Fin 7)).subtype ≤ normalizer (H : Set S7)) :
    H = blockAlternatingImage := by
  let U := H.comap fourThreeHom
  have hmap : U.map fourThreeHom = H := map_comap_eq_self hH
  let e : U ≃* H := (U.equivMapOfInjective fourThreeHom fourThreeHom_injective).trans
    (MulEquiv.subgroupCongr hmap)
  have hpU : IsPPerfect 2 U := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have h9U : 9 ∣ Nat.card U := by rwa [Nat.card_congr e.toEquiv]
  let J := H.subgroupOf fourThreeStabilizer
  have h9J : 9 ∣ Nat.card J := by rw [Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv]; exact h9
  have hCJ := contains_threeCycles_of_nine J h9J
  have hC : threeFactor ≤ U := by
    intro u hu
    have h : fourThreeEquiv u ∈ threeCycles := mem_map_of_mem fourThreeEquiv.toMonoidHom hu
    exact hCJ h
  have hnU : (doubleSwap, 1) ∈ normalizer (U : Set FourThree) := by
    have ha : fourThreeHom (doubleSwap, 1) ∈ normalizer (H : Set S7) :=
      hn ⟨⟨fourThreeHom (doubleSwap, 1), doubleSwap_standard.2⟩, doubleSwap_standard.1, rfl⟩
    intro u
    change fourThreeHom u ∈ H ↔ fourThreeHom ((doubleSwap, 1) * u * (doubleSwap, 1)⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv]
    exact ha (fourThreeHom u)
  have he := block_structure U hpU hC h9U hnU
  rw [← hmap, he]
  rfl

noncomputable def blockAlternatingEquiv : blockAlternating ≃*
    (alternatingGroup (Fin 4) × Multiplicative (ZMod 3)) :=
  (Subgroup.prodEquiv _ _).trans ((MulEquiv.refl _).prodCongr
    (mulEquivOfPrimeCardEq card_a3 (Nat.card_zmod 3)))

/-- Solvability and rank give the partition; Sylow invariance and
O²(Q) = Q then determine the subgroup in those same coordinates. -/
theorem model_structure (Q : Subgroup (alternatingGroup (Fin 7)))
    (P : Sylow 2 (alternatingGroup (Fin 7)))
    [Group.IsSolvable (Q ⊔ (P : Subgroup (alternatingGroup (Fin 7))) : Subgroup _)]
    (hn : (P : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (Q : Set _))
    (hp : IsPPerfect 2 Q) (hrank : primeRank 3 Q = 2) :
    ∃ σ : S7, Q.map ((MulAut.conj σ).toMonoidHom.comp
      (alternatingGroup (Fin 7)).subtype) = blockAlternatingImage := by
  obtain ⟨σ, hplace, hP⟩ := fourThree_placement Q P hrank
  let ψ := (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype
  have hψ : Function.Injective ψ :=
    (MulAut.conj σ).injective.comp (alternatingGroup (Fin 7)).subtype_injective
  have hH : Q.map ψ ≤ fourThreeStabilizer := (map_mono le_sup_left).trans hplace
  have hpH : IsPPerfect 2 (Q.map ψ) :=
    hp.of_surjective (ψ.subgroupMap Q) (ψ.subgroupMap_surjective Q)
  have h9 : 9 ∣ Nat.card (Q.map ψ) := by
    rw [card_map_of_injective hψ]
    exact nine_dvd_of_threeRank_two hrank
  have hnH : standardEvenTwo.map (alternatingGroup (Fin 7)).subtype ≤
      normalizer (Q.map ψ : Set S7) := by
    rw [← hP]
    exact (map_mono hn).trans (Q.le_normalizer_map ψ)
  exact ⟨σ, image_eq_blockAlternating (Q.map ψ) hH hpH h9 hnH⟩

/-- The marked permutation identification gives the source abstract product. -/
theorem model_equiv_a4_c3 (Q : Subgroup (alternatingGroup (Fin 7)))
    (P : Sylow 2 (alternatingGroup (Fin 7)))
    [Group.IsSolvable (Q ⊔ (P : Subgroup (alternatingGroup (Fin 7))) : Subgroup _)]
    (hn : (P : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (Q : Set _))
    (hp : IsPPerfect 2 Q) (hrank : primeRank 3 Q = 2) :
    Nonempty (Q ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 3))) := by
  obtain ⟨σ, he⟩ := model_structure Q P hn hp hrank
  let ψ := (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype
  have hψ : Function.Injective ψ :=
    (MulAut.conj σ).injective.comp (alternatingGroup (Fin 7)).subtype_injective
  exact ⟨(Q.equivMapOfInjective ψ hψ).trans ((MulEquiv.subgroupCongr he).trans
    ((blockAlternating.equivMapOfInjective fourThreeHom fourThreeHom_injective).symm.trans
      blockAlternatingEquiv))⟩

/-- In the identified product, the three-point factor is its whole center. -/
theorem center_card_of_equiv_a4_c3 {H : Type*} [Group H]
    (e : H ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 3))) :
    Nat.card (center H) = 3 := by
  rw [Nat.card_congr (centerCongr e).toEquiv, Subgroup.center_prod,
    alternatingGroup.center_eq_bot (by norm_num), center_eq_top,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_bot, card_top, one_mul]
  exact Nat.card_zmod 3

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.AlternatingSeven
