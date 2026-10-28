module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.ResidualProduct
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.Preliminary

/-!
# The actual alternating-square obstruction in 15.3.43(d)

Assume the selected actor `Y₊` is isomorphic to `A₄`. Its order-four
commutator plane exhausts its intersection with the two-core of `YT`.
The opposite-plane actor is its actual conjugate by `t`. The source
core geometry makes these actors commute, and their disjoint cubic
images generate the joint-plane action quotient. Lifting through the
Frattini subgroup in the two alternatives of 15.3.7, and then using
two-perfectness, proves that they generate `Y` itself. Multiplication
therefore gives the forbidden `A₄ × A₄` isomorphism.

The intrinsic core-action and generation lemmas are shared with the
residual-product proof of 15.3.40. Here the actor is `Y₊` itself, and
no rank-two hypothesis or conclusion `Y = Y₊` is used. The plane action
and core geometry in the signatures still have to be supplied from the
genuine earlier local setup; these lemmas do not construct that setup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(d), printed p.1139, using 15.3.7 and 15.3.9, pp.1122--1123.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
open RankTwo.ResidualProduct
variable {G D : Type*} [Group G] [Group D]

/-- Commutation, disjointness and generation construct the actual direct-product isomorphism. -/
theorem alternating_square_of_rank_one_local_geometry [Finite G] [Finite D]
    {Y Yplus S T U W : Subgroup G}
    (f : Y →* D) (hD : Nat.card D = 9)
    (hk : f.ker = (centralizer (U ⊔ W : Subgroup G)).subgroupOf Y)
    (hquot : QuotientAlternatives Y f)
    (hY : IsPPerfect 2 Y) (hplusPerfect : IsPPerfect 2 Yplus) (hplusY : Yplus ≤ Y)
    (hT : T ≤ normalizer (Y : Set G))
    (hRS : (Y ⊔ T).pCoreIn 2 ≤ S)
    (hself : Y ⊓ centralizer ((Y ⊔ T).pCoreIn 2 : Set G) ≤ (Y ⊔ T).pCoreIn 2)
    (hUR : U ≤ (Y ⊔ T).pCoreIn 2) (hWR : W ≤ (Y ⊔ T).pCoreIn 2)
    (hU : Nat.card U = 4) (hW : Nat.card W = 4) (hdUW : Disjoint U W)
    (hSA : S ≤ normalizer (Yplus : Set G))
    (hAU : Yplus ≤ centralizer (U : Set G))
    (hAW : ⁅W, Yplus⁆ = W)
    (eA : Yplus ≃* alternatingGroup (Fin 4))
    (t : G) (ht : t ∈ T)
    (hswapU : U.map (MulAut.conj t).toMonoidHom = W)
    (hswapW : W.map (MulAut.conj t).toMonoidHom = U) :
    Y = Yplus ⊔ Yplus.map (MulAut.conj t).toMonoidHom ∧
      Disjoint Yplus (Yplus.map (MulAut.conj t).toMonoidHom) ∧
      Yplus ≤ centralizer (Yplus.map (MulAut.conj t).toMonoidHom : Set G) ∧
      Nonempty (Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  let A := Yplus
  let B := A.map (MulAut.conj t).toMonoidHom
  let Q := (Y ⊔ T).pCoreIn 2
  let e := (MulAut.conj t).toMonoidHom
  have hAY : A ≤ Y := hplusY
  have hKY : Y ⊔ T ≤ normalizer (Y : Set G) := sup_le Y.le_normalizer hT
  have hKQ : Y ⊔ T ≤ normalizer (Q : Set G) :=
    (Y ⊔ T).le_normalizer.trans (normalizer_le_normalizer_characteristic_image
      (Y ⊔ T) (pCore 2 (Y ⊔ T : Subgroup G)))
  have hYQ : Y ≤ normalizer (Q : Set G) := le_sup_left.trans hKQ
  have hQt : Q.map e = Q := mem_normalizer_iff_map_conj_eq.mp (hKQ (mem_sup_right ht))
  have hYt : Y.map e = Y := mem_normalizer_iff_map_conj_eq.mp (hT ht)
  have hBY : B ≤ Y := by
    rw [← hYt]
    exact map_mono hAY
  have hQA : Q ≤ normalizer (A : Set G) := hRS.trans hSA
  have hAQ : A ≤ normalizer (Q : Set G) := hAY.trans hYQ
  have hQB : Q ≤ normalizer (B : Set G) := by
    rw [← hQt]
    exact (map_mono hQA).trans (le_normalizer_map e)
  have hBQ : B ≤ normalizer (Q : Set G) := hBY.trans hYQ
  have hWA : W ≤ A := by
    rw [← hAW]
    exact le_normalizer_iff_commutator_le_right.mp (hWR.trans hQA)
  have hUB : U ≤ B := by
    rw [← hswapW]
    exact map_mono hWA
  have hBW : B ≤ centralizer (W : Set G) := by
    rw [← hswapU]
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, commutator_eq_bot_iff_le_centralizer.mpr hAU, Subgroup.map_bot]
  have hBU : ⁅U, B⁆ = U := by
    rw [← hswapW]
    exact (map_commutator W A e).symm.trans (congrArg (Subgroup.map e) hAW)
  have hA : IsPPerfect 2 A := hplusPerfect
  have hB : IsPPerfect 2 B := hA.of_surjective
    (e.subgroupMap A) (e.subgroupMap_surjective A)
  have hQ : IsPGroup 2 Q := isPGroup_pCoreIn 2 (Y ⊔ T)
  have hcA : Nat.card A = 12 := by
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcB : Nat.card B = 12 := (card_map_of_injective (MulAut.conj t).injective).trans hcA
  have hQAeq : Q ⊓ A = W := inf_eq_plane hQ hcA hW hWR hWA
  have hQBeq : Q ⊓ B = U := inf_eq_plane hQ hcB hU hUR hUB
  have hc : A ≤ centralizer (B : Set G) := actors_commute hAY hBY hself hQ hA hB
    hQA hQB hAQ hBQ hQAeq hQBeq hAU hBW hdUW
  have hz : center A = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    apply eA.injective
    have hh : eA a ∈ center (alternatingGroup (Fin 4)) := by
      rw [mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := eA.surjective b
      simpa only [map_mul] using congrArg eA (mem_center_iff.mp ha c)
    rw [alternatingGroup.center_eq_bot (by simp)] at hh
    simpa using hh
  have hd : Disjoint A B := actors_disjoint hc hz
  have hUne : U ≠ ⊥ := by intro he; simp [he] at hU
  have hWne : W ≠ ⊥ := by intro he; simp [he] at hW
  have himage := action_image_generated f hk hAY hBY hAU hBW hc hcA hcB hD hAW hBU hUne hWne
  have hsupp := supplement_core_of_action_image f himage (by
    rcases hquot with ⟨_, _, hk⟩ | ⟨he, _, hk⟩
    · rw [hk]; exact bot_le
    · let := he
      rw [hk, IsExtraspecial.frattini_eq_center_three])
  have hsupp' : (A ⊔ B) ⊔ Y.pCoreIn 2 = Y := by
    have hh := congrArg (Subgroup.map Y.subtype) hsupp
    simpa only [pCoreIn, Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hAY hBY),
      ← MonoidHom.range_eq_map, range_subtype] using hh
  have hcoreQ : Y.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left hKY
  have hgen : Y = A ⊔ B := residual_generated hY hA hB hQ hAY hBY hQA hQB (by
    rw [← hsupp']
    exact sup_le_sup_left hcoreQ _)
  obtain ⟨esquare⟩ := RankTwo.alternating_square_of_conjugate_factors Y A t hgen hd hc eA
  exact ⟨hgen, hd, hc, ⟨esquare⟩⟩


/-- Clause (d), from the constructed direct product and the genuine exclusion 15.3.9. -/
theorem not_alternating_four_of_local_geometry [Finite G] [Finite D]
    {Y Yplus S T U W : Subgroup G}
    (f : Y →* D) (hD : Nat.card D = 9)
    (hk : f.ker = (centralizer (U ⊔ W : Subgroup G)).subgroupOf Y)
    (hquot : QuotientAlternatives Y f)
    (hY : IsPPerfect 2 Y) (hplusPerfect : IsPPerfect 2 Yplus) (hplusY : Yplus ≤ Y)
    (hT : T ≤ normalizer (Y : Set G))
    (hRS : (Y ⊔ T).pCoreIn 2 ≤ S)
    (hself : Y ⊓ centralizer ((Y ⊔ T).pCoreIn 2 : Set G) ≤ (Y ⊔ T).pCoreIn 2)
    (hUR : U ≤ (Y ⊔ T).pCoreIn 2) (hWR : W ≤ (Y ⊔ T).pCoreIn 2)
    (hU : Nat.card U = 4) (hW : Nat.card W = 4) (hdUW : Disjoint U W)
    (hSA : S ≤ normalizer (Yplus : Set G))
    (hAU : Yplus ≤ centralizer (U : Set G))
    (hAW : ⁅W, Yplus⁆ = W)
    (h9 : ¬ Nonempty (Y ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))))
    (t : G) (ht : t ∈ T)
    (hswapU : U.map (MulAut.conj t).toMonoidHom = W)
    (hswapW : W.map (MulAut.conj t).toMonoidHom = U) :
    ¬ Nonempty (Yplus ≃* alternatingGroup (Fin 4)) := by
  rintro ⟨eA⟩
  have h := alternating_square_of_rank_one_local_geometry f hD hk hquot hY
    hplusPerfect hplusY hT hRS hself hUR hWR hU hW hdUW hSA hAU hAW eA
    t ht hswapU hswapW
  exact h9 h.2.2.2

end CFSG.Quasithin.Chapter15.Section03.RankOne
