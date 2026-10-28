module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Natural.Permutation
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Natural.Odd

/-!
# The natural A₆ generation budget in ranks one and two

An elementary subgroup of S₆ with an even involution needs only three
A₆ conjugates, by the intrinsic involution-generation theorem. The sign
map forces an even involution in rank two. When there is no even involution,
the rank is at most one; two conjugates give an even involution and its
three generating conjugates expand to six conjugates of the original actor.
The indices are transported explicitly through Fin 3 × Fin 2 ≃ Fin 6.

Source: the group-generation route to Aschbacher–Smith K.1.1, printed p.452
(PDF p.463), citing GM02 Theorem 6.2 and Table 6.3.
-/

public section

open Equiv Subgroup Representation.BinaryOffender AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof

private theorem six_of_odd (E : Subgroup S6) (x : S6) (hxE : x ∈ E) (hx : x ≠ 1)
    (hx2 : x ^ 2 = 1) (hodd : x ∉ alternatingGroup (Fin 6)) :
    ∃ c : Fin 6 → A6, alternatingGroup (Fin 6) ≤
      ⨆ i, E.map (MulAut.conj (c i : S6)).toMonoidHom := by
  obtain ⟨k,t,ht,ht2,he⟩ := odd_difference x hx hx2 hodd
  let B := E ⊔ E.map (MulAut.conj (k : S6)).toMonoidHom
  have htB : (t : S6) ∈ B := by
    rw [he]
    have hm := B.mul_mem ((show E ≤ B from le_sup_left) hxE)
      ((show E.map (MulAut.conj (k : S6)).toMonoidHom ≤ B from le_sup_right)
        (mem_map_of_mem (MulAut.conj (k : S6)).toMonoidHom hxE))
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc] using hm
  obtain ⟨d,hd⟩ := three_of_even B t ht ht2 htB
  let e : Fin 3 × Fin 2 ≃ Fin 6 := finProdFinEquiv
  let c : Fin 6 → A6 := fun i => d (e.symm i).1 * ![1,k] (e.symm i).2
  have hc0 (i : Fin 3) : c (e (i,0)) = d i := by simp [c]
  have hc1 (i : Fin 3) : c (e (i,1)) = d i * k := by simp [c]
  refine ⟨c, hd.trans (iSup_le fun i => ?_)⟩
  change (E ⊔ E.map (MulAut.conj (k : S6)).toMonoidHom).map _ ≤ _
  rw [Subgroup.map_sup]
  apply sup_le
  · simpa only [hc0] using (le_iSup (fun j : Fin 6 =>
      E.map (MulAut.conj (c j : S6)).toMonoidHom) (e (i,0)))
  · have hm : (E.map (MulAut.conj (k : S6)).toMonoidHom).map
        (MulAut.conj (d i : S6)).toMonoidHom =
        E.map (MulAut.conj ((d i * k : A6) : S6)).toMonoidHom := by
      rw [map_map]
      congr 1
    rw [hm]
    simpa only [hc1] using (le_iSup (fun j : Fin 6 =>
      E.map (MulAut.conj (c j : S6)).toMonoidHom) (e (i,1)))

theorem permutation_low_rank (E : Subgroup S6) (hE : IsElementaryTwo E)
    (hr : rank E ≤ 2) :
    ∃ (n : ℕ) (c : Fin n → A6), n * rank E ≤ 6 ∧
      alternatingGroup (Fin 6) ≤ ⨆ i, E.map (MulAut.conj (c i : S6)).toMonoidHom := by
  classical
  let : IsElementaryAbelian 2 E := hE.2
  by_cases he : ∃ t : A6, t ≠ 1 ∧ (t : S6) ∈ E
  · obtain ⟨t,ht,htE⟩ := he
    have ht2 : t ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (t : S6) htE)
    obtain ⟨c,hc⟩ := three_of_even E t ht ht2 htE
    exact ⟨3,c, by omega, hc⟩
  · have hcard : Nat.card E ≤ 2 := by
      by_contra h
      exact he (exists_even_of_card_gt_two E (by omega))
    have hr1 : rank E ≤ 1 := (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 2 ≤ 1)
    obtain ⟨x,hxE,hx⟩ := (E.bot_or_exists_ne_one).resolve_left hE.1
    have hodd : x ∉ alternatingGroup (Fin 6) := by
      intro hxalt
      exact he ⟨⟨x,hxalt⟩, fun h => hx (congrArg Subtype.val h), hxE⟩
    obtain ⟨c,hc⟩ := six_of_odd E x hxE hx
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxE) hodd
    exact ⟨6,c, by omega, hc⟩
end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof.NaturalProof
