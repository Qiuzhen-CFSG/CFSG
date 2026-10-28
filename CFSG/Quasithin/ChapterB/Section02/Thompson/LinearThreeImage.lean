module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Sylow
public import Theory.GroupTheory.SylowImageLocalization
public import Theory.SpecificGroups.PSL3Two.SourceFlag
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Calculations
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates

/-!
# The near-maximal Thompson image in SL₃(2)

A maximal elementary subgroup with nontrivial action image has image of
order at most four. Pulling back a cyclic subgroup in that image loses at
most one rank. Involution fusion and conjugation by the action kernel put
each conjugate back in the specified Sylow subgroup without changing its
image or order. Subgroups of the prescribed near-maximal order therefore
put every Sylow involution in J₁'s image. The two root factors generate the
whole marked Sylow subgroup.

This is the rank-loss and fusion argument of Aschbacher–Smith 14.3.9(3),
printed pp.992–993, using the definition in B.2.2, p.74. Its original-group
consumer is LocalReduction.CubicThompsonCommutator, proving 14.5.10.
-/

public noncomputable section
open Subgroup Stellmacher Matrix.PSL3Two
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB

private theorem near_maximal_involution_image
    {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (S : Sylow 2 X) (q : X →* Q) (hq : Function.Surjective q)
    (hr : 1 < twoRank (S : Subgroup X))
    (hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ q.ker)
    (hsmall : ∀ A : Subgroup X, A ∈ elementaryAbelianMaxSubgroups (S : Subgroup X) →
      Nat.card (A.map q) ≤ 4)
    (hfuse : ∀ a b : Q, a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b ^ 2 = 1 →
      ∃ g : Q, (MulAut.conj g) a = b)
    (b : Q) (hb : b ∈ (S : Subgroup X).map q) (hb2 : b ^ 2 = 1) :
    b ∈ (thompsonJ (S : Subgroup X) 1).map q := by
  classical
  by_cases hb1 : b = 1
  · exact hb1 ▸ one_mem _
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup X), ¬ A ≤ q.ker := by
    by_contra hn
    push Not at hn
    exact hJ (sSup_le hn)
  obtain ⟨A,hA,hAk⟩ := hex
  let := hA.2.1
  have hne : A.map q ≠ ⊥ := fun he => hAk ((Subgroup.map_eq_bot_iff _).mp he)
  obtain ⟨a,ha,ha1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have ha2 : a ^ 2 = 1 := by
    let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  let C := A ⊓ (zpowers a).comap q
  have hC : C ≤ A := inf_le_left
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hC) (inclusion_injective _)
  have hcq : C.map q = zpowers a := by
    apply le_antisymm
    · rintro z ⟨x,hx,rfl⟩
      exact hx.2
    · intro z hz
      obtain ⟨x,hx,he⟩ := (zpowers_le.mpr ha : zpowers a ≤ A.map q) hz
      exact ⟨x,⟨hx,show q x ∈ zpowers a from he.symm ▸ hz⟩,he⟩
  have hca : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha2 ha1
  have hi : C.relIndex A ≤ 2 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup Q) (zpowers a) (A.map q)
      bot_le (zpowers_le.mpr ha)
    rw [relIndex_bot_left,relIndex_bot_left,hca] at hm
    have hs := hsmall A hA
    have he : C.relIndex A = (zpowers a).relIndex (A.map q) := by
      change (A ⊓ (zpowers a).comap q).relIndex A = _
      rw [inf_relIndex_left,relIndex_comap]
    rw [he]
    omega
  have hcard : Nat.card A ≤ Nat.card C * 2 := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup X) C A bot_le hC
    simp only [relIndex_bot_left] at hm
    rw [←hm]
    exact Nat.mul_le_mul_left _ hi
  obtain ⟨g,hg⟩ := hfuse a b ha1 ha2 hb1 hb2
  obtain ⟨x,rfl⟩ := hq g
  let C' := C.map (MulAut.conj x).toMonoidHom
  have hC'q : C'.map q = zpowers b := by
    calc
      _ = (C.map q).map (MulAut.conj (q x)).toMonoidHom := by
        rw [map_map,map_map]
        congr 1
        ext c
        simp [MulAut.conj_apply]
      _ = zpowers b := by rw [hcq,MonoidHom.map_zpowers]; exact congrArg zpowers hg
  have hC'p : IsPGroup 2 C' := (IsElementaryAbelian.isPGroup 2 C).map _
  obtain ⟨k,hk,hBS⟩ := S.exists_kernel_conjugate_le q C' hC'p
    (hC'q ▸ zpowers_le.mpr hb)
  let B := C'.map (MulAut.conj k).toMonoidHom
  let : IsElementaryAbelian 2 C' := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBq : B.map q = zpowers b := by
    change (C'.map (MulAut.conj k).toMonoidHom).map q = _
    rw [map_map]
    have he : q.comp (MulAut.conj k).toMonoidHom = q := by
      ext c
      simp [MulAut.conj_apply,hk]
    rw [he,hC'q]
  have hBc : Nat.card B = Nat.card C := by
    change Nat.card ((C.map (MulAut.conj x).toMonoidHom).map (MulAut.conj k).toMonoidHom) = _
    rw [card_map_of_injective (MulAut.conj k).injective,
      card_map_of_injective (MulAut.conj x).injective]
  have hbound : 2 ^ (twoRank (S : Subgroup X) - 1) ≤ Nat.card B := by
    rw [elementaryAbelianMaxSubgroups_card_eq _ _ hA,maxOrder_eq_two_pow_rank] at hcard
    have he : twoRank (S : Subgroup X) = (twoRank (S : Subgroup X) - 1) + 1 := by omega
    rw [he,pow_succ] at hcard
    rw [hBc]
    omega
  have hbmap : b ∈ B.map q := hBq.symm ▸ mem_zpowers b
  obtain ⟨c,hc,hcb⟩ := hbmap
  obtain ⟨E,hEB,hEe,hEc,hcE⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem B
    (by omega : 0 < twoRank (S : Subgroup X) - 1) hbound c hc
  exact ⟨c,(le_sSup (show E ∈ thompsonFamily (S : Subgroup X) 1 from
    ⟨hEB.trans hBS,hEe,by omega,hEc⟩)) hcE,hcb⟩

private theorem elementary_borel_card (A : Subgroup SL) (hA : A ≤ borelSL)
    [IsElementaryAbelian 2 A] : Nat.card A ≤ 4 := by
  have hd : Nat.card A ∣ 8 := by simpa only [card_borelSL] using card_dvd_of_le hA
  have he : Nat.card A ≠ 8 := by
    intro hc
    have hEq : A = borelSL := eq_of_le_of_card_ge hA (by rw [hc,card_borelSL])
    have hcomm := IsMulCommutative.is_comm.comm
      (⟨Bruhat.upper 1,hEq ▸ Bruhat.upper_mem 1⟩ : A)
      ⟨Bruhat.upper 4,hEq ▸ Bruhat.upper_mem 4⟩
    have hne : Bruhat.upper 1 * Bruhat.upper 4 ≠ Bruhat.upper 4 * Bruhat.upper 1 := by decide +kernel
    exact hne (congrArg Subtype.val hcomm)
  have hd' : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 4 ∨ Nat.card A = 8 := by
    have hh := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card A ∣ 2 ^ 3 from hd)
    obtain ⟨n,hn,hc⟩ := hh
    interval_cases n <;> simp_all
  omega

private theorem linear_involution_fusion (a b : SL)
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1) (hb : b ≠ 1) (hb2 : b ^ 2 = 1) :
    ∃ g : SL, (MulAut.conj g) a = b := by
  obtain ⟨x,hx⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator
    a ha (by simpa only [pow_two] using ha2)
  obtain ⟨y,hy⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator
    b hb (by simpa only [pow_two] using hb2)
  refine ⟨y*x⁻¹,?_⟩
  have hx' : x⁻¹*a*x = BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution := by
    calc
      _ = x⁻¹*(a*x) := by group
      _ = _ := by rw [hx]; group
  change (y*x⁻¹)*a*(y*x⁻¹)⁻¹=b
  calc
    _ = y*(x⁻¹*a*x)*y⁻¹ := by group
    _ = y*BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution*y⁻¹ := by rw [hx']
    _ = b := by rw [←hy]; group

private theorem upper_last_square (j : Fin 2) :
    Bruhat.upper ⟨4 * j, by omega⟩ ^ 2 = 1 := by
  revert j
  decide +kernel

/-- If J(S) has nontrivial image in the original SL₃(2) quotient, then
J₁(S) maps onto its full marked Sylow subgroup. No elementary lift of the
whole Sylow image is assumed. -/
theorem linear_three_thompson_one_image
    {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (q : X →* SL) (hq : Function.Surjective q)
    (hS : (S : Subgroup X).map q = borelSL)
    (hr : 1 < twoRank (S : Subgroup X))
    (hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ q.ker) :
    (thompsonJ (S : Subgroup X) 1).map q = borelSL := by
  apply le_antisymm ((map_mono (thompsonJ_le _ _)).trans_eq hS)
  intro b hb
  obtain ⟨i,j,rfl⟩ := SourceFlag.borel_factors b hb
  have hmem (a : SL) (ha : a ∈ borelSL) (ha2 : a ^ 2 = 1) :
      a ∈ (thompsonJ (S : Subgroup X) 1).map q :=
    near_maximal_involution_image S q hq hr hJ (fun A hA => by
      let := hA.2.1
      let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
      exact elementary_borel_card _ ((map_mono hA.1).trans_eq hS))
      linear_involution_fusion a (hS ▸ ha) ha2
  apply mul_mem
  · exact hmem _ (SourceFlag.radical_le_borel (SourceFlag.upper_first i))
      (Matrix.PSL3Two.MarkedAutomorphisms.pointV_square _ (SourceFlag.upper_first i))
  · exact hmem _ (SourceFlag.root_le_borel (SourceFlag.upper_last j)) (upper_last_square j)

end CFSG.Quasithin.ChapterB
