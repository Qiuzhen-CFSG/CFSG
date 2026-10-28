module

public import Theory.SpecificGroups.PSL3Three.Generators
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.ElementaryAbelian.Basic

/-!
# Two conjugate four-groups generate SL₃(3)

Move one involution to `diag(-1,-1,1)`. Its commuting partner lies in the
GL₂ block centralizer; a small scalar certificate conjugates that partner to
`diag(1,-1,-1)` while fixing the first involution. A second displayed change
of basis then gives two conjugate diagonal four-groups containing the standard
SL₃(3) generators, certified by words of length eight.

This supplies an elementary generation proof of the inner fixed-space bound
in Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.2,
manuscript pp.9--10. Only the 243 possible scalar blocks and the short words
are checked by kernel reduction; the ambient group is not enumerated.
-/

public section
set_option backward.isDefEq.respectTransparency false

namespace Matrix.PSL3Three.InnerFourGeneration
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
private def sign : SL := ⟨!![1,0,0; 0,2,0; 0,0,2], by decide⟩
private def sign' : SL := ⟨!![2,0,0; 0,1,0; 0,0,2], by decide⟩
private abbrev z := Matrix.SL3.standardInvolution (ZMod 3)
private def mixer : SL := ⟨!![0,1,1; 1,0,1; 1,1,1], by decide⟩
private def alphabet : Fin 4 → SL :=
  ![sign, sign',
    ⟨!![2,0,0; 1,2,2; 1,0,1], by decide⟩,
    ⟨!![2,1,2; 0,2,0; 0,1,1], by decide⟩]
private theorem alphabet_two : alphabet 2 = mixer * sign * mixer⁻¹ := by decide
private theorem alphabet_three : alphabet 3 = mixer * sign' * mixer⁻¹ := by decide
private def word : Fin 2 → List (Fin 4) :=
  ![[0,2,3,1,2,0,2,3], [0,3,1,3,0,3,1,3]]
private theorem word_eval (i : Fin 2) :
    evalWord alphabet (word i) = ambientGenerators (i.castLE (by decide)) := by
  apply Subtype.ext
  revert i
  decide

private theorem generate_of_signs (H : Subgroup SL) (hz : z ∈ H) (hs : sign ∈ H) :
    H ⊔ H.map (MulAut.conj mixer).toMonoidHom = ⊤ := by
  let J := H ⊔ H.map (MulAut.conj mixer).toMonoidHom
  have hs' : sign' ∈ H := by
    have he : sign' = z * sign := by decide
    rw [he]
    exact H.mul_mem hz hs
  have ha : ∀ i, alphabet i ∈ J := by
    intro i
    fin_cases i
    · exact Subgroup.mem_sup_left hs
    · exact Subgroup.mem_sup_left hs'
    · rw [show alphabet ⟨2, by decide⟩ = _ from alphabet_two]
      exact Subgroup.mem_sup_right (mem_map_of_mem (MulAut.conj mixer).toMonoidHom hs)
    · rw [show alphabet ⟨3, by decide⟩ = _ from alphabet_three]
      exact Subgroup.mem_sup_right (mem_map_of_mem (MulAut.conj mixer).toMonoidHom hs')
  have h0 : ambientGenerators 0 ∈ J := by
    have he : evalWord alphabet (word 0) = ambientGenerators 0 := word_eval 0
    exact he ▸ evalWord_mem _ J ha _
  have h1 : ambientGenerators 1 ∈ J := by
    have he : evalWord alphabet (word 1) = ambientGenerators 1 := word_eval 1
    exact he ▸ evalWord_mem _ J ha _
  apply eq_top_of_ambientGenerators_mem
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact (ambientGenerators_inverse 0).symm ▸ J.inv_mem h0
  · exact (ambientGenerators_inverse 1).symm ▸ J.inv_mem h1

private def blockConjugator : Fin 12 → SL :=
  ![⟨!![1,1,0; 1,2,0; 0,0,1], by decide⟩,
    ⟨!![1,2,0; 1,1,0; 0,0,2], by decide⟩,
    ⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 1,1,0; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 1,2,0; 0,0,2], by decide⟩,
    ⟨!![1,2,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![0,1,0; 1,0,0; 0,0,2], by decide⟩,
    ⟨!![1,2,0; 1,0,0; 0,0,1], by decide⟩,
    ⟨!![1,1,0; 1,0,0; 0,0,2], by decide⟩,
    ⟨!![0,1,0; 1,1,0; 0,0,2], by decide⟩,
    ⟨!![0,1,0; 1,2,0; 0,0,2], by decide⟩]

private theorem blockConjugator_commute (i : Fin 12) :
    Commute (blockConjugator i) z := by
  change blockConjugator i * z = z * blockConjugator i
  apply Subtype.ext
  revert i
  decide

private theorem block_certificate : ∀ a b c d e : ZMod 3,
    let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![a,b,0; c,d,0; 0,0,e]
    M * M = 1 → M.det = 1 → M ≠ 1 → M ≠ z.val →
      ∃ i : Fin 12, (blockConjugator i).val * M = sign.val * (blockConjugator i).val := by
  decide

private theorem second_involution (u : SL) (hu : u ^ 2 = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hc : Commute u z) :
    ∃ c : SL, c * z * c⁻¹ = z ∧ c * u * c⁻¹ = sign := by
  have hoff := (Matrix.SL3.mem_standardInvolution_centralizer_iff (ZMod 3)
    (by decide) u).mp (mem_centralizer_singleton_iff.mpr hc.eq)
  have he : u.val = !![u 0 0, u 0 1, 0; u 1 0, u 1 1, 0; 0, 0, u 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨i, hi⟩ := block_certificate (u 0 0) (u 0 1) (u 1 0) (u 1 1) (u 2 2)
    (by rw [← he]; exact congrArg Subtype.val (by simpa [pow_two] using hu))
    (by rw [← he]; exact u.property)
    (by rw [← he]; exact fun h => hu1 (Subtype.ext h))
    (by rw [← he]; exact fun h => huz (Subtype.ext h))
  refine ⟨blockConjugator i, ?_, ?_⟩
  · rw [(blockConjugator_commute i).eq, mul_inv_cancel_right]
  · have hh : blockConjugator i * u = sign * blockConjugator i := by
      apply Subtype.ext
      change (blockConjugator i).val * u.val = sign.val * (blockConjugator i).val
      simpa only [← he] using hi
    rw [hh, mul_inv_cancel_right]

open scoped IsMulCommutative in
/-- Two conjugates of every elementary subgroup of order four generate SL₃(3). -/
theorem exists_conjugate_sup_eq_top (A : Subgroup SL) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 4) :
    ∃ g : SL, A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
  have hA : A ≠ ⊥ := by intro he; simp [he] at hcard
  obtain ⟨t, htA, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hlt : zpowers t < A := by
    refine lt_of_le_of_ne (zpowers_le.mpr htA) ?_
    intro he
    have hh := congrArg (fun B : Subgroup SL => Nat.card B) he
    rw [Nat.card_zpowers, hto, hcard] at hh
    omega
  obtain ⟨u, huA, hut⟩ := SetLike.exists_of_lt hlt
  have hu1 : u ≠ 1 := fun he => hut (he ▸ (zpowers t).one_mem)
  have hutz : u ≠ t := fun he => hut (he ▸ mem_zpowers t)
  have hu2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u huA
  have hcomm : Commute u t :=
    congrArg Subtype.val (mul_comm (⟨u, huA⟩ : A) ⟨t, htA⟩)
  obtain ⟨s, hs⟩ := isConj_iff.mp
    (Matrix.SL3.involution_isConj_standard (ZMod 3) t hto (by decide))
  let α := MulAut.conj s
  have hαt : α t = z := hs
  have hαu : α u ≠ 1 := by simpa using hu1
  have hαuz : α u ≠ z := by rw [← hαt]; exact α.injective.ne hutz
  have hαu2 : (α u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  obtain ⟨c, hcz, hcu⟩ := second_involution (α u) hαu2 hαu hαuz
    (hαt ▸ hcomm.map α.toMonoidHom)
  let β := MulAut.conj (c * s)
  have hβt : β t = z := by
    change (c * s) * t * (c * s)⁻¹ = z
    calc
      _ = c * (s * t * s⁻¹) * c⁻¹ := by group
      _ = z := by rw [hs]; exact hcz
  have hβu : β u = sign := by
    change (c * s) * u * (c * s)⁻¹ = sign
    calc
      _ = c * (s * u * s⁻¹) * c⁻¹ := by group
      _ = sign := hcu
  have hgen := generate_of_signs (A.map β.toMonoidHom)
    (hβt ▸ mem_map_of_mem β.toMonoidHom htA)
    (hβu ▸ mem_map_of_mem β.toMonoidHom huA)
  refine ⟨(c * s)⁻¹ * mixer * (c * s), ?_⟩
  have hmap : (A.map (MulAut.conj ((c * s)⁻¹ * mixer * (c * s))).toMonoidHom).map
      β.toMonoidHom = (A.map β.toMonoidHom).map (MulAut.conj mixer).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun f : SL →* SL => A.map f)
    apply MonoidHom.ext
    intro x
    change (c * s) * (((c * s)⁻¹ * mixer * (c * s)) * x *
      ((c * s)⁻¹ * mixer * (c * s))⁻¹) * (c * s)⁻¹ =
      mixer * ((c * s) * x * (c * s)⁻¹) * mixer⁻¹
    group
  apply (Subgroup.map_injective (f := β.toMonoidHom) β.injective)
  rw [Subgroup.map_sup, hmap, hgen, Subgroup.map_top_of_surjective _ β.surjective]
end Matrix.PSL3Three.InnerFourGeneration
