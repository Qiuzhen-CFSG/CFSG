module

public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.ElementaryAbelian.Basic

/-!
# Simultaneous diagonalization of four-subgroups in SL₃(3)

Every elementary four-subgroup is conjugate to the determinant-one diagonal
subgroup. First conjugate one involution to diag(-1,-1,1); its commuting
partner lies in the GL₂ block centralizer. The twelve displayed block
changes of basis diagonalize that partner. Only the 243 scalar blocks are
checked, and subgroup equality follows from order four.

Source: Aschbacher--Smith, quasithin manuscript, Lemma 2.5.8(5), pp.556--557.
The block argument also occurs in `PSL3Three.InnerFourGeneration`.
-/

public section
set_option backward.isDefEq.respectTransparency false
namespace Matrix.PSL3Three.FourGeometry
open Subgroup

private def sign : SL := ⟨!![1,0,0; 0,2,0; 0,0,2], by decide⟩
private abbrev z := Matrix.SL3.standardInvolution (ZMod 3)

/-- The four determinant-one diagonal matrices. -/
@[expose] def diagonalElement : Fin 4 → SL :=
  ![1, Matrix.SL3.standardInvolution (ZMod 3),
    ⟨!![1,0,0; 0,2,0; 0,0,2], by decide⟩,
    Matrix.SL3.standardInvolution (ZMod 3) *
      ⟨!![1,0,0; 0,2,0; 0,0,2], by decide⟩]

private theorem diagonal_mul : ∀ i j : Fin 4,
    ∃ k : Fin 4, diagonalElement i * diagonalElement j = diagonalElement k := by decide
private theorem diagonal_inv : ∀ i : Fin 4,
    (diagonalElement i)⁻¹ = diagonalElement i := by decide

/-- The actual diagonal four-subgroup of SL₃(3). -/
@[expose] def diagonalFour : Subgroup SL where
  carrier := Set.range diagonalElement
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := diagonal_mul i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (diagonal_inv i).symm⟩

private theorem diagonalElement_injective : Function.Injective diagonalElement := by decide

/-- The diagonal subgroup has order four. -/
theorem card_diagonalFour : Nat.card diagonalFour = 4 := by
  let e : Fin 4 ≃ diagonalFour := Equiv.ofBijective
    (fun i => ⟨diagonalElement i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ h => diagonalElement_injective (congrArg Subtype.val h), by
      rintro ⟨_, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  rw [← Nat.card_congr e]
  simp

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
/-- Every elementary four-subgroup admits a simultaneous diagonalizing conjugation. -/
theorem exists_conj_diagonalFour (A : Subgroup SL) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 4) :
    ∃ g : SL, A.map (MulAut.conj g).toMonoidHom = diagonalFour := by
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
  refine ⟨c * s, ?_⟩
  apply (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rintro x ⟨i, rfl⟩
    have hzt : z ∈ A.map β.toMonoidHom := hβt ▸ mem_map_of_mem β.toMonoidHom htA
    have hsu : sign ∈ A.map β.toMonoidHom := hβu ▸ mem_map_of_mem β.toMonoidHom huA
    fin_cases i
    · exact Subgroup.one_mem _
    · exact hzt
    · exact hsu
    · exact Subgroup.mul_mem _ hzt hsu
  · rw [Subgroup.card_map_of_injective β.injective, hcard, card_diagonalFour]

end Matrix.PSL3Three.FourGeometry
