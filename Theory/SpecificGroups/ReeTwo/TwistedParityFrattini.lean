module

public import Theory.SpecificGroups.ReeTwo.TwistedParityCoordinates

/-!
# The Frattini subgroup of the twisted Ree two parity kernel

The three corrected binary coordinates have exactly the Frattini subgroup as
kernel. The previously proved containment and kernel order reduce this to a
lower bound of 256 for the Frattini order. Squares and commutators put roots
4 through 9 and the product of roots 2 and 3 in the Frattini subgroup. Their
ordered words give 128 distinct core elements. Multiplication by the square of
`rootOne * root 0` doubles this family, since that square has nontrivial
cyclic-four coordinate. Coordinate recovery proves that all 256 elements are
distinct.

Source: Shinoda (1975), (2.3), pp. 81–82, using the verified multiplication
and normal forms in `Core`, `RootAction`, and `Sylow`. Core root indices here
are shifted by three from Shinoda's indices. The finitely many square and
commutator identities below are checked by the Lean kernel.
-/

namespace ReeTwo.SylowModel
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
private abbrev K := (maximalCharacter 1 1 0).ker
-- Work in the ambient model to avoid carrying subtype witnesses through root words.
private def W : Subgroup SylowModel := (frattini K).map K.subtype

private theorem square_mem (x : SylowModel) (hx : x ∈ K) : x ^ 2 ∈ W := by
  apply Subgroup.mem_map.mpr
  refine ⟨(⟨x, hx⟩ : K) ^ 2, ?_, rfl⟩
  rw [(IsPGroup.of_card (n := 11)
    (maximalCharacter_ker_card 1 1 0 (by decide))).frattini_eq_closure_squares]
  exact Subgroup.subset_closure ⟨⟨x, hx⟩, rfl⟩

private theorem comm_mem (x y : SylowModel) (hx : x ∈ K) (hy : y ∈ K) :
    rightComm x y ∈ W := by
  have he : rightComm x y = (x⁻¹) ^ 2 * (x * y⁻¹) ^ 2 * y ^ 2 := by
    simp [rightComm, pow_two, mul_assoc]
  rw [he]
  exact W.mul_mem (W.mul_mem (square_mem _ (K.inv_mem hx))
    (square_mem _ (K.mul_mem hx (K.inv_mem hy)))) (square_mem _ hy)

private theorem root_mem_K (i : CoreRoot) (hi : i ≠ 0) : root i ∈ K :=
  (by decide +kernel : ∀ i : CoreRoot, i ≠ 0 → root i ∈ K) i hi

private theorem a_mem_K : rootOne * root 0 ∈ K := by decide +kernel

private theorem tail_mem : ∀ i : CoreRoot, 4 ≤ i.val → root i ∈ W := by
  have h5 : root 5 ∈ W := by
    have he : root 1 ^ 2 = root 5 := by decide +kernel
    exact he ▸ square_mem _ (root_mem_K 1 (by decide))
  have h8 : root 8 ∈ W := by
    have he : root 3 ^ 2 = root 8 := by decide +kernel
    exact he ▸ square_mem _ (root_mem_K 3 (by decide))
  have h9 : root 9 ∈ W := by
    have he : root 2 ^ 2 = root 9 := by decide +kernel
    exact he ▸ square_mem _ (root_mem_K 2 (by decide))
  have h6 : root 6 ∈ W := by
    have he : rightComm (root 1) (root 2) = root 6 := by decide +kernel
    exact he ▸ comm_mem _ _ (root_mem_K 1 (by decide)) (root_mem_K 2 (by decide))
  have h7 : root 7 ∈ W := by
    have he : rightComm (root 2) (root 3) = root 7 := by decide +kernel
    exact he ▸ comm_mem _ _ (root_mem_K 2 (by decide)) (root_mem_K 3 (by decide))
  have h4 : root 4 ∈ W := by
    have he : rightComm (rootOne * root 0) (root 3) =
        root 4 * root 5 * root 7 * root 9 := by decide +kernel
    have h := he ▸ comm_mem _ _ a_mem_K (root_mem_K 3 (by decide))
    exact (W.mul_mem_cancel_right h5).mp
      ((W.mul_mem_cancel_right h7).mp ((W.mul_mem_cancel_right h9).mp h))
  intro i hi
  fin_cases i <;> norm_num at hi
  all_goals assumption

private theorem pair_mem : root 2 * root 3 ∈ W := by
  have he : rightComm (rootOne * root 0) (root 1) =
      root 2 * root 3 * root 4 * root 6 * root 8 * root 9 := by decide +kernel
  have h := he ▸ comm_mem _ _ a_mem_K (root_mem_K 1 (by decide))
  exact (W.mul_mem_cancel_right (tail_mem 4 (by decide))).mp
    ((W.mul_mem_cancel_right (tail_mem 6 (by decide))).mp
      ((W.mul_mem_cancel_right (tail_mem 8 (by decide))).mp
        ((W.mul_mem_cancel_right (tail_mem 9 (by decide))).mp h)))

-- The paired coordinate and the six tail coordinates supply seven free bits.
private def coreBlock (v : Fin 7 → ZMod 2) : Core :=
  ⟨0, 0, v 0, v 0, v 1, v 2, v 3, v 4, v 5, v 6⟩

private theorem coreBlock_mem (v : Fin 7 → ZMod 2) :
    SemidirectProduct.inl (coreBlock v) ∈ W := by
  have hn := congrArg (SemidirectProduct.inl : Core →* SylowModel)
    (Core.normal_form (coreBlock v))
  simp only [map_mul, map_pow] at hn
  change root 0 ^ 0 * root 1 ^ 0 * root 2 ^ (v 0).val * root 3 ^ (v 0).val *
    root 4 ^ (v 1).val * root 5 ^ (v 2).val * root 6 ^ (v 3).val *
    root 7 ^ (v 4).val * root 8 ^ (v 5).val * root 9 ^ (v 6).val = _ at hn
  have hp : root 2 ^ (v 0).val * root 3 ^ (v 0).val = (root 2 * root 3) ^ (v 0).val :=
    (by decide +kernel : ∀ b : ZMod 2, root 2 ^ b.val * root 3 ^ b.val =
      (root 2 * root 3) ^ b.val) (v 0)
  simp only [pow_zero, one_mul, hp] at hn
  rw [← hn]
  exact W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem (W.mul_mem
    (W.pow_mem pair_mem _) (W.pow_mem (tail_mem 4 (by decide)) _))
    (W.pow_mem (tail_mem 5 (by decide)) _)) (W.pow_mem (tail_mem 6 (by decide)) _))
    (W.pow_mem (tail_mem 7 (by decide)) _)) (W.pow_mem (tail_mem 8 (by decide)) _))
    (W.pow_mem (tail_mem 9 (by decide)) _)

-- The square supplies an independent eighth bit in the cyclic-four factor.
private def word (p : ZMod 2 × (Fin 7 → ZMod 2)) : SylowModel :=
  ((rootOne * root 0) ^ 2) ^ p.1.val * SemidirectProduct.inl (coreBlock p.2)

private theorem word_mem (p : ZMod 2 × (Fin 7 → ZMod 2)) : word p ∈ W :=
  W.mul_mem (W.pow_mem (square_mem _ a_mem_K) _) (coreBlock_mem p.2)

private theorem word_injective : Function.Injective word := by
  intro p q h
  have hr := congrArg SemidirectProduct.right h
  have ht : p.1 = q.1 := by
    change (((rootOne * root 0) ^ 2) ^ p.1.val).right * 1 =
      (((rootOne * root 0) ^ 2) ^ q.1.val).right * 1 at hr
    simp only [mul_one] at hr
    exact (by decide +kernel : ∀ b c : ZMod 2,
      (((rootOne * root 0) ^ 2) ^ b.val).right =
        (((rootOne * root 0) ^ 2) ^ c.val).right → b = c) p.1 q.1 hr
  apply Prod.ext ht
  have he : coreBlock p.2 = coreBlock q.2 := by
    unfold word at h
    rw [ht] at h
    exact SemidirectProduct.inl_injective (mul_left_cancel h)
  funext i
  fin_cases i
  · exact congrArg Core.b2 he
  · exact congrArg Core.b4 he
  · exact congrArg Core.b5 he
  · exact congrArg Core.b6 he
  · exact congrArg Core.b7 he
  · exact congrArg Core.b8 he
  · exact congrArg Core.b9 he

private theorem frattini_card_ge : 256 ≤ Nat.card (frattini K) := by
  have h := Nat.card_le_card_of_injective (fun p => (⟨word p, word_mem p⟩ : W))
    (fun _ _ he => word_injective (congrArg Subtype.val he))
  have hc : Nat.card (ZMod 2 × (Fin 7 → ZMod 2)) = 256 := by
    rw [Nat.card_prod, Nat.card_fun]
    norm_num
  rw [hc] at h
  have hw : Nat.card W = Nat.card (frattini K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  exact hw ▸ h

/-- The corrected binary coordinate map realizes the Frattini quotient of the
 twisted parity kernel. -/
public theorem twistedParityCoordinates_ker_eq_frattini :
    twistedParityCoordinates.ker = frattini (maximalCharacter 1 1 0).ker := by
  symm
  apply Subgroup.eq_of_le_of_card_ge frattini_le_twistedParityCoordinates_ker
  rw [twistedParityCoordinates_ker_card]
  exact frattini_card_ge
end ReeTwo.SylowModel
