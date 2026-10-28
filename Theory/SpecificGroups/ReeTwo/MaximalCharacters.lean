module

public import Theory.SpecificGroups.ReeTwo.Characters
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The seven maximal subgroups of the Ree two Sylow model

Every binary character is a product of cyclic-four parity, the root-3
coordinate, and the sum of the root-4, root-5 and root-6 coordinates.
The root commutators kill the last six core coordinates in every binary
image, and the root-1 action identifies the three middle root images.
Thus evaluation on roots 1, 3 and 4 determines a binary character.

The seven nonzero parameter triples give index-two kernels of order 2048,
and every index-two subgroup is one of these kernels. This includes the
parity kernel; no automorphism claims are made here.

Source: the verified coordinate multiplication and root-1 action from
Shinoda (1975), (2.3), pp. 81–83, in `Core` and `RootAction`.
-/

namespace ReeTwo
namespace Core

/-- The first core coordinate, corresponding to root 3. -/
@[expose] public def rootThreeCharacter : Core →* FiveFour.Cyclic 2 where
  toFun x := Multiplicative.ofAdd x.b0
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem rootThreeCharacter_a :
    rootThreeCharacter.comp a.toMonoidHom = rootThreeCharacter := by
  apply hom_ext
  exact (by decide +kernel : ∀ i : CoreRoot,
    rootThreeCharacter (a (root i)) = rootThreeCharacter (root i))

/-- The cyclic-four factor fixes the root-3 character. -/
public theorem rootThreeCharacter_action (t : FiveFour.Cyclic 4) (x : Core) :
    rootThreeCharacter (complementAction (SemidirectProduct.inr t) x) =
      rootThreeCharacter x := by
  rw [← FiveFour.generator_pow_val t, map_pow, map_pow]
  change rootThreeCharacter ((a ^ t.toAdd.val) x) = _
  generalize t.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact (DFunLike.congr_fun rootThreeCharacter_a _).trans ih
end Core

namespace SylowModel

/-- The root-3 coordinate extended to the Sylow semidirect product. -/
@[expose] public def rootThreeCharacter : SylowModel →* FiveFour.Cyclic 2 where
  toFun x := Core.rootThreeCharacter x.left
  map_one' := rfl
  map_mul' x y := by
    change Core.rootThreeCharacter (x.left * Core.complementAction
      (SemidirectProduct.inr x.right) y.left) = _
    rw [map_mul, Core.rootThreeCharacter_action]

@[simp] public theorem rootThreeCharacter_root (i : CoreRoot) :
    rootThreeCharacter (root i) = Core.rootThreeCharacter (Core.root i) := rfl

@[simp] public theorem rootThreeCharacter_rootOne : rootThreeCharacter rootOne = 1 := rfl

/-- Binary characters parametrized by parity, root 3, and the core character. -/
@[expose] public def maximalCharacter (a b c : ZMod 2) : SylowModel →* FiveFour.Cyclic 2 :=
  character ^ a.val * rootThreeCharacter ^ b.val * coreCharacter ^ c.val

private theorem binary_map_comm (f : SylowModel →* FiveFour.Cyclic 2) (x y : SylowModel) :
    f (rightComm x y) = 1 := by simp [rightComm, mul_comm]

private theorem binary_root_tail (f : SylowModel →* FiveFour.Cyclic 2) :
    ∀ i : CoreRoot, 4 ≤ i.val → f (root i) = 1 := by
  have h4 : rightComm rootOne (root 3) = root 4 := by decide +kernel
  have h5 : rightComm (root 0) (root 2) = root 5 := by decide +kernel
  have h6 : rightComm (root 1) (root 2) = root 6 := by decide +kernel
  have h7 : rightComm (root 2) (root 3) = root 7 := by decide +kernel
  have h8 : rightComm (root 2) (root 4) = root 8 := by decide +kernel
  have h9 : rightComm (root 0) (root 8) = root 9 := by decide +kernel
  intro i hi
  fin_cases i <;> norm_num at hi
  all_goals first
    | exact h4 ▸ binary_map_comm f _ _
    | exact h5 ▸ binary_map_comm f _ _
    | exact h6 ▸ binary_map_comm f _ _
    | exact h7 ▸ binary_map_comm f _ _
    | exact h8 ▸ binary_map_comm f _ _
    | exact h9 ▸ binary_map_comm f _ _

private theorem binary_root_middle (f : SylowModel →* FiveFour.Cyclic 2) :
    f (root 2) = f (root 1) ∧ f (root 3) = f (root 1) := by
  have h0 : rightComm rootOne (root 0) = root 1 * root 2 * root 4 * root 8 * root 9 :=
    by decide +kernel
  have h1 : rightComm rootOne (root 1) =
      root 2 * root 3 * root 4 * root 6 * root 7 * root 8 * root 9 := by decide +kernel
  have hh0 := congrArg f h0
  have hh1 := congrArg f h1
  simp only [binary_map_comm, map_mul, binary_root_tail f 4 (by decide),
    binary_root_tail f 6 (by decide), binary_root_tail f 7 (by decide),
    binary_root_tail f 8 (by decide), binary_root_tail f 9 (by decide), mul_one] at hh0 hh1
  have hb : ∀ x y : FiveFour.Cyclic 2, 1 = x * y → y = x := by decide +kernel
  exact ⟨hb _ _ hh0, (hb _ _ hh1).trans (hb _ _ hh0)⟩

/-- Roots 1, 3 and 4 determine every binary character of the Sylow model. -/
public theorem binary_hom_ext {f g : SylowModel →* FiveFour.Cyclic 2}
    (ha : f rootOne = g rootOne) (hb : f (root 0) = g (root 0))
    (hc : f (root 1) = g (root 1)) : f = g := by
  apply SemidirectProduct.hom_ext
  · apply Core.hom_ext
    intro i
    change f (root i) = g (root i)
    fin_cases i
    · exact hb
    · exact hc
    · exact (binary_root_middle f).1.trans (hc.trans (binary_root_middle g).1.symm)
    · exact (binary_root_middle f).2.trans (hc.trans (binary_root_middle g).2.symm)
    all_goals rw [binary_root_tail f _ (by decide), binary_root_tail g _ (by decide)]
  · apply FiveFour.cyclicHom_ext
    change f (SemidirectProduct.inr (FiveFour.generator 4)) =
      g (SemidirectProduct.inr (FiveFour.generator 4))
    simpa only [rootOne, map_inv, inv_inv] using congrArg Inv.inv ha

/-- The three chosen roots recover the character parameters. -/
public theorem maximalCharacter_values (a b c : ZMod 2) :
    maximalCharacter a b c rootOne = Multiplicative.ofAdd a ∧
    maximalCharacter a b c (root 0) = Multiplicative.ofAdd b ∧
    maximalCharacter a b c (root 1) = Multiplicative.ofAdd c := by
  exact (by decide +kernel : ∀ a b c : ZMod 2,
    maximalCharacter a b c rootOne = Multiplicative.ofAdd a ∧
    maximalCharacter a b c (root 0) = Multiplicative.ofAdd b ∧
    maximalCharacter a b c (root 1) = Multiplicative.ofAdd c) a b c

/-- All binary characters occur in the explicit three-parameter family. -/
public theorem binary_hom_eq_maximalCharacter (f : SylowModel →* FiveFour.Cyclic 2) :
    f = maximalCharacter (f rootOne).toAdd (f (root 0)).toAdd (f (root 1)).toAdd := by
  apply binary_hom_ext
  · exact (maximalCharacter_values _ _ _).1.symm
  · exact (maximalCharacter_values _ _ _).2.1.symm
  · exact (maximalCharacter_values _ _ _).2.2.symm

/-- Distinct binary parameter triples have distinct kernels. -/
public theorem maximalCharacter_ker_injective (a b c a' b' c' : ZMod 2)
    (h : (maximalCharacter a b c).ker = (maximalCharacter a' b' c').ker) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hf (x : SylowModel) : maximalCharacter a b c x = 1 ↔
      maximalCharacter a' b' c' x = 1 := by
    change x ∈ (maximalCharacter a b c).ker ↔ x ∈ (maximalCharacter a' b' c').ker
    rw [h]
  have hb : ∀ x y : FiveFour.Cyclic 2, (x = 1 ↔ y = 1) → x = y := by decide
  have h0 := hb _ _ (hf rootOne)
  have h1 := hb _ _ (hf (root 0))
  have h2 := hb _ _ (hf (root 1))
  rw [(maximalCharacter_values a b c).1, (maximalCharacter_values a' b' c').1] at h0
  rw [(maximalCharacter_values a b c).2.1, (maximalCharacter_values a' b' c').2.1] at h1
  rw [(maximalCharacter_values a b c).2.2, (maximalCharacter_values a' b' c').2.2] at h2
  exact ⟨congrArg Multiplicative.toAdd h0, congrArg Multiplicative.toAdd h1,
    congrArg Multiplicative.toAdd h2⟩

/-- Every nonzero parameter triple gives a nontrivial binary quotient. -/
public theorem maximalCharacter_surjective (a b c : ZMod 2)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    Function.Surjective (maximalCharacter a b c) := by
  have hbin : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hw : ∃ x, maximalCharacter a b c x = FiveFour.generator 2 := by
    rcases h with ha | hb | hc
    · exact ⟨rootOne, (maximalCharacter_values a b c).1.trans
        (congrArg Multiplicative.ofAdd (hbin a ha))⟩
    · exact ⟨root 0, (maximalCharacter_values a b c).2.1.trans
        (congrArg Multiplicative.ofAdd (hbin b hb))⟩
    · exact ⟨root 1, (maximalCharacter_values a b c).2.2.trans
        (congrArg Multiplicative.ofAdd (hbin c hc))⟩
  intro y
  rcases (by decide : ∀ y : FiveFour.Cyclic 2, y = 1 ∨ y = FiveFour.generator 2) y with
    rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact hw

/-- The seven nontrivial binary characters have index-two kernels. -/
public theorem maximalCharacter_ker_index (a b c : ZMod 2)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : (maximalCharacter a b c).ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (maximalCharacter_surjective a b c h)]
  rw [Nat.card_congr (Subgroup.topEquiv.toEquiv)]
  change Nat.card (ZMod 2) = 2
  simp

/-- Each nontrivial binary-character kernel has order 2048. -/
public theorem maximalCharacter_ker_card (a b c : ZMod 2)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : Nat.card (maximalCharacter a b c).ker = 2048 := by
  have he := (maximalCharacter a b c).ker.index_mul_card
  rw [maximalCharacter_ker_index a b c h, card] at he
  omega

/-- Every index-two subgroup is one of the seven explicit kernels. -/
public theorem eq_maximalCharacter_ker_of_index_eq_two (U : Subgroup SylowModel)
    (hU : U.index = 2) :
    ∃ a b c : ZMod 2, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      U = (maximalCharacter a b c).ker := by
  let : U.Normal := U.normal_of_index_eq_two hU
  have hquot : Nat.card (SylowModel ⧸ U) = 2 := by rw [← U.index_eq_card, hU]
  let e : (SylowModel ⧸ U) ≃* FiveFour.Cyclic 2 :=
    mulEquivOfPrimeCardEq hquot (by change Nat.card (ZMod 2) = 2; simp)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' U)
  have hker : f.ker = U := by
    ext x
    change e (QuotientGroup.mk' U x) = 1 ↔ x ∈ U
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  refine ⟨(f rootOne).toAdd, (f (root 0)).toAdd, (f (root 1)).toAdd, ?_, ?_⟩
  · by_contra h
    push Not at h
    have hf : f = 1 := by
      rw [binary_hom_eq_maximalCharacter f]
      rw [h.1, h.2.1, h.2.2]
      simp [maximalCharacter]
    have ht : U = ⊤ := by rw [← hker, hf]; simp
    simp [ht] at hU
  · rw [← binary_hom_eq_maximalCharacter f, hker]

end SylowModel
end ReeTwo
