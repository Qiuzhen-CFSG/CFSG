module

public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.Reduction
public import Theory.SpecificGroups.Tits.AmalgamRigidity.RestrictionBounds
public import Theory.SpecificGroups.ReeTwo.InvolutionCharacters
public import Theory.SpecificGroups.ReeTwo.SylowEighthPower
public import Theory.SpecificGroups.ReeTwo.SylowCollectedArithmetic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Set.Card

/-!
# Automorphisms of the full binary Ree Sylow group

The mixed-character kernel is the marked Tits Sylow subgroup. Its automorphic
images are among just two kernels: every pulled-back mixed character kills
involutions, and its kernel contains an element with nontrivial eighth power.
The binary-character classification therefore leaves only the core character
and the mixed character. In particular, we do not assume that this subgroup
is characteristic.

The stabilizer restricts to the automorphism group of the actual Tits Sylow
subgroup, whose order is at most 8192. A pointwise fixer is determined by the
image of `rootOne`. Its displacement centralizes the mixed kernel, and three
explicit elements force that displacement to be either one or the last root.
Thus the restriction kernel has order at most two, giving the bound
`2 * (2 * 8192) = 32768`.

The final application removes this upper-bound premise from the literal full
Ree amalgam factorization criterion. The first-restriction lower bound and the
separating second restriction remain the independent inputs of that assembly.

Source: Shinoda (1975), (2.3), pp.81–83, for the verified coordinates; Parrott
(1972), p.683, for the marked Tits Sylow subgroup; Aschbacher–Smith F.1.11–12,
printed pp.262–263, for the amalgam application. No exploratory GAP exhaustion
is used in this proof.
-/

namespace Tits.AmalgamRigidity.FullRee
open ReeTwo SylowModel
open scoped Pointwise

/-- Involutions remove the root-three coefficient. The element
`rootOne * root 0 * root 2` then excludes the parity character by its eighth power. -/
private theorem mixed_comp (f : MulAut SylowModel) :
    mixedCharacter.comp f.toMonoidHom = coreCharacter ∨
    mixedCharacter.comp f.toMonoidHom = mixedCharacter := by
  let χ := mixedCharacter.comp f.toMonoidHom
  have hb : χ (root 0) = 1 := by
    apply alternativeCharacter_eq_one_of_square_eq_one mixedCharacter (Or.inr rfl)
    rw [← map_pow, show root 0 ^ 2 = 1 from by decide +kernel, map_one]
  have hn : χ ≠ 1 := by
    intro h
    have he := DFunLike.congr_fun h (f.symm (root 1))
    change mixedCharacter (f (f.symm (root 1))) = 1 at he
    rw [f.apply_symm_apply] at he
    exact mixedCharacter_nontrivial he
  have hp : χ ≠ character := by
    intro h
    let x := rootOne * root 0 * root 2
    have hx : mixedCharacter x = 1 := by decide +kernel
    have hx8 : x ^ 8 ≠ 1 := (eighth_power_ne_one_iff x).mpr (by decide +kernel)
    have hy : character (f.symm x) = 1 := by
      rw [← h]
      change mixedCharacter (f (f.symm x)) = 1
      rwa [f.apply_symm_apply]
    have hy8 : f.symm x ^ 8 ≠ 1 := by
      intro he
      apply hx8
      have he' := congrArg f he
      simpa only [map_pow, f.apply_symm_apply, map_one] using he'
    have he := (eighth_power_ne_one_iff (f.symm x)).mp hy8
    rw [hy] at he
    exact (by decide : (1 : FiveFour.Cyclic 2) ≠ FiveFour.generator 2) he.1
  have he := binary_hom_eq_maximalCharacter χ
  rw [hb] at he
  change χ = maximalCharacter (χ rootOne).toAdd 0 (χ (root 1)).toAdd at he
  have cases₂ : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases cases₂ (χ rootOne).toAdd with ha | ha <;>
    rcases cases₂ (χ (root 1)).toAdd with hc | hc <;> rw [ha, hc] at he
  · exact (hn (by simpa [χ, show (1 : ZMod 2).val = 1 from rfl, maximalCharacter] using he)).elim
  · exact Or.inl (by simpa [χ, show (1 : ZMod 2).val = 1 from rfl, maximalCharacter] using he)
  · exact (hp (by simpa [χ, show (1 : ZMod 2).val = 1 from rfl, maximalCharacter] using he)).elim
  · exact Or.inr (by simpa [χ, show (1 : ZMod 2).val = 1 from rfl,
      maximalCharacter, mixedCharacter, mul_comm] using he)

private abbrev K := mixedCharacter.ker
private abbrev stabilizer := MulAction.stabilizer (MulAut SylowModel) K

private theorem stabilizer_index_le : stabilizer.index ≤ 2 := by
  rw [MulAction.index_stabilizer]
  have hsub : MulAction.orbit (MulAut SylowModel) K ⊆
      ({coreCharacter.ker, mixedCharacter.ker} : Set (Subgroup SylowModel)) := by
    rintro U ⟨f, rfl⟩
    have he : f • K = (mixedCharacter.comp f.symm.toMonoidHom).ker := by
      exact (MonoidHom.ker_comp_mulEquiv mixedCharacter f.symm).symm
    change f • K ∈ ({coreCharacter.ker, mixedCharacter.ker} : Set (Subgroup SylowModel))
    rw [he]
    change (mixedCharacter.comp f.symm.toMonoidHom).ker = coreCharacter.ker ∨
      (mixedCharacter.comp f.symm.toMonoidHom).ker = mixedCharacter.ker
    rcases mixed_comp f.symm with h | h
    · exact Or.inl (congrArg MonoidHom.ker h)
    · exact Or.inr (congrArg MonoidHom.ker h)
  have hn : coreCharacter.ker ≠ mixedCharacter.ker := by
    intro h
    have hm : rootOne ∈ coreCharacter.ker := coreCharacter_rootOne
    rw [h] at hm
    exact character_rootOne_ne_one (by simpa only [MonoidHom.mem_ker,
      mixedCharacter_rootOne] using hm)
  exact (Set.ncard_le_ncard hsub).trans (Set.ncard_pair hn).le

private theorem coordinate_action_check : ∀ t : FiveFour.Cyclic 4,
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b1 = (Core.root 0).b1 →
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b2 = (Core.root 0).b2 →
    (Core.complementAction (SemidirectProduct.inr t) (Core.root 0)).b3 = (Core.root 0).b3 →
    t = 1 := by decide +kernel

private theorem small_check : ∀ a b c : ZMod 2,
    let g : SylowModel := ⟨⟨0, 0, 0, 0, 0, 0, a, b, 0, c⟩, 1⟩
    Collected.collectedMul g (Collected.collectedMul rootOne (root 2)) =
      Collected.collectedMul (Collected.collectedMul rootOne (root 2)) g →
    g = 1 ∨ g = root 9 := by decide +kernel

/-- Three elements of the mixed kernel already have centralizer contained
in the last root subgroup. Only the final three binary coordinates are enumerated. -/
private theorem centralizer_small (g : SylowModel)
    (h0 : g * root 0 = root 0 * g)
    (h4 : g * root 4 = root 4 * g)
    (hy : g * (rootOne * root 2) = (rootOne * root 2) * g) :
    g = 1 ∨ g = root 9 := by
  have hc : g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 0) =
      Core.root 0 * g.left := by
    have h := congrArg SemidirectProduct.left h0
    change g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root 0) =
      Core.root 0 * Core.complementAction (SemidirectProduct.inr 1) g.left at h
    simpa only [map_one, MulAut.one_apply] using h
  have ht : g.right = 1 := by
    apply coordinate_action_check
    · exact add_left_cancel (by
        simpa only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
          Core.mul, add_comm (Core.root 0).b1] using congrArg Core.b1 hc)
    · exact add_left_cancel (by
        simpa only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
          Core.mul, add_comm (Core.root 0).b2] using congrArg Core.b2 hc)
    · exact add_left_cancel (by
        simpa only [show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl,
          Core.mul, add_comm (Core.root 0).b3] using congrArg Core.b3 hc)
  have core_comm (i : CoreRoot) (h : g * root i = root i * g) :
      Core.mul g.left (Core.root i) = Core.mul (Core.root i) g.left := by
    have he := congrArg SemidirectProduct.left h
    change g.left * Core.complementAction (SemidirectProduct.inr g.right) (Core.root i) =
      Core.root i * Core.complementAction (SemidirectProduct.inr 1) g.left at he
    simpa only [ht, map_one, MulAut.one_apply,
      show ∀ x y : Core, x * y = Core.mul x y from fun _ _ => rfl] using he
  have h40 : g.left.b4 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords] using congrArg Core.b7 (core_comm 0 h0)
  have h30 : g.left.b3 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords, h40] using congrArg Core.b6 (core_comm 0 h0)
  have h20 : g.left.b2 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords, h30] using congrArg Core.b5 (core_comm 0 h0)
  have h80 : g.left.b8 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords, h30, h40] using congrArg Core.b9 (core_comm 0 h0)
  have h00 : g.left.b0 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords] using (congrArg Core.b6 (core_comm 4 h4)).symm
  have h10 : g.left.b1 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords, h20] using (congrArg Core.b8 (core_comm 4 h4)).symm
  have h50 : g.left.b5 = 0 := by
    simpa [Core.mul, Core.root, Core.ofCoords, h00, h10] using congrArg Core.b9 (core_comm 4 h4)
  have he : g = ⟨⟨0, 0, 0, 0, 0, 0, g.left.b6, g.left.b7, 0, g.left.b9⟩, 1⟩ := by
    apply SemidirectProduct.ext
    · exact Core.ext h00 h10 h20 h30 h40 h50 rfl rfl h80 rfl
    · exact ht
  rw [he] at hy ⊢
  exact small_check _ _ _ (by simpa only [Collected.collectedMul_eq] using hy)

private def restriction : stabilizer →* MulAut K where
  toFun f := (f.val.subgroupMap K).trans (MulEquiv.subgroupCongr f.property)
  map_one' := by apply MulEquiv.ext; intro x; apply Subtype.ext; rfl
  map_mul' := by intro f g; apply MulEquiv.ext; intro x; apply Subtype.ext; rfl

private theorem aut_ext {f g : MulAut SylowModel}
    (hK : ∀ x ∈ K, f x = g x) (ht : f rootOne = g rootOne) : f = g := by
  apply MulEquiv.ext
  intro x
  by_cases hx : x ∈ K
  · exact hK x hx
  have hy : rootOne⁻¹ * x ∈ K := by
    change mixedCharacter (rootOne⁻¹ * x) = 1
    rw [map_mul, map_inv]
    exact (by decide +kernel : ∀ u : FiveFour.Cyclic 2, u ≠ 1 →
      (mixedCharacter rootOne)⁻¹ * u = 1) _ hx
  calc
    f x = f rootOne * f (rootOne⁻¹ * x) := by rw [← map_mul, mul_inv_cancel_left]
    _ = g rootOne * g (rootOne⁻¹ * x) := by rw [ht, hK _ hy]
    _ = g x := by rw [← map_mul, mul_inv_cancel_left]

private theorem kernel_fixed (f : restriction.ker) (x : SylowModel) (hx : x ∈ K) :
    f.val.val x = x := by
  exact congrArg (fun a : MulAut K => (a ⟨x, hx⟩ : SylowModel)) f.property

private theorem displacement_small (f : restriction.ker) :
    rootOne⁻¹ * f.val.val rootOne = 1 ∨
      rootOne⁻¹ * f.val.val rootOne = root 9 := by
  have hc (x : SylowModel) (hx : x ∈ K) :
      (rootOne⁻¹ * f.val.val rootOne) * x = x * (rootOne⁻¹ * f.val.val rootOne) := by
    have hm : rootOne * x * rootOne⁻¹ ∈ K :=
      (inferInstance : K.Normal).conj_mem x hx rootOne
    have h := kernel_fixed f _ hm
    simp only [map_mul, map_inv, kernel_fixed f x hx] at h
    calc
      _ = rootOne⁻¹ * (f.val.val rootOne * x * (f.val.val rootOne)⁻¹) *
          f.val.val rootOne := by group
      _ = x * (rootOne⁻¹ * f.val.val rootOne) := by rw [h]; group
  apply centralizer_small
  · exact hc _ (by decide +kernel)
  · exact hc _ (by decide +kernel)
  · exact hc _ (by decide +kernel)

private theorem restriction_kernel_card : Nat.card restriction.ker ≤ 2 := by
  let code (f : restriction.ker) : ZMod 2 :=
    (rootOne⁻¹ * f.val.val rootOne).left.b9
  have hi : Function.Injective code := by
    intro f g h
    have hd : rootOne⁻¹ * f.val.val rootOne = rootOne⁻¹ * g.val.val rootOne := by
      rcases displacement_small f with hf | hf <;>
        rcases displacement_small g with hg | hg
      · exact hf.trans hg.symm
      · have hh : (0 : ZMod 2) = 1 := by
          change (rootOne⁻¹ * f.val.val rootOne).left.b9 =
            (rootOne⁻¹ * g.val.val rootOne).left.b9 at h
          simpa only [hf, hg, show (1 : SylowModel).left.b9 = 0 from rfl,
            show (root 9).left.b9 = 1 from by decide +kernel] using h
        exact (zero_ne_one hh).elim
      · have hh : (1 : ZMod 2) = 0 := by
          change (rootOne⁻¹ * f.val.val rootOne).left.b9 =
            (rootOne⁻¹ * g.val.val rootOne).left.b9 at h
          simpa only [hf, hg, show (1 : SylowModel).left.b9 = 0 from rfl,
            show (root 9).left.b9 = 1 from by decide +kernel] using h
        exact (one_ne_zero hh).elim
      · exact hf.trans hg.symm
    apply Subtype.ext
    apply Subtype.ext
    exact aut_ext (fun x hx => (kernel_fixed f x hx).trans (kernel_fixed g x hx).symm)
      (mul_left_cancel hd)
  simpa using Nat.card_le_card_of_injective code hi

private theorem stabilizer_card_le : Nat.card stabilizer ≤ 16384 := by
  have ha : Nat.card (MulAut K) ≤ 8192 := by
    rw [Nat.card_congr (MulAut.congr
      ReeTwo.ParabolicMarkedComparison.Verified.titsSylowEquiv).toEquiv]
    exact Tits.AmalgamRigidity.sylowAut_card_le
  have hr : Nat.card restriction.range ≤ 8192 :=
    (Nat.card_le_card_of_injective restriction.range.subtype Subtype.val_injective).trans ha
  have hc := restriction.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  have hb := Nat.mul_le_mul restriction_kernel_card hr
  rw [hc] at hb
  exact hb

/-- The full binary Ree Sylow group has at most 32768 automorphisms. -/
public theorem sylowAut_card_le : Nat.card (MulAut SylowModel) ≤ 32768 := by
  have hc := stabilizer.card_mul_index
  have hb := Nat.mul_le_mul stabilizer_card_le stabilizer_index_le
  rw [hc] at hb
  exact hb


/-- The proved Sylow automorphism bound leaves just the two independent
endpoint restriction calculations in the full Ree factorization criterion. -/
public theorem factorsThrough_of_first_restriction_bound
    (hfirst : 16384 ≤ Nat.card firstRestrictions)
    (hsecond : ∃ r : MulAut ReeTwo.SylowModel,
      r ∈ secondRestrictions ∧ r ∉ firstRestrictions)
    (d : MulAut ExceptionalParabolics.FullRee.B) :
    Theory.GroupTheory.RankTwoAmalgam.FactorsThrough
      ExceptionalParabolics.FullRee.amalgam d :=
  factorsThrough_of_bounds sylowAut_card_le hfirst hsecond d

end Tits.AmalgamRigidity.FullRee
