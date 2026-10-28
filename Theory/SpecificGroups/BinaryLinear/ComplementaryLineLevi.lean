module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Complement

/-!
# Levi complements determined by a complementary binary line

If V = W ⊕ K with K a binary line, the simultaneous stabilizer of W and K
acts faithfully and fully on W: extend an automorphism by the identity on K,
and use the triviality of GL(K) for faithfulness. The quotient V/W is also a
binary line, so restriction to W has the same kernel as the two-block action.
That kernel is the intrinsic two-core of the parabolic. Unique factorization
then proves the relative complement assertion inside that parabolic.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(2)(iv), printed pp.94–95. The five-dimensional maximality and the
application to the original offender are supplied in the consuming modules.
-/

public section

open Subgroup
namespace BinaryLinear.ComplementaryLineLevi
open SmallParabolicLevi
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem line_aut_eq_one (hV : Module.finrank (ZMod 2) V = 1) (g : GL V) :
    g = 1 := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hV hv (g v)
  have hc0 : c ≠ 0 := by
    intro h
    exact hv (g.map_eq_zero_iff.mp (by simpa [h] using hc.symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

private noncomputable def extend (W K : Submodule (ZMod 2) V)
    (hWK : IsCompl W K) (a : GL W) : GL V :=
  let e := W.prodEquivOfIsCompl K hWK
  (e.symm.trans (a.prodCongr (LinearEquiv.refl (ZMod 2) K))).trans e

private theorem extend_left (W K : Submodule (ZMod 2) V)
    (hWK : IsCompl W K) (a : GL W) (w : W) :
    extend W K hWK a w = (a w : V) := by
  simp [extend]

private theorem extend_right (W K : Submodule (ZMod 2) V)
    (hWK : IsCompl W K) (a : GL W) (k : K) :
    extend W K hWK a k = (k : V) := by
  simp [extend]

private theorem extend_mem (W K : Submodule (ZMod 2) V)
    (hWK : IsCompl W K) (a : GL W) :
    extend W K hWK a ∈ parabolic W ⊓ parabolic K := by
  have hW : ∀ v ∈ W, extend W K hWK a v ∈ W := by
    intro v hv
    rw [show extend W K hWK a v = (a ⟨v, hv⟩ : V) from extend_left W K hWK a ⟨v, hv⟩]
    exact (a ⟨v, hv⟩).property
  constructor
  · intro v
    constructor
    · intro hv
      let w : W := ⟨extend W K hWK a v, hv⟩
      have he : extend W K hWK a (a.symm w : V) = extend W K hWK a v := by
        rw [extend_left, a.apply_symm_apply]
      exact (extend W K hWK a).injective he ▸ (a.symm w).property
    · exact hW v
  · intro v
    constructor
    · intro hv
      have he := extend_right W K hWK a ⟨extend W K hWK a v, hv⟩
      exact (extend W K hWK a).injective he ▸ hv
    · intro hv
      rw [extend_right W K hWK a ⟨v, hv⟩]
      exact hv

/-- The literal restriction action of the simultaneous stabilizer is bijective. -/
theorem restriction_bijective (W K : Submodule (ZMod 2) V)
    (hK : Module.finrank (ZMod 2) K = 1) (hWK : IsCompl W K) :
    Function.Bijective ((subspaceAction W).comp
      (Subgroup.inclusion (show parabolic W ⊓ parabolic K ≤ parabolic W from inf_le_left))) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨w, k⟩, rfl⟩ := (W.prodEquivOfIsCompl K hWK).surjective v
    change g.val ((w : V) + k) = h.val ((w : V) + k)
    have hw : g.val w = h.val w :=
      congrArg Subtype.val (LinearEquiv.congr_fun he w)
    have gk : g.val k = (k : V) := congrArg Subtype.val
      (LinearEquiv.congr_fun (line_aut_eq_one hK (subspaceAction K ⟨g.val, g.property.2⟩)) k)
    have hk : h.val k = (k : V) := congrArg Subtype.val
      (LinearEquiv.congr_fun (line_aut_eq_one hK (subspaceAction K ⟨h.val, h.property.2⟩)) k)
    rw [map_add, map_add, hw, gk, hk]
  · intro a
    refine ⟨⟨extend W K hWK a, extend_mem W K hWK a⟩, ?_⟩
    ext w
    exact extend_left W K hWK a w

/-- With a complementary binary line, restriction alone detects the intrinsic
parabolic two-core: the other diagonal block has trivial automorphism group. -/
theorem ker_restriction_eq_twoCore [FiniteDimensional (ZMod 2) V]
    (W K : Submodule (ZMod 2) V)
    (hK : Module.finrank (ZMod 2) K = 1) (hWK : IsCompl W K) :
    (subspaceAction W).ker = pCore 2 (parabolic W) := by
  have hq : Module.finrank (ZMod 2) (V ⧸ W) = 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hWK
    have := Submodule.finrank_quotient_add_finrank W
    omega
  rw [← ker_blockAction_eq_twoCore]
  ext g
  change subspaceAction W g = 1 ↔ (subspaceAction W g, quotientAction W g) = (1, 1)
  simp [line_aut_eq_one hq (quotientAction W g)]

/-- The simultaneous stabilizer is a complement to the intrinsic two-core,
with both subgroups regarded inside the actual parabolic. -/
theorem twoCore_isComplement [FiniteDimensional (ZMod 2) V]
    (W K : Submodule (ZMod 2) V)
    (hK : Module.finrank (ZMod 2) K = 1) (hWK : IsCompl W K) :
    (pCore 2 (parabolic W)).IsComplement'
      ((parabolic W ⊓ parabolic K).subgroupOf (parabolic W)) := by
  rw [← ker_restriction_eq_twoCore W K hK hWK]
  let f := subspaceAction W
  let L := (parabolic W ⊓ parabolic K).subgroupOf (parabolic W)
  have hb : Function.Bijective (f.comp L.subtype) := by
    have hb := restriction_bijective W K hK hWK
    constructor
    · intro x y hxy
      have he : (⟨x.val.val, x.property⟩ : ↥(parabolic W ⊓ parabolic K)) =
          ⟨y.val.val, y.property⟩ := hb.1 hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(parabolic W ⊓ parabolic K) => z.val) he
    · intro a
      obtain ⟨g, hg⟩ := hb.2 a
      exact ⟨⟨⟨g.val, g.property.1⟩, g.property⟩, hg⟩
  constructor
  · rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have hy : y = y' := by
      apply hb.1
      change f y.val = f y'.val
      have hp := congrArg f h
      have hx : f x = 1 := x.property
      have hx' : f x' = 1 := x'.property
      simpa only [map_mul, hx, hx', one_mul] using hp
    subst y'
    exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
  · intro g
    obtain ⟨l, hl⟩ := hb.2 (f g)
    refine ⟨(⟨g * l.val⁻¹, ?_⟩, l), ?_⟩
    · change f (g * l.val⁻¹) = 1
      change f l.val = f g at hl
      rw [map_mul, map_inv, hl, mul_inv_cancel]
    · exact inv_mul_cancel_right _ _

end BinaryLinear.ComplementaryLineLevi
