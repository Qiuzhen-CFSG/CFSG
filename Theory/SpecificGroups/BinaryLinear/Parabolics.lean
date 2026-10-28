module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup

/-!
# Parabolics in a binary linear group

For a subspace `W` of a vector space over `𝔽₂`, the block-unipotent radical
fixes `W` pointwise and acts trivially on `V/W`. Rank-one transvections show
that its common fixed space is exactly `W` when `W ≠ 0`, and that its ambient
centralizer is contained in the radical when also `W ≠ V`. Its normalizer is
therefore the geometric stabilizer of `W`. Relative normality then gives
self-centralization of the stabilizer's intrinsic two-core.

The fixed space of a nonidentity two-subgroup of a finite binary vector space
is nonzero and proper, and its normalizer stabilizes that space. These facts
supply the local linear algebra for the binary cases in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2(2), printed p.4
(repeated as Theorem 0.1.1(2), printed p.482).
-/

@[expose] public section

namespace BinaryLinear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev GL (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] := V ≃ₗ[ZMod 2] V

private theorem binary_add_self (v : V) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]

private theorem binary_scalar {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

/-- The group fixing W pointwise and acting trivially on V/W. -/
def radical (W : Submodule (ZMod 2) V) : Subgroup (GL V) where
  carrier := {g | (∀ w ∈ W, g w = w) ∧ ∀ v, g v - v ∈ W}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hgd⟩ ⟨hh, hhd⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      simp only [LinearEquiv.mul_apply, hh w hw, hg w hw]
    · intro v
      have := W.add_mem (hgd (h v)) (hhd v)
      simpa only [sub_add_sub_cancel, LinearEquiv.mul_apply] using this
  inv_mem' := by
    rintro g ⟨hg, hgd⟩
    refine ⟨?_, ?_⟩
    · intro w hw
      apply g.injective
      simpa using (hg w hw).symm
    · intro v
      have := W.neg_mem (hgd (g⁻¹ v))
      simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, neg_sub] using this

/-- The geometric parabolic stabilizing W. -/
def parabolic (W : Submodule (ZMod 2) V) : Subgroup (GL V) where
  carrier := {g | ∀ v, g v ∈ W ↔ v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    exact (hg (h v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    simpa using (hg (g⁻¹ v)).symm

theorem radical_le_parabolic (W : Submodule (ZMod 2) V) :
    radical W ≤ parabolic W := by
  intro g hg v
  constructor
  · intro hv
    have := W.sub_mem hv (hg.2 v)
    simpa using this
  · intro hv
    simpa only [hg.1 v hv] using hv

theorem radical_two (W : Submodule (ZMod 2) V) : IsPGroup 2 (radical W) := by
  apply isPGroup_iff_pow_pow_eq_one.mpr
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change (g : GL V) ^ 2 = 1
  ext v
  have hd := g.property.1 ((g : GL V) v - v) (g.property.2 v)
  simp only [map_sub] at hd
  simp only [pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq]
  apply sub_eq_zero.mp
  calc
    (g : GL V) ((g : GL V) v) - v =
        ((g : GL V) ((g : GL V) v) - (g : GL V) v) + ((g : GL V) v - v) := by abel
    _ = 0 := by rw [hd, binary_add_self]

/-- A rank-one transvection in characteristic two. -/
def transvection (w : V) (f : V →ₗ[ZMod 2] ZMod 2) (hfw : f w = 0) : GL V where
  toFun v := v + f v • w
  invFun v := v + f v • w
  map_add' v u := by simp [map_add, add_smul]; abel
  map_smul' a v := by simp [smul_add, smul_smul]
  left_inv v := by simp [map_add, map_smul, hfw, add_assoc, binary_add_self]
  right_inv v := by simp [map_add, map_smul, hfw, add_assoc, binary_add_self]

theorem transvection_mem {W : Submodule (ZMod 2) V} {w : V} (hw : w ∈ W)
    {f : V →ₗ[ZMod 2] ZMod 2} (hf : W ≤ f.ker) :
    transvection w f (hf hw) ∈ radical W := by
  refine ⟨?_, ?_⟩
  · intro v hv
    change v + f v • w = v
    simp only [show f v = 0 from hf hv, zero_smul, add_zero]
  · intro v
    change (v + f v • w) - v ∈ W
    simpa only [add_sub_cancel_left] using W.smul_mem (f v) hw

theorem mem_iff_fixed_radical {W : Submodule (ZMod 2) V} (hW : W ≠ ⊥) (v : V) :
    v ∈ W ↔ ∀ g ∈ radical W, g v = v := by
  constructor
  · exact fun hv g hg => hg.1 v hv
  · intro hv
    by_contra hvW
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    obtain ⟨f, hfv, hf⟩ := W.exists_le_ker_of_notMem hvW
    have h := hv (transvection w f (hf hw)) (transvection_mem hw hf)
    change v + f v • w = v at h
    rw [binary_scalar hfv, one_smul] at h
    exact hw0 (add_eq_left.mp h)

theorem radical_ne_bot {W : Submodule (ZMod 2) V} (hW : W ≠ ⊥) (hWt : W ≠ ⊤) :
    radical W ≠ ⊥ := by
  intro h
  apply hWt
  apply top_unique
  intro v _
  apply (mem_iff_fixed_radical hW v).mpr
  intro g hg
  have hg1 : g = 1 := by simpa only [h, Subgroup.mem_bot] using hg
  simp only [hg1, LinearEquiv.coe_one, id_eq]

theorem parabolic_le_normalizer (W : Submodule (ZMod 2) V) :
    parabolic W ≤ Subgroup.normalizer (radical W : Set (GL V)) := by
  rw [Subgroup.le_set_normalizer_iff]
  intro g hg t ht
  refine ⟨?_, ?_⟩
  · intro w hw
    change g (t (g⁻¹ w)) = w
    have hi : g⁻¹ w ∈ W := (parabolic W).inv_mem hg w |>.mpr hw
    rw [ht.1 _ hi]
    simp
  · intro v
    have hd := (hg (t (g⁻¹ v) - g⁻¹ v)).mpr (ht.2 (g⁻¹ v))
    simpa only [map_sub, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
      LinearEquiv.mul_apply] using hd

theorem normalizer_radical {W : Submodule (ZMod 2) V} (hW : W ≠ ⊥) :
    Subgroup.normalizer (radical W : Set (GL V)) = parabolic W := by
  apply le_antisymm _ (parabolic_le_normalizer W)
  have stable : ∀ g ∈ Subgroup.normalizer (radical W : Set (GL V)),
      ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    apply (mem_iff_fixed_radical hW (g w)).mpr
    intro t ht
    have ht' : g⁻¹ * t * g ∈ radical W := by
      simpa only [inv_inv, SetLike.mem_coe] using
        ((Subgroup.normalizer (radical W : Set (GL V))).inv_mem hg t).mp ht
    have hh := ht'.1 w hw
    have := congrArg g hh
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply] using this
  intro g hg v
  constructor
  · intro hv
    simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
      stable g⁻¹ ((Subgroup.normalizer (radical W : Set (GL V))).inv_mem hg) (g v) hv
  · exact stable g hg v

theorem centralizer_radical_le {W : Submodule (ZMod 2) V} (hW : W ≠ ⊥) (hWt : W ≠ ⊤) :
    Subgroup.centralizer (radical W : Set (GL V)) ≤ radical W := by
  intro g hg
  have comm (w : V) (hw : w ∈ W) (f : V →ₗ[ZMod 2] ZMod 2) (hf : W ≤ f.ker)
      (v : V) : f (g v) • w = f v • g w := by
    have h := congrArg (fun t : GL V => t v)
      ((Subgroup.mem_centralizer_iff.mp hg) _ (transvection_mem hw hf))
    change g v + f (g v) • w = g (v + f v • w) at h
    simpa only [map_add, map_smul, add_right_inj] using h
  have fix : ∀ w ∈ W, g w = w := by
    obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hWt)
    obtain ⟨f, hfv, hf⟩ := W.exists_le_ker_of_notMem hv
    have hf1 := binary_scalar hfv
    intro w hw
    by_cases hw0 : w = 0
    · simp [hw0]
    have hc := comm w hw f hf v
    rw [hf1, one_smul] at hc
    have hfg : f (g v) ≠ 0 := by
      intro hzero
      rw [hzero, zero_smul] at hc
      exact hw0 (g.map_eq_zero_iff.mp hc.symm)
    rw [binary_scalar hfg, one_smul] at hc
    exact hc.symm
  refine ⟨fix, ?_⟩
  intro v
  by_contra hd
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨f, hfd, hf⟩ := W.exists_le_ker_of_notMem hd
  have hc := comm w hw f hf v
  rw [fix w hw] at hc
  have hz : f (g v - v) • w = 0 := by
    rw [map_sub, sub_smul, hc, sub_self]
  rw [binary_scalar hfd, one_smul] at hz
  exact hw0 hz

/-- The actual common fixed subspace of a subgroup of the linear group. -/
def fixedSpace (Q : Subgroup (GL V)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ q ∈ Q, q v = v}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw q hq
    simp only [map_add, hv q hq, hw q hq]
  smul_mem' := by
    intro a v hv q hq
    simp only [map_smul, hv q hq]

theorem fixedSpace_ne_bot [Finite V] (hV : 2 ∣ Nat.card V)
    {Q : Subgroup (GL V)} (hQ : IsPGroup 2 Q) : fixedSpace Q ≠ ⊥ := by
  have hz : (0 : V) ∈ MulAction.fixedPoints Q V := by
    rw [MulAction.mem_fixedPoints]
    intro q
    exact q.val.map_zero
  obtain ⟨v, hv, h0v⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hV hz
  have hvQ : v ∈ fixedSpace Q := by
    intro q hq
    exact (MulAction.mem_fixedPoints.mp hv) ⟨q, hq⟩
  intro hbot
  have hv0 : v = 0 := by simpa only [hbot, Submodule.mem_bot] using hvQ
  exact h0v hv0.symm

theorem fixedSpace_ne_top {Q : Subgroup (GL V)} (hQ : Q ≠ ⊥) : fixedSpace Q ≠ ⊤ := by
  intro htop
  apply hQ
  apply bot_unique
  intro q hq
  change q = 1
  ext v
  exact (show v ∈ fixedSpace Q from htop ▸ Submodule.mem_top) q hq

theorem normalizer_le_parabolic_fixedSpace (Q : Subgroup (GL V)) :
    Subgroup.normalizer (Q : Set (GL V)) ≤ parabolic (fixedSpace Q) := by
  have stable : ∀ g ∈ Subgroup.normalizer (Q : Set (GL V)),
      ∀ v ∈ fixedSpace Q, g v ∈ fixedSpace Q := by
    intro g hg v hv q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      simpa only [inv_inv, SetLike.mem_coe] using
        ((Subgroup.normalizer (Q : Set (GL V))).inv_mem hg q).mp hq
    have := congrArg g (hv _ hq')
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_inv,
      LinearEquiv.apply_symm_apply] using this
  intro g hg v
  constructor
  · intro hv
    simpa only [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using
      stable g⁻¹ ((Subgroup.normalizer (Q : Set (GL V))).inv_mem hg) (g v) hv
  · exact stable g hg v

/-- Relative normality of the radical controls the intrinsic two-core. -/
theorem centralizer_parabolic_twoCore_le {W : Submodule (ZMod 2) V}
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) :
    Subgroup.centralizer (pCore 2 (parabolic W) : Set (parabolic W)) ≤
      pCore 2 (parabolic W) :=
  centralizer_pCore_le_of_normalized 2 (radical W) (parabolic W)
    (radical_two W) (radical_le_parabolic W) (parabolic_le_normalizer W)
    (centralizer_radical_le hW hWt)

end BinaryLinear
