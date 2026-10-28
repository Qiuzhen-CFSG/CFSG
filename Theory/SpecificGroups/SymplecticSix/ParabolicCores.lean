module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
The transvection construction and nondegenerate-pairing calculation adapt
Atlas/LinearGroups/Symplectic/{Transvection,TransvectionImage}.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Covered by the ATLAS Research and
Attribution License 1.0; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: specialize to the CFSG binary six-space carrier and add the intrinsic
flag-kernel, exponent-four, and centralizer arguments.
-/

public import Theory.SpecificGroups.SymplecticSix.Basic
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Theory.PGroupCore
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.ZMod

/-!
# Self-centralizing two-cores of binary symplectic parabolics

For a totally isotropic subspace `W`, the subgroup `radical W` of its full
matrix stabilizer fixes `W` pointwise and acts trivially on `Wᗮ / W`. Preservation of the
symplectic form also makes its action on `V / Wᗮ` trivial. Thus displacement
lowers the three-step flag, and every element has fourth power one. The
subgroup is normal in the full stabilizer, hence lies in its intrinsic two-core.

If `W` is nonzero and totally isotropic, a matrix centralizing this subgroup
fixes `W` pointwise: commute it with the transvection in each direction of `W`
and use that the coefficient field has two elements. For `w ∈ W` and
`z ∈ Wᗮ`, the product of transvections in directions `w+z`, `w`, and `z`
acts as `x ↦ x + B(x,w)z + B(x,z)w` and belongs to the subgroup. Commuting
with this product, for one nonzero `w`, forces the displacement of every
`z ∈ Wᗮ` into `W`. This proves that the subgroup, and therefore the full
two-core, is self-centralizing inside the stabilizer.

The argument is uniform in isotropic dimension: it covers all dimensions
one, two, and three occurring by `TwoLocalCover.finrank_le_three_of_isotropic`,
without choices of bases, conjugacy reductions, or Levi-factor assumptions.
All normality, cores, and centralizers are intrinsic to `stabilizer W`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(2), printed p.4, repeated as Theorem 0.1.1(2), printed p.482, in
`refs/quasithin.pdf`. This is the binary isotropic-stabilizer calculation
needed for condition E in the Sp₆(2) converse; two-local coverage and field
transport are separate results.
-/

public noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticSix.ParabolicCores

local notation "F" => ZMod 2
local notation "V" => Vector (ZMod 2)

private theorem add_self (x : V) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem cancel_middle (x y z : V) : (x + y) + (y + z) = x + z := by
  rw [add_assoc, ← add_assoc y y z, add_self, zero_add]

private theorem action_add (g : Sp F) (x y : V) :
    g • (x + y) = g • x + g • y := (toLinear g).map_add x y

private theorem action_smul (g : Sp F) (a : F) (x : V) :
    g • (a • x) = a • (g • x) := (toLinear g).map_smul a x

private theorem orthogonal_invariant (W : Submodule F V) (g : stabilizer W)
    {x : V} (hx : x ∈ (form F).orthogonal W) :
    (g : Sp F) • x ∈ (form F).orthogonal W := by
  intro y hy
  have hy' := (mem_stabilizer_iff W (g⁻¹ : stabilizer W)).mp (g⁻¹).property y hy
  have h := preserves_form (g : Sp F) ((g⁻¹ : stabilizer W) • y) x
  simpa only [Subgroup.smul_def, Subgroup.coe_inv, smul_inv_smul] using h.trans (hx _ hy')

/-- The subgroup fixing `W` pointwise and sending each `x ∈ Wᗮ` to `x` modulo `W`.
For isotropic `W`, this is the kernel of the action on the associated flag quotients. -/
def radical (W : Submodule F V) : Subgroup (stabilizer W) where
  carrier := {g | (∀ x ∈ W, (g : Sp F) • x = x) ∧
    ∀ x ∈ (form F).orthogonal W, (g : Sp F) • x + x ∈ W}
  one_mem' := by
    constructor
    · intro x _; exact one_smul _ x
    · intro x _; simpa only [Subgroup.coe_one, one_smul, add_self] using W.zero_mem
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro x hx
      simp only [Subgroup.coe_mul, mul_smul, hh.1 x hx, hg.1 x hx]
    · intro x hx
      have ha := hg.2 ((h : Sp F) • x) (orthogonal_invariant W h hx)
      have hb := hh.2 x hx
      simpa only [cancel_middle, Subgroup.coe_mul, mul_smul] using W.add_mem ha hb
  inv_mem' := by
    intro g hg
    constructor
    · intro x hx
      have h := congrArg (fun y => (g⁻¹ : stabilizer W) • y) (hg.1 x hx)
      simpa only [Subgroup.smul_def, Subgroup.coe_inv, inv_smul_smul] using h.symm
    · intro x hx
      have h := hg.2 ((g⁻¹ : stabilizer W) • x) (orthogonal_invariant W g⁻¹ hx)
      simpa only [Subgroup.smul_def, Subgroup.coe_inv, smul_inv_smul, add_comm] using h

theorem mem_radical_iff (W : Submodule F V) (g : stabilizer W) :
    g ∈ radical W ↔ (∀ x ∈ W, (g : Sp F) • x = x) ∧
      ∀ x ∈ (form F).orthogonal W, (g : Sp F) • x + x ∈ W := Iff.rfl

instance radical_normal (W : Submodule F V) : (radical W).Normal where
  conj_mem g hg h := by
    constructor
    · intro x hx
      have hx' : (h : Sp F)⁻¹ • x ∈ W :=
        (mem_stabilizer_iff W (h⁻¹ : stabilizer W)).mp (h⁻¹).property x hx
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
      rw [hg.1 _ hx', smul_inv_smul]
    · intro x hx
      have hm := hg.2 ((h⁻¹ : stabilizer W) • x) (orthogonal_invariant W h⁻¹ hx)
      have hh := (mem_stabilizer_iff W h).mp h.property _ hm
      simpa only [Subgroup.smul_def, Subgroup.coe_mul, Subgroup.coe_inv,
        action_add, mul_smul, smul_inv_smul] using hh

private theorem displacement_mem_orthogonal (W : Submodule F V)
    (g : stabilizer W) (hg : g ∈ radical W) (x : V) :
    (g : Sp F) • x + x ∈ (form F).orthogonal W := by
  intro y hy
  have h := preserves_form (g : Sp F) y x
  rw [hg.1 y hy] at h
  rw [map_add, h, CharTwo.add_self_eq_zero]

private theorem ext_action {g h : Sp F}
    (he : ∀ x : V, g • x = h • x) : g = h := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have h := congrFun (he (Pi.single j 1)) i
  simpa [smul_eq_mulVec, Matrix.mulVec_single] using h

/-- Every element of the flag kernel has fourth power one. -/
theorem radical_pow_four (W : Submodule F V) (g : radical W) : g ^ 4 = 1 := by
  let a : Sp F := g.val.val
  have ha := g.property
  have hsq (x : V) : a ^ 2 • x + x ∈ W := by
    have h := ha.2 (a • x + x) (displacement_mem_orthogonal W g.val ha x)
    change a • (a • x + x) + (a • x + x) ∈ W at h
    rw [action_add, cancel_middle] at h
    simpa only [pow_two, mul_smul] using h
  apply Subtype.ext
  apply Subtype.ext
  apply ext_action
  intro x
  simp only [Subgroup.coe_pow, Subgroup.coe_one, one_smul]
  change a ^ 4 • x = x
  have hf : a ^ 2 • (a ^ 2 • x + x) = a ^ 2 • x + x := by
    simp only [pow_two, mul_smul] at hsq ⊢
    rw [ha.1 _ (hsq x), ha.1 _ (hsq x)]
  have he : a ^ 4 • x + a ^ 2 • x = x + a ^ 2 • x := by
    simpa only [action_add, ← mul_smul, ← pow_add, add_comm] using hf
  exact add_right_cancel he

/-- The intrinsic flag kernel is a two-group. -/
theorem radical_isPGroup (W : Submodule F V) : IsPGroup 2 (radical W) := by
  intro g
  exact ⟨2, radical_pow_four W g⟩

/-- Normality and the exponent bound place the flag kernel in the two-core. -/
theorem radical_le_pCore (W : Submodule F V) : radical W ≤ pCore 2 (stabilizer W) :=
  le_sSup ⟨inferInstance, radical_isPGroup W⟩

private theorem form_self (v : V) : form F v v = 0 := by
  simp [form_apply, mul_comm]

private theorem form_swap (v w : V) : form F v w = form F w v := by
  have h : form F v w = -form F w v := by
    simp only [form_apply, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [CharTwo.neg_eq] using h

private def transvectionMap (v : V) : Module.End F V :=
  LinearMap.transvection ((form F).flip v) v

private theorem transvectionMap_apply (v x : V) :
    transvectionMap v x = x + form F x v • v := rfl

private def transvection (v : V) : Sp F :=
  ⟨LinearMap.toMatrix' (transvectionMap v), by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 3) F)
      (LinearMap.toMatrix' (transvectionMap v)) (LinearMap.toMatrix' (transvectionMap v))
    have hpres : (form F).comp (transvectionMap v) (transvectionMap v) = form F := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      change form F (transvectionMap v x) (transvectionMap v y) = form F x y
      simp only [transvectionMap_apply, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, form_self, mul_zero, add_zero]
      rw [form_swap v y]
      have hz := CharTwo.add_self_eq_zero (form F x v * form F y v)
      linear_combination hz
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg, Matrix.neg_mul, form] using hm⟩

private theorem transvection_apply (v x : V) :
    transvection v • x = x + form F x v • v := by
  change (LinearMap.toMatrix' (transvectionMap v)) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, transvectionMap_apply]

private theorem exists_form_left {v : V} (hv : v ≠ 0) :
    ∃ x, form F x v = 1 := by
  have hex : ∃ w, form F w v ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    cases i with
    | inl i =>
      have hi := h (Pi.single (.inr i) 1)
      simpa [form_apply, Pi.single_apply] using hi
    | inr i =>
      have hi := h (e i)
      simpa [form_apply, e, Pi.single_apply] using hi
  obtain ⟨w, hw⟩ := hex
  exact ⟨(form F w v)⁻¹ • w, by simp [map_smul, hw]⟩

private theorem transvection_stabilizes (W : Submodule F V) (w : V) (hw : w ∈ W) :
    transvection w ∈ stabilizer W := by
  rw [mem_stabilizer_iff]
  intro x hx
  rw [transvection_apply]
  exact W.add_mem hx (W.smul_mem _ hw)

private def localTransvection (W : Submodule F V) (w : V) (hw : w ∈ W) : stabilizer W :=
  ⟨transvection w, transvection_stabilizes W w hw⟩

private theorem localTransvection_mem (W : Submodule F V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) (w : V) (hw : w ∈ W) :
    localTransvection W w hw ∈ radical W := by
  constructor
  · intro x hx
    change transvection w • x = x
    rw [transvection_apply, hW x hx w hw, zero_smul, add_zero]
  · intro x _
    change transvection w • x + x ∈ W
    rw [transvection_apply, add_comm x, add_assoc, add_self, add_zero]
    exact W.smul_mem _ hw

private theorem centralizer_fixes (W : Submodule F V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0)
    (g : stabilizer W) (hg : g ∈ Subgroup.centralizer (radical W : Set (stabilizer W)))
    (w : V) (hw : w ∈ W) : (g : Sp F) • w = w := by
  by_cases hw0 : w = 0
  · subst w
    exact map_zero (toLinear (g : Sp F))
  obtain ⟨x, hx⟩ := exists_form_left hw0
  have h := congrArg (fun a : stabilizer W => (a : Sp F) • x)
    (hg (localTransvection W w hw) (localTransvection_mem W hW w hw))
  change (transvection w * (g : Sp F)) • x = ((g : Sp F) * transvection w) • x at h
  simp only [mul_smul, transvection_apply, action_add, hx, one_smul] at h
  have hs : form F ((g : Sp F) • x) w • w = (g : Sp F) • w := add_left_cancel h
  have ha : ∀ a : F, a = 0 ∨ a = 1 := by decide
  rcases ha (form F ((g : Sp F) • x) w) with hz | ho
  · rw [hz, zero_smul] at hs
    exact False.elim (hw0 ((toLinear (g : Sp F)).injective (hs.symm.trans
      (map_zero (toLinear (g : Sp F))).symm)))
  · simpa only [ho, one_smul] using hs.symm

private def shear (w z : V) : Sp F :=
  transvection (w + z) * transvection w * transvection z

private theorem shear_apply (w z : V) (hwz : form F w z = 0) (x : V) :
    shear w z • x = x + form F x w • z + form F x z • w := by
  have hzw : form F z w = 0 := (form_swap z w).trans hwz
  simp only [shear, mul_smul, transvection_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, form_self,
    hwz, hzw, mul_zero, add_zero]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

private theorem shear_stabilizes (W : Submodule F V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0)
    (w : V) (hw : w ∈ W) (z : V) (hz : z ∈ (form F).orthogonal W) :
    shear w z ∈ stabilizer W := by
  rw [mem_stabilizer_iff]
  intro x hx
  simp only [shear_apply w z (hz w hw), hW x hx w hw, hz x hx, zero_smul, add_zero]
  exact hx

private def localShear (W : Submodule F V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0)
    (w : V) (hw : w ∈ W) (z : V) (hz : z ∈ (form F).orthogonal W) : stabilizer W :=
  ⟨shear w z, shear_stabilizes W hW w hw z hz⟩

private theorem localShear_mem (W : Submodule F V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0)
    (w : V) (hw : w ∈ W) (z : V) (hz : z ∈ (form F).orthogonal W) :
    localShear W hW w hw z hz ∈ radical W := by
  constructor
  · intro x hx
    change shear w z • x = x
    simp only [shear_apply w z (hz w hw), hW x hx w hw, hz x hx, zero_smul, add_zero]
  · intro x hx
    change shear w z • x + x ∈ W
    have hxw : form F x w = 0 := (form_swap x w).trans (hx w hw)
    rw [shear_apply w z (hz w hw), hxw, zero_smul, add_zero, add_comm x,
      add_assoc, add_self, add_zero]
    exact W.smul_mem _ hw

private theorem centralizer_displacement (W : Submodule F V) (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0)
    (g : stabilizer W) (hg : g ∈ Subgroup.centralizer (radical W : Set (stabilizer W)))
    (z : V) (hz : z ∈ (form F).orthogonal W) : (g : Sp F) • z + z ∈ W := by
  obtain ⟨w, hw, hw0⟩ := W.ne_bot_iff.mp hW0
  obtain ⟨x, hx⟩ := exists_form_left hw0
  have hgw := centralizer_fixes W hW g hg w hw
  have hx' : form F ((g : Sp F) • x) w = 1 := by
    have h := preserves_form (g : Sp F) x w
    rwa [hgw, hx] at h
  have h := congrArg (fun a : stabilizer W => (a : Sp F) • x)
    (hg (localShear W hW w hw z hz) (localShear_mem W hW w hw z hz))
  change (shear w z * (g : Sp F)) • x = ((g : Sp F) * shear w z) • x at h
  simp only [mul_smul, shear_apply w z (hz w hw), action_add, action_smul,
    hx, hx', one_smul, hgw] at h
  have he : z + form F ((g : Sp F) • x) z • w =
      (g : Sp F) • z + form F x z • w := by
    apply add_left_cancel (a := (g : Sp F) • x)
    simpa only [add_assoc] using h
  have he' : (g : Sp F) • z + z =
      form F ((g : Sp F) • x) z • w + form F x z • w := by
    calc
      (g : Sp F) • z + z =
          ((g : Sp F) • z + form F x z • w) + (form F x z • w + z) :=
        (cancel_middle _ _ _).symm
      _ = (z + form F ((g : Sp F) • x) z • w) + (form F x z • w + z) := by rw [← he]
      _ = form F ((g : Sp F) • x) z • w + form F x z • w := by
        rw [add_comm (form F x z • w) z, add_comm z, cancel_middle]
  rw [he']
  exact W.add_mem (W.smul_mem _ hw) (W.smul_mem _ hw)

/-- The intrinsic centralizer of the normal two-subgroup lies in that subgroup. -/
theorem centralizer_radical_le (W : Submodule F V) (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) :
    Subgroup.centralizer (radical W : Set (stabilizer W)) ≤ radical W := by
  intro g hg
  exact ⟨centralizer_fixes W hW g hg, centralizer_displacement W hW0 hW g hg⟩

/-- Every full stabilizer of a nonzero totally isotropic binary six-space
subspace has self-centralizing intrinsic two-core. -/
theorem centralizer_pCore_le (W : Submodule F V) (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, form F x y = 0) :
    Subgroup.centralizer (pCore 2 (stabilizer W) : Set (stabilizer W)) ≤
      pCore 2 (stabilizer W) := by
  intro g hg
  apply radical_le_pCore W
  apply centralizer_radical_le W hW0 hW
  intro u hu
  exact hg u (radical_le_pCore W hu)

end Theory.SpecificGroups.SymplecticSix.ParabolicCores
