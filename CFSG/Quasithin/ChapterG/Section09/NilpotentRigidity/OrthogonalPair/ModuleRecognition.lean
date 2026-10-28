module
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.OrthogonalPair.Carrier
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

/-!
# Recognition of the binary four-dimensional dihedral-pair module

For a nonzero binary module, the two commuting standard reflections have
a nonzero common fixed vector `w`. If both standard cubic rotations are
fixed-point-free, their orbit vectors `w`, `r w`, `s w`, and `r (s w)` are
linearly independent: successive reflection differences isolate the four
coefficients. In dimension four these vectors form a basis. The resulting
linear equivalence intertwines the action with the marked determinant
model from `MatrixModel`, on which `Carrier` identifies the exact
Siegel-generated elementary orthogonal group.

This is the module recognition used for the shared four-space in
Aschbacher--Smith G.9.2, printed pp.352--353 (`refs/quasithin.pdf`,
PDF pp.363--364). The fixed-vector hypotheses are essential; the direct
sum of the two natural planes does not satisfy them.
-/

public section
namespace ClassicalOrthogonal.BinaryD2
universe v
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) Pair W)

local notation "r" => ((DihedralGroup.r 1, 1) : Pair)
local notation "s" => ((1, DihedralGroup.r 1) : Pair)
local notation "a" => ((DihedralGroup.sr 0, 1) : Pair)
local notation "c" => ((1, DihedralGroup.sr 0) : Pair)

private theorem add_self_binary (w : W) : w + w = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ w
  have hz : (2 : ZMod 2) = 0 := by decide
  rw [hz, zero_smul] at h
  exact h.symm

private theorem involution_apply {g : Pair} (hg : g * g = 1) (w : W) :
    σ g (σ g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, hg, map_one]
  rfl

private theorem commute_apply {g h : Pair} (hg : Commute g h) (w : W) :
    σ g (σ h w) = σ h (σ g w) :=
  congrArg (fun f : Module.End (ZMod 2) W => f w) (hg.map σ).eq

private theorem cubic_apply {g : Pair} (hg : g ^ 3 = 1)
    (hf : ∀ w, σ g w = w → w = 0) (w : W) : σ g (σ g w) = w + σ g w := by
  have hc : σ g (σ g (σ g w)) = w := by
    calc _ = σ (g ^ 3) w := by simp [pow_succ, map_mul, Module.End.mul_apply]
         _ = w := by rw [hg, map_one]; rfl
  have hn : σ g (σ g w) + σ g w + w = 0 := hf _ (by simp only [map_add, hc]; abel)
  have htwo := add_self_binary (w + σ g w)
  calc σ g (σ g w) = (σ g (σ g w) + σ g w + w) + (w + σ g w) := by
         rw [add_comm w (σ g w)] at htwo
         linear_combination (norm := abel) -htwo
       _ = w + σ g w := by rw [hn, zero_add]

/-- Two commuting involutions on a nonzero binary module have a nonzero common fixed vector. -/
theorem exists_common_fixed [Nontrivial W] :
    ∃ w : W, w ≠ 0 ∧ σ a w = w ∧ σ c w = w := by
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  have haa : a * a = 1 := by decide
  have hcc : c * c = 1 := by decide
  have hac : Commute a c := by unfold Commute SemiconjBy; decide
  have hy : ∃ y : W, y ≠ 0 ∧ σ a y = y := by
    by_cases hax : σ a x = x
    · exact ⟨x, hx, hax⟩
    · refine ⟨σ a x + x, ?_, ?_⟩
      · intro h
        apply hax
        have ht := add_self_binary x
        linear_combination (norm := abel) h - ht
      · rw [map_add, involution_apply σ haa]
        abel
  obtain ⟨y, hy0, hay⟩ := hy
  by_cases hcy : σ c y = y
  · exact ⟨y, hy0, hay, hcy⟩
  · refine ⟨σ c y + y, ?_, ?_, ?_⟩
    · intro h
      apply hcy
      have ht := add_self_binary y
      linear_combination (norm := abel) h - ht
    · rw [map_add, commute_apply σ hac, hay]
    · rw [map_add, involution_apply σ hcc]
      abel

/-- The four orbit vectors, ordered according to determinant coordinates. -/
@[expose] def orbitMap (w : W) : Space →ₗ[ZMod 2] W where
  toFun x := x (.inl 1) • w + x (.inr 0) • σ r w +
    x (.inl 0) • σ s w + x (.inr 1) • σ r (σ s w)
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' t x := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply]


private theorem reflection_cubic {b g : Pair} (hg : g ^ 3 = 1)
    (hbg : b * g = g * g * b) (hf : ∀ w, σ g w = w → w = 0)
    {w : W} (hb : σ b w = w) : σ b (σ g w) = w + σ g w := by
  calc σ b (σ g w) = σ (b * g) w := by rw [map_mul, Module.End.mul_apply]
       _ = σ (g * g * b) w := by rw [hbg]
       _ = σ g (σ g w) := by simp only [map_mul, Module.End.mul_apply, hb]
       _ = w + σ g w := cubic_apply σ hg hf w

/-- Reflection differences separate the four coefficients in the rotation orbit. -/
theorem orbitMap_injective (w : W) (hw : w ≠ 0)
    (ha : σ a w = w) (hc : σ c w = w)
    (hr : ∀ z, σ r z = z → z = 0) (hs : ∀ z, σ s z = z → z = 0) :
    Function.Injective (orbitMap σ w) := by
  have har : σ a (σ r w) = w + σ r w :=
    reflection_cubic σ (by decide) (by decide) hr ha
  have has : σ a (σ s w) = σ s w := by
    rw [commute_apply σ (by unfold Commute SemiconjBy; decide : Commute a s), ha]
  have hars : σ a (σ r (σ s w)) = σ s w + σ r (σ s w) :=
    reflection_cubic σ (by decide) (by decide) hr has
  have hcs : σ c (σ s w) = w + σ s w :=
    reflection_cubic σ (by decide) (by decide) hs hc
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  change x (.inl 1) • w + x (.inr 0) • σ r w +
    x (.inl 0) • σ s w + x (.inr 1) • σ r (σ s w) = 0 at hx
  have hax := congrArg (σ a) hx
  simp only [map_add, map_smul, ha, har, has, hars, map_zero] at hax
  have hd : x (.inr 0) • w + x (.inr 1) • σ s w = 0 := by
    linear_combination (norm := module) hax - hx
  have hcd := congrArg (σ c) hd
  simp only [map_add, map_smul, hc, hcs, map_zero] at hcd
  have hd0 : x (.inr 1) = 0 := by
    apply (smul_eq_zero.mp (show x (.inr 1) • w = 0 from ?_)).resolve_right hw
    linear_combination (norm := module) hcd - hd
  have hb0 : x (.inr 0) = 0 := by
    rw [hd0, zero_smul, add_zero] at hd
    exact (smul_eq_zero.mp hd).resolve_right hw
  simp only [hd0, hb0, zero_smul, add_zero] at hx
  have hcx := congrArg (σ c) hx
  simp only [map_add, map_smul, hc, hcs, map_zero] at hcx
  have hc0 : x (.inl 0) = 0 := by
    apply (smul_eq_zero.mp (show x (.inl 0) • w = 0 from ?_)).resolve_right hw
    linear_combination (norm := module) hcx - hx
  rw [hc0, zero_smul, add_zero] at hx
  have ha0 : x (.inl 1) = 0 := (smul_eq_zero.mp hx).resolve_right hw
  funext i
  rcases i with i | i <;> fin_cases i
  · exact hc0
  · exact ha0
  · exact hb0
  · exact hd0


private theorem rotation_left_coordinates : ∀ x : Space,
    (pairHom r).val x = Sum.elim ![x (.inr 1), x (.inr 0)]
      ![x (.inl 1) + x (.inr 0), x (.inl 0) + x (.inr 1)] := by decide +kernel

private theorem rotation_right_coordinates : ∀ x : Space,
    (pairHom s).val x = Sum.elim ![x (.inl 0) + x (.inl 1), x (.inl 0)]
      ![x (.inr 1), x (.inr 1) + x (.inr 0)] := by decide +kernel

private theorem reflection_left_coordinates : ∀ x : Space,
    (pairHom a).val x = Sum.elim ![x (.inl 0) + x (.inr 1), x (.inl 1) + x (.inr 0)]
      ![x (.inr 0), x (.inr 1)] := by decide +kernel

private theorem reflection_right_coordinates : ∀ x : Space,
    (pairHom c).val x = Sum.elim ![x (.inl 0), x (.inl 0) + x (.inl 1)]
      ![x (.inr 1) + x (.inr 0), x (.inr 1)] := by decide +kernel

/-- The orbit map intertwines the full product action, with the binary matrix marking. -/
theorem orbitMap_intertwines (w : W)
    (ha : σ a w = w) (hc : σ c w = w)
    (hr : ∀ z, σ r z = z → z = 0) (hs : ∀ z, σ s z = z → z = 0)
    (g : Pair) (x : Space) : orbitMap σ w ((pairHom g).val x) = σ g (orbitMap σ w x) := by
  have hr2 (z : W) : σ r (σ r z) = z + σ r z := cubic_apply σ (by decide) hr z
  have hs2 (z : W) : σ s (σ s z) = z + σ s z := cubic_apply σ (by decide) hs z
  have hsr (z : W) : σ s (σ r z) = σ r (σ s z) :=
    commute_apply σ (by unfold Commute SemiconjBy; decide : Commute s r) z
  have har : σ a (σ r w) = w + σ r w :=
    reflection_cubic σ (by decide) (by decide) hr ha
  have has : σ a (σ s w) = σ s w := by
    rw [commute_apply σ (by unfold Commute SemiconjBy; decide : Commute a s), ha]
  have hars : σ a (σ r (σ s w)) = σ s w + σ r (σ s w) :=
    reflection_cubic σ (by decide) (by decide) hr has
  have hcs : σ c (σ s w) = w + σ s w :=
    reflection_cubic σ (by decide) (by decide) hs hc
  have hcr : σ c (σ r w) = σ r w := by
    rw [commute_apply σ (by unfold Commute SemiconjBy; decide : Commute c r), hc]
  have hcrs : σ c (σ r (σ s w)) = σ r w + σ r (σ s w) := by
    rw [commute_apply σ (by unfold Commute SemiconjBy; decide : Commute c r), hcs, map_add]
  have ht : ∀ g : Pair, ∀ x : Space,
      orbitMap σ w ((pairHom g).val x) = σ g (orbitMap σ w x) := by
    intro g
    apply pair_induction (fun g => ∀ x, orbitMap σ w ((pairHom g).val x) =
      σ g (orbitMap σ w x)) ?_ ?_ ?_ ?_ ?_ ?_ g
    · intro x
      simp
    · intro x
      rw [rotation_left_coordinates]
      dsimp only [orbitMap, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [map_add, map_smul, hr2]
      module
    · intro x
      rw [reflection_left_coordinates]
      dsimp only [orbitMap, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [map_add, map_smul, ha, har, has, hars]
      module
    · intro x
      rw [rotation_right_coordinates]
      dsimp only [orbitMap, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [map_add, map_smul, hsr, hs2]
      module
    · intro x
      rw [reflection_right_coordinates]
      dsimp only [orbitMap, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
        Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp only [map_add, map_smul, hc, hcr, hcs, hcrs]
      module
    · intro g h hg hh x
      rw [map_mul]
      change orbitMap σ w ((pairHom g).val ((pairHom h).val x)) = _
      rw [hg, hh, map_mul, Module.End.mul_apply]
  exact ht g x

/-- Every binary four-space with both cubic rotations fixed-point-free is
linearly equivalent to the marked determinant action. -/
theorem exists_intertwining_equiv [FiniteDimensional (ZMod 2) W]
    (hdim : Module.finrank (ZMod 2) W = 4)
    (hr : ∀ z, σ r z = z → z = 0) (hs : ∀ z, σ s z = z → z = 0) :
    ∃ f : W ≃ₗ[ZMod 2] Space, ∀ g z, f (σ g z) = (pairHom g).val (f z) := by
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) W)
  obtain ⟨w, hw, ha, hc⟩ := exists_common_fixed σ
  have hdim' : Module.finrank (ZMod 2) Space = Module.finrank (ZMod 2) W := by
    rw [hdim]
    simp [Space, VectorD, Index, Module.finrank_fintype_fun_eq_card]
  let e : Space ≃ₗ[ZMod 2] W := LinearEquiv.ofInjectiveOfFinrankEq
    (orbitMap σ w) (orbitMap_injective σ w hw ha hc hr hs) hdim'
  refine ⟨e.symm, ?_⟩
  intro g z
  apply e.injective
  rw [LinearEquiv.apply_symm_apply]
  change σ g z = orbitMap σ w ((pairHom g).val (e.symm z))
  rw [orbitMap_intertwines σ w ha hc hr hs]
  change σ g z = σ g (e (e.symm z))
  rw [LinearEquiv.apply_symm_apply]

end ClassicalOrthogonal.BinaryD2
