module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.FixedSpaces
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Matrices in the shear centralizer

Fixing Λ²Γ₃ and Γ₁∧Γ₄ pointwise leaves just two upper-left blocks:
the identity and the transvection e₄ ↦ e₄ + e₁. The remaining column is
an arbitrary last-column shear. We check the small binary minor calculation
by case splitting in the kernel and use it on the actual exterior action.
Source: Aschbacher--Smith 12.5.7/10, printed pp.820--821.
-/

@[expose] public section
open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- The pointwise centralizer of the two 3-spaces, restricted to the 4-parabolic. -/
noncomputable def C : Subgroup Group :=
  BinaryOffender.subspaceKernel (exteriorAction 2) (V₃ ⊔ V₃') (parabolic 4)

/-- The pointwise centralizer of `V₆` inside the 4-parabolic. -/
noncomputable def pointwiseV₆ : Subgroup Group :=
  BinaryOffender.subspaceKernel (exteriorAction 2) V₆ (parabolic 4)

def upperLeft (g : Group) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => g.val i.castSucc j.castSucc

private theorem actionMatrix_fixed_basis (g : Group) (t s : Fin 10)
    (h : exteriorAction 2 g (basis t) = basis t) :
    actionMatrix g s t = if s = t then 1 else 0 := by
  have he := congrArg (fun x : V => coordinates x s) h
  rw [coordinates_action, coordinates_basis] at he
  fin_cases s <;> simp [Matrix.mulVec, dotProduct, Pi.single_apply] at he ⊢
  all_goals assumption

private def wedge6 (s : Fin 6) : Fin 10 := ![0, 1, 2, 4, 5, 7] s

private def pair6 (s : Fin 6) : Fin 2 → Fin 4 :=
  ![![0,1], ![0,2], ![0,3], ![1,2], ![1,3], ![2,3]] s

private def minor4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (i j k l : Fin 4) : ZMod 2 :=
  A i k * A j l + A i l * A j k

private def fixed4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ s t : Fin 6,
    minor4 A (pair6 s 0) (pair6 s 1) (pair6 t 0) (pair6 t 1) = if s = t then 1 else 0

private def smallWedge (s : Fin 4) : Fin 10 := ![0, 1, 2, 4] s

private def pairSmall (s : Fin 4) : Fin 2 → Fin 4 :=
  ![![0,1], ![0,2], ![0,3], ![1,2]] s

private def fixedSmall4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ s : Fin 6, ∀ t : Fin 4,
    minor4 A (pair6 s 0) (pair6 s 1) (pairSmall t 0) (pairSmall t 1) =
      if wedge6 s = smallWedge t then 1 else 0

def trans4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if i = 0 ∧ j = 3 then 1 else if i = j then 1 else 0

private theorem matrix4_eq_one_or_trans4_of_fixedSmall (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h : fixedSmall4 A) : A = 1 ∨ A = trans4 := by
  simp only [fixedSmall4, Fin.forall_fin_succ, pair6, pairSmall, wedge6, smallWedge,
    Matrix.cons_val_zero, Matrix.cons_val_one, minor4] at h
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 0 0) with h00 | h00 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 1 0) with h10 | h10 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 2 0) with h20 | h20 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 3 0) with h30 | h30 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 0 1) with h01 | h01 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 1 1) with h11 | h11 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 2 1) with h21 | h21 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 3 1) with h31 | h31 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 0 2) with h02 | h02 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 1 2) with h12 | h12 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 2 2) with h22 | h22 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 3 2) with h32 | h32 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 0 3) with h03 | h03 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 1 3) with h13 | h13 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 2 3) with h23 | h23 <;> try simp_all
  all_goals rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (A 3 3) with h33 | h33 <;> try simp_all
  all_goals
    first
    | solve | left; ext i j; fin_cases i <;> fin_cases j <;> simp_all
    | right; ext i j; fin_cases i <;> fin_cases j <;> simp_all [trans4]

private theorem matrix4_eq_one_of_fixed (A : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h : fixed4 A) : A = 1 := by
  have hs : fixedSmall4 A := by
    simp_all [fixed4, fixedSmall4, Fin.forall_fin_succ, minor4, pair6, pairSmall,
      wedge6, smallWedge]
  rcases matrix4_eq_one_or_trans4_of_fixedSmall A hs with he | he
  · exact he
  · have hh := h 0 4
    simp [he, minor4, pair6, trans4] at hh

private theorem upperLeft_fixed_of_fixed_V₆ (g : Group)
    (h : ∀ v ∈ V₆, exteriorAction 2 g v = v) : fixed4 (upperLeft g) := by
  intro s t
  have hs : wedge6 s ∈ ({0,1,2,4,5,7} : Finset (Fin 10)) := by
    fin_cases s <;> simp [wedge6]
  have ht : wedge6 t ∈ ({0,1,2,4,5,7} : Finset (Fin 10)) := by
    fin_cases t <;> simp [wedge6]
  have hh := actionMatrix_fixed_basis g (wedge6 t) (wedge6 s)
    (h _ (Submodule.subset_span ⟨wedge6 t, ht, rfl⟩))
  fin_cases s <;> fin_cases t <;>
    simp_all [actionMatrix, upperLeft, wedge6, pair6, pair, minor4,
      sub_eq_add_neg, ZMod.neg_eq_self_mod_two, mul_comm]
  all_goals ring_nf at hh ⊢; exact hh


set_option maxHeartbeats 1000000 in
private theorem upperLeft_fixed_of_fixed_C (g : Group)
    (hg : g ∈ C) : fixedSmall4 (upperLeft g) := by
  change g ∈ parabolic 4 ∧ (∀ v ∈ V₃ ⊔ V₃', exteriorAction 2 g v = v) at hg
  intro s t
  have hs : wedge6 s ∈ ({0,1,2,4,5,7} : Finset (Fin 10)) := by
    fin_cases s <;> simp [wedge6]
  have ht : smallWedge t ∈ ({0,1,2,4} : Finset (Fin 10)) := by
    fin_cases t <;> simp [smallWedge]
  have hmem : basis (smallWedge t) ∈ V₃ ⊔ V₃' := by
    rw [V₃, V₃', ← coordinateSpan_union]
    apply Submodule.subset_span
    fin_cases t <;> simp [smallWedge]
  have hh := actionMatrix_fixed_basis g (smallWedge t) (wedge6 s) (hg.2 _ hmem)
  fin_cases s <;> fin_cases t <;>
    simp_all [actionMatrix, upperLeft, wedge6, smallWedge, pair6, pairSmall, pair,
      minor4, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, mul_comm]
  all_goals ring_nf at hh ⊢; exact hh

def shearParameterOf (g : Group) : ShearParameter := fun i => g.val i.castSucc 4

theorem upperLeft_C_cases (g : Group) (hg : g ∈ C) :
    upperLeft g = 1 ∨ upperLeft g = trans4 := by
  exact matrix4_eq_one_or_trans4_of_fixedSmall _ (upperLeft_fixed_of_fixed_C g hg)


def tau : Group :=
  Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 3) 1

theorem tau_matrix : tau.val =
    (fun i j : Fin 5 => if i = 0 ∧ j = 3 then 1 else if i = j then 1 else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tau, Matrix.SpecialLinearGroup.transvection, Matrix.transvection]

private theorem g_eq_shear_of_upperLeft (g : Group) (hg : g ∈ parabolic 4)
    (hA : upperLeft g = 1) : g = shear (shearParameterOf g) := by
  have hlow := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have hdne : g.val 4 4 ≠ 0 := by
    intro hd
    have hr := g.row_ne_zero 4
    apply hr
    funext j
    fin_cases j
    all_goals simp [hlow, hd]
  have hd : g.val 4 4 = 1 := by
    exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) _ |>.resolve_left hdne
  have htop (i j : Fin 5) (hi : i.val < 4) (hj : j.val < 4) :
      g.val i j = if i = j then 1 else 0 := by
    have hx := congrFun (congrFun hA ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simpa [upperLeft, Matrix.one_apply, Fin.ext_iff] using hx
  apply Subtype.ext
  rw [matrix_shear]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp_all [shearParameterOf]

private theorem g_eq_shear_mul_tau_of_upperLeft (g : Group) (hg : g ∈ parabolic 4)
    (hA : upperLeft g = trans4) :
    g = shear (shearParameterOf g) * tau := by
  have hlow := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have hdne : g.val 4 4 ≠ 0 := by
    intro hd
    have hr := g.row_ne_zero 4
    apply hr
    funext j
    fin_cases j
    all_goals simp [hlow, hd]
  have hd : g.val 4 4 = 1 := by
    exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) _ |>.resolve_left hdne
  have htop (i j : Fin 5) (hi : i.val < 4) (hj : j.val < 4) :
      g.val i j = trans4 ⟨i.val, hi⟩ ⟨j.val, hj⟩ := by
    exact congrFun (congrFun hA ⟨i.val, hi⟩) ⟨j.val, hj⟩
  apply Subtype.ext
  ext i j
  change g.val i j = ∑ k, (shear (shearParameterOf g)).val i k * tau.val k j
  simp only [matrix_shear, tau_matrix]
  fin_cases i <;> fin_cases j
  all_goals simp_all [shearParameterOf, trans4, Fin.sum_univ_succ] <;> decide

theorem C_eq_shear_or_shear_mul_tau (g : Group) (hg : g ∈ C) :
    g = shear (shearParameterOf g) ∨
      g = shear (shearParameterOf g) * tau := by
  rcases upperLeft_C_cases g hg with hA | hA
  · exact Or.inl (g_eq_shear_of_upperLeft g hg.1 hA)
  · exact Or.inr (g_eq_shear_mul_tau_of_upperLeft g hg.1 hA)

theorem upperLeft_eq_one_of_fixed_V₆ (g : Group) (_hg : g ∈ parabolic 4)
    (h : ∀ v ∈ V₆, exteriorAction 2 g v = v) : upperLeft g = 1 := by
  exact matrix4_eq_one_of_fixed _ (upperLeft_fixed_of_fixed_V₆ g h)

theorem fixed_V₆_in_parabolic_eq_shear (g : Group)
    (hg : g ∈ parabolic 4) (h : ∀ v ∈ V₆, exteriorAction 2 g v = v) :
    g = shear (shearParameterOf g) := by
  have hA := upperLeft_eq_one_of_fixed_V₆ g hg h
  have htop (i j : Fin 5) (hi : i.val < 4) (hj : j.val < 4) :
      g.val i j = if i = j then 1 else 0 := by
    have hx := congrFun (congrFun hA ⟨i.val, hi⟩) ⟨j.val, hj⟩
    simpa [upperLeft, Matrix.one_apply, Fin.ext_iff] using hx
  have hlow := (mem_parabolic_iff_lowerLeft_zero 4 g).mp hg
  have hdne : g.val 4 4 ≠ 0 := by
    intro hd
    have hr := g.row_ne_zero 4
    apply hr
    funext j
    fin_cases j
    all_goals simp [hlow, hd]
  have hd : g.val 4 4 = 1 := by
    exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) _ |>.resolve_left hdne
  apply Subtype.ext
  rw [matrix_shear]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp_all [shearParameterOf]


theorem V₃_le_V₆ : V₃ ≤ V₆ := by
  rw [V₃, V₆]
  apply Submodule.span_mono
  exact Set.image_mono (by simp)

theorem V₃'_le_V₆ : V₃' ≤ V₆ := by
  rw [V₃', V₆]
  apply Submodule.span_mono
  exact Set.image_mono (by simp)

theorem sup_V₃_V₃'_le_V₆ : V₃ ⊔ V₃' ≤ V₆ := sup_le V₃_le_V₆ V₃'_le_V₆

theorem shear_mem_parabolic_four (u : ShearParameter) : shear u ∈ parabolic 4 := by
  apply (mem_parabolic_iff_lowerLeft_zero 4 _).mpr
  intro i j hi hj
  rw [matrix_shear]
  fin_cases i <;> fin_cases j <;> simp_all

theorem shear_fix_V₆ (u : ShearParameter) : V₆ ≤ fixedSpace (shear u) := by
  intro v hv
  rw [mem_fixedSpace]
  rw [shear_action]
  rw [(mem_V₆_iff_shearQuotient v).mp hv]
  apply coordinates.injective
  rw [show shearWedge 0 u = 0 from (shearWedge_eq_zero_iff 0 u).mpr (Or.inl rfl)]
  simp

theorem shear_le_C : shearSubgroup ≤ C := by
  intro g hg
  obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp hg
  refine ⟨shear_mem_parabolic_four u, ?_⟩
  intro v hv
  exact (mem_fixedSpace _ _).mp (shear_fix_V₆ u (sup_V₃_V₃'_le_V₆ hv))

theorem pointwiseV₆_eq_shearSubgroup : pointwiseV₆ = shearSubgroup := by
  apply le_antisymm
  · intro g hg
    change g ∈ parabolic 4 ∧ (∀ v ∈ V₆, exteriorAction 2 g v = v) at hg
    exact (mem_shearSubgroup g).mpr ⟨shearParameterOf g,
      (fixed_V₆_in_parabolic_eq_shear g hg.1 hg.2).symm⟩
  · intro g hg
    obtain ⟨u, rfl⟩ := (mem_shearSubgroup g).mp hg
    refine ⟨shear_mem_parabolic_four u, ?_⟩
    intro v hv
    exact (mem_fixedSpace _ _).mp (shear_fix_V₆ u hv)

end Representation.SL5ExteriorSquare
