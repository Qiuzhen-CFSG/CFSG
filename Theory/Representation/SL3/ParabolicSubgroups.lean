module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Additive subgroups of the natural SL₃ parabolic modules

Elementary transvections recover full coordinate axes from a single nonzero
coordinate. Thus a proper invariant additive subgroup of the vector stabilizer
is fixed pointwise, while a nonzero invariant additive subgroup of the covector
stabilizer contains the vector plane. A commutator-generated subgroup therefore
absorbs every displacement of the whole module. Scalar closure is never assumed.

This is the natural-module calculation in Aschbacher--Smith C.4.7 and original
4.3.7, printed pp.153 and 616. The covector convention in LinearThreeFlags
makes the source projective line a two-dimensional vector plane.
-/

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

private theorem single_mem (W : AddSubgroup (Fin 3 → F))
    (P : Subgroup SL(3,F))
    (hW : ∀ g ∈ P, ∀ v ∈ W, g.val.mulVec v ∈ W)
    {v : Fin 3 → F} (hv : v ∈ W) {i j : Fin 3} (hij : i ≠ j)
    (ht : ∀ a : F, transvection hij a ∈ P) (hj : v j ≠ 0) (a : F) :
    Pi.single i a ∈ W := by
  have h := W.sub_mem (hW _ (ht (a / v j)) v hv) hv
  have he := OneCohomology.SLHigherNatural.action_transvection hij (a / v j) v
  change (transvection hij (a / v j)).val.mulVec v = _ at he
  rw [he, add_sub_cancel_left, div_mul_cancel₀ a hj] at h
  exact h

private theorem point_transvection {i j : Fin 3} (hij : i ≠ j) (hj : j ≠ 0) (a : F) :
    transvection hij a ∈ pointLocalSL F := by
  rw [mem_pointLocalSL_iff]
  simp [transvection_coe, hj]

private theorem line_transvection {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 2) (a : F) :
    transvection hij a ∈ lineLocalSL F := by
  rw [mem_lineLocalSL_iff]
  simp [transvection_coe, hi]

/-- Every proper invariant additive subgroup of the vector stabilizer is
pointwise fixed. No scalar-closure assumption on the subgroup is made. -/
theorem point_invariant_fixed (W : AddSubgroup (Fin 3 → F)) (hproper : W ≠ ⊤)
    (hW : ∀ g ∈ pointLocalSL F, ∀ v ∈ W, g.val.mulVec v ∈ W) :
    ∀ g ∈ pointLocalSL F, ∀ v ∈ W, g.val.mulVec v = v := by
  have hcoords (v : Fin 3 → F) (hv : v ∈ W) : v 1 = 0 ∧ v 2 = 0 := by
    by_contra! h
    have hbase : (∀ a : F, Pi.single (1 : Fin 3) a ∈ W) ∧
        (∀ a : F, Pi.single (2 : Fin 3) a ∈ W) := by
      by_cases h1 : v 1 = 0
      · have h2 : v 2 ≠ 0 := h h1
        have hs1 := single_mem W _ hW hv (by decide : (1 : Fin 3) ≠ 2)
          (point_transvection _ (by decide)) h2
        refine ⟨hs1, ?_⟩
        intro a
        exact single_mem W _ hW (hs1 1) (by decide : (2 : Fin 3) ≠ 1)
          (point_transvection _ (by decide)) (by simp) a
      · have hs2 := single_mem W _ hW hv (by decide : (2 : Fin 3) ≠ 1)
          (point_transvection _ (by decide)) h1
        refine ⟨?_, hs2⟩
        intro a
        exact single_mem W _ hW (hs2 1) (by decide : (1 : Fin 3) ≠ 2)
          (point_transvection _ (by decide)) (by simp) a
    have hs0 (a : F) : Pi.single (0 : Fin 3) a ∈ W :=
      single_mem W _ hW (hbase.1 1) (by decide : (0 : Fin 3) ≠ 1)
        (point_transvection _ (by decide)) (by simp) a
    apply hproper
    apply top_unique
    intro w _
    have he : w = Pi.single 0 (w 0) + Pi.single 1 (w 1) + Pi.single 2 (w 2) := by
      ext i
      fin_cases i <;> simp
    rw [he]
    exact W.add_mem (W.add_mem (hs0 _) (hbase.1 _)) (hbase.2 _)
  intro g hg v hv
  obtain ⟨h1,h2⟩ := hcoords v hv
  obtain ⟨hg0,hg1,hg2⟩ := (mem_pointLocalSL_iff F g).mp hg
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1,h2,hg0,hg1,hg2]

/-- Every nonzero invariant additive subgroup of the covector stabilizer
contains its full vector plane. -/
theorem line_plane_le (W : AddSubgroup (Fin 3 → F)) (hne : W ≠ ⊥)
    (hW : ∀ g ∈ lineLocalSL F, ∀ v ∈ W, g.val.mulVec v ∈ W) :
    ∀ v : Fin 3 → F, v 2 = 0 → v ∈ W := by
  have hex : ∃ v ∈ W, v ≠ 0 := by
    by_contra! h
    apply hne
    exact bot_unique (fun v hv => h v hv)
  obtain ⟨v,hv,hv0⟩ := hex
  have hc : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv0 (funext h)
  obtain ⟨j,hj⟩ := hc
  have hbase : (∀ a : F, Pi.single (0 : Fin 3) a ∈ W) ∧
      (∀ a : F, Pi.single (1 : Fin 3) a ∈ W) := by
    by_cases hj0 : j = 0
    · subst j
      have hs1 := single_mem W _ hW hv (by decide : (1 : Fin 3) ≠ 0)
        (line_transvection _ (by decide)) hj
      refine ⟨?_,hs1⟩
      intro a
      exact single_mem W _ hW (hs1 1) (by decide : (0 : Fin 3) ≠ 1)
        (line_transvection _ (by decide)) (by simp) a
    · have hs0 := single_mem W _ hW hv (Ne.symm hj0) (line_transvection _ (by decide : (0 : Fin 3) ≠ 2)) hj
      refine ⟨hs0,?_⟩
      intro a
      exact single_mem W _ hW (hs0 1) (by decide : (1 : Fin 3) ≠ 0)
        (line_transvection _ (by decide)) (by simp) a
  intro w hw
  have he : w = Pi.single 0 (w 0) + Pi.single 1 (w 1) := by
    ext i
    fin_cases i <;> simp [hw]
  rw [he]
  exact W.add_mem (hbase.1 _) (hbase.2 _)

/-- The natural-module displacements lie in every nonzero additive
subgroup preserved by the covector stabilizer. -/
theorem line_displacement_mem (W : AddSubgroup (Fin 3 → F)) (hne : W ≠ ⊥)
    (hW : ∀ g ∈ lineLocalSL F, ∀ v ∈ W, g.val.mulVec v ∈ W)
    (g : SL(3,F)) (hg : g ∈ lineLocalSL F) (v : Fin 3 → F) :
    g.val.mulVec v - v ∈ W := by
  apply line_plane_le W hne hW
  obtain ⟨h0,h1,h2⟩ := (mem_lineLocalSL_iff F g).mp hg
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,h0,h1,h2]
/-- A nonzero moved subgroup for the vector stabilizer is the whole module. -/
theorem point_eq_top_of_moved (W : AddSubgroup (Fin 3 → F)) (hne : W ≠ ⊥)
    (hW : ∀ g ∈ pointLocalSL F, ∀ v ∈ W, g.val.mulVec v ∈ W)
    (hmoved : ∀ S : AddSubgroup (Fin 3 → F),
      (∀ g ∈ pointLocalSL F, ∀ v ∈ W, g.val.mulVec v - v ∈ S) → W ≤ S) :
    W = ⊤ := by
  by_contra ht
  have hf := point_invariant_fixed W ht hW
  apply hne
  exact bot_unique (hmoved ⊥ (by
    intro a ha w hw
    change a.val.mulVec w - w = 0
    rw [hf a ha w hw, sub_self]))

/-- A nonzero moved subgroup for the covector stabilizer is exactly the
vector plane, even if it was initially only an additive subgroup. -/
theorem line_mem_iff_of_moved (W : AddSubgroup (Fin 3 → F)) (hne : W ≠ ⊥)
    (hW : ∀ g ∈ lineLocalSL F, ∀ v ∈ W, g.val.mulVec v ∈ W)
    (hmoved : ∀ S : AddSubgroup (Fin 3 → F),
      (∀ g ∈ lineLocalSL F, ∀ v ∈ W, g.val.mulVec v - v ∈ S) → W ≤ S)
    (v : Fin 3 → F) : v ∈ W ↔ v 2 = 0 := by
  let P : AddSubgroup (Fin 3 → F) :=
    { carrier := {w | w 2 = 0}
      zero_mem' := rfl
      add_mem' := by intro x y hx hy; change x 2 + y 2 = 0; rw [hx,hy,add_zero]
      neg_mem' := by intro x hx; change -x 2 = 0; rw [hx,neg_zero] }
  have hWP : W ≤ P := hmoved P (by
    intro g hg w _
    obtain ⟨h0,h1,h2⟩ := (mem_lineLocalSL_iff F g).mp hg
    change (g.val.mulVec w - w) 2 = 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three,h0,h1,h2])
  exact ⟨fun hv => hWP hv, line_plane_le W hne hW v⟩

/-- A nonzero invariant additive subgroup generated by its local
commutators absorbs every displacement of the whole natural module. -/
theorem displacement_mem_of_moved (P : Subgroup SL(3,F))
    (hP : P = pointLocalSL F ∨ P = lineLocalSL F)
    (W : AddSubgroup (Fin 3 → F)) (hne : W ≠ ⊥)
    (hW : ∀ g ∈ P, ∀ v ∈ W, g.val.mulVec v ∈ W)
    (hmoved : ∀ S : AddSubgroup (Fin 3 → F),
      (∀ g ∈ P, ∀ v ∈ W, g.val.mulVec v - v ∈ S) → W ≤ S)
    (g : SL(3,F)) (hg : g ∈ P) (v : Fin 3 → F) :
    g.val.mulVec v - v ∈ W := by
  rcases hP with rfl | rfl
  · rw [point_eq_top_of_moved W hne hW hmoved]
    trivial
  · exact line_displacement_mem W hne hW g hg v

end Representation.SL3ParabolicNatural
