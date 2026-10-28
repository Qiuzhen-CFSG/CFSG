module

public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.OrderTwoFour
public import Theory.Combinatorics.SimpleGraph.OctagonShortPaths.OppositionAlgebra

/-!
# Opposition determines the point graph of an octagon of order (2,4)

On the zero-color fiber, half the incidence distance takes values zero through
four. The proved weighted point-neighbor sum gives all four distance-matrix
recurrences, and the opposition-square identity recovers adjacency from exactly
512 common opposites. Thus any opposition-preserving permutation preserves the
point graph. No transitivity, recurrence or opposition-count input is assumed.

Source: Aschbacher–Smith J.5.6–12, printed pp.447–449.
-/

public noncomputable section
namespace SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
open scoped BigOperators
open SimpleGraph.OctagonOpposition
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (D : OrderTwoFourDatum G)
attribute [local instance] Classical.propDecidable

abbrev Point := {v : V // D.color v=0}

local instance : DecidableEq (D.Point) := Classical.decEq _

@[expose] def pointDistance (u v : D.Point) : Fin 5 :=
  ⟨G.dist u v / 2, by have h := D.diameter u v; omega⟩

theorem twice_pointDistance (u v : D.Point) :
    2*(D.pointDistance u v : ℕ)=G.dist u v := by
  obtain ⟨k,hk⟩ := D.even_point_distance u.property v.property
  change 2*(G.dist u v/2)=G.dist u v
  omega

theorem pointDistance_eq_iff (u v : D.Point) (i : Fin 5) :
    D.pointDistance u v=i ↔ G.dist u v=2*(i:ℕ) := by
  have h := D.twice_pointDistance u v
  constructor
  · intro he; rw [he] at h; exact h.symm
  · intro he; apply Fin.ext; omega

theorem pointDistance_zero (u v : D.Point) : D.pointDistance u v=0 ↔ u=v := by
  rw [D.pointDistance_eq_iff]
  simp only [Fin.val_zero,mul_zero,D.connected.dist_eq_zero_iff,Subtype.ext_iff]

theorem pointDistance_symm (u v : D.Point) : D.pointDistance u v=D.pointDistance v u := by
  apply Fin.ext
  change G.dist u v/2=G.dist v u/2
  rw [dist_comm]

theorem point_sum_eq (u : D.Point) (f : V → ℤ) :
    (∑ w : D.Point, if G.dist u w=2 then f w else 0) =
      ∑ w : V, if G.dist u w=2 then f w else 0 := by
  classical
  let S := Finset.univ.filter (fun w=> D.color w=0)
  rw [← Finset.sum_subtype (p := fun w => D.color w=0) S (by simp [S])
    (fun w=>if G.dist (u:V) w=2 then f w else 0)]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro w hw hnot
  have hnotcolor : D.color w≠0 := by simpa [S] using hnot
  have hdist : G.dist (u:V) w≠2 := by
    intro hh
    have hc := distance_color D.connected D.color D.color_adj (u:V) w
    rw [u.property,hh,zero_add] at hc
    exact hnotcolor (hc.symm.trans (by decide : (2:ZMod 2)=0))
  simp [hdist]

theorem matrix_product_sum (u v : D.Point) (j : Fin 5) :
    (distanceMatrix D.pointDistance 1*distanceMatrix D.pointDistance j) u v =
      ∑ w : V, if G.dist u w=2 then (if G.dist w v=2*(j:ℕ) then (1:ℤ) else 0) else 0 := by
  rw [Matrix.mul_apply,←D.point_sum_eq]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [distanceMatrix,D.pointDistance_eq_iff,Fin.val_one,mul_one]
  split_ifs <;> simp_all

theorem matrix_product_entry (u v : D.Point) (j : Fin 5) :
    (distanceMatrix D.pointDistance 1*distanceMatrix D.pointDistance j) u v =
      ![10*(if j=1 then (1:ℤ) else 0),
        (if j=0 then 1 else 0)+(if j=1 then 1 else 0)+8*(if j=2 then 1 else 0),
        (if j=1 then 1 else 0)+(if j=2 then 1 else 0)+8*(if j=3 then 1 else 0),
        (if j=2 then 1 else 0)+(if j=3 then 1 else 0)+8*(if j=4 then 1 else 0),
        5*(if j=3 then 1 else 0)+5*(if j=4 then 1 else 0)] (D.pointDistance u v) := by
  rw [D.matrix_product_sum]
  have hs := D.double_point_sum u v u.property v.property (fun n=>if n=2*(j:ℕ) then (1:ℤ) else 0)
  have hd := D.twice_pointDistance u v
  generalize he : D.pointDistance u v=k at hd ⊢
  rw [←hd] at hs
  fin_cases k <;> fin_cases j <;> norm_num at hs ⊢ <;> exact hs

private theorem scalar_entry (n : ℕ) [n.AtLeastTwo] (M : Matrix D.Point D.Point ℤ) (u v : D.Point) :
    ((ofNat(n) : Matrix D.Point D.Point ℤ) * M) u v = (ofNat(n) : ℤ) * M u v := by
  change (((n : Matrix D.Point D.Point ℤ) * M) u v) = (n : ℤ) * M u v
  rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul]

theorem recurrence : Recurrence D.pointDistance := by
  constructor
  all_goals ext u v
  · rw [D.matrix_product_entry]
    simp only [Matrix.add_apply,Matrix.ofNat_apply]
    generalize hd : D.pointDistance u v=k
    fin_cases k <;> simp [distanceMatrix,←D.pointDistance_zero u v,hd]
  · rw [D.matrix_product_entry]
    simp only [Matrix.add_apply,scalar_entry]
    generalize hd : D.pointDistance u v=k
    fin_cases k <;> simp [distanceMatrix,hd]
  · rw [D.matrix_product_entry]
    simp only [Matrix.add_apply,scalar_entry]
    generalize hd : D.pointDistance u v=k
    fin_cases k <;> simp [distanceMatrix,hd]
  · rw [D.matrix_product_entry]
    simp only [Matrix.add_apply,scalar_entry]
    generalize hd : D.pointDistance u v=k
    fin_cases k <;> simp [distanceMatrix,hd]

theorem adjacency_iff_common_opposites (u v : D.Point) :
    G.dist (u:V) v=2 ↔
      (Finset.univ.filter (fun w : D.Point=>G.dist (u:V) w=8 ∧ G.dist (v:V) w=8)).card=512 := by
  simpa [D.pointDistance_eq_iff] using
    adjacency_from_opposition D.pointDistance D.pointDistance_zero D.pointDistance_symm D.recurrence u v

theorem adjacency_preserved (e : D.Point ≃ D.Point)
    (hop : ∀ u v : D.Point,G.dist (e u:V) (e v)=8 ↔ G.dist (u:V) v=8)
    (u v : D.Point) : G.dist (e u:V) (e v)=2 ↔ G.dist (u:V) v=2 := by
  have hop' : ∀ u v,D.pointDistance (e u) (e v)=4 ↔ D.pointDistance u v=4 := by
    intro u v
    simpa [D.pointDistance_eq_iff] using hop u v
  simpa only [D.pointDistance_eq_iff,Fin.val_one,mul_one] using
    adjacency_invariant_of_opposition D.pointDistance D.pointDistance_zero
      D.pointDistance_symm D.recurrence e hop' u v

end SimpleGraph.OctagonShortPaths.OrderTwoFourDatum
