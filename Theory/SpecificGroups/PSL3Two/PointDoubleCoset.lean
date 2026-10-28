module
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-!
# The two point-parabolic double cosets in SL₃(2)

Six literal matrices fixing the first coordinate send the second coordinate
to each of the other nonzero vectors. Thus every matrix outside the point
stabilizer lies in its double coset of the coordinate swap. The certificate
checks just these six movers; the decomposition for arbitrary matrices is
proved by the actual vector action.
Source: the binary seven-point geometry in MS93 (1.6), pp.845--847.
-/

@[expose] public section
open Matrix Subgroup
namespace Matrix.PSL3Two
namespace PointDoubleCoset
private def mover : Fin 6 → SL := ![
  ⟨!![1,0,0;0,1,0;0,0,1],by decide⟩,
  ⟨!![1,1,0;0,1,0;0,0,1],by decide⟩,
  ⟨!![1,0,0;0,0,1;0,1,0],by decide⟩,
  ⟨!![1,1,0;0,0,1;0,1,0],by decide⟩,
  ⟨!![1,0,0;0,1,0;0,1,1],by decide⟩,
  ⟨!![1,1,0;0,1,0;0,1,1],by decide⟩]
def swap : SL := ⟨!![0,1,0;1,0,0;0,0,1],by decide⟩

private theorem fixes_base (g : SL) : g∈pointParabolicSL ↔
    g • (![1,0,0] : Fin 3 → ZMod 2) = ![1,0,0] := by
  rw [mem_pointParabolicSL_iff]
  constructor
  · rintro ⟨h1,h2⟩
    have h00 : g.val 0 0 ≠ 0 := by
      intro hz
      have hd := g.property
      simp only [det_fin_three,hz,h1,h2,zero_mul,mul_zero,add_zero,sub_zero] at hd
      exact zero_ne_one hd
    have hb : ∀ x : ZMod 2, x≠0 → x=1 := by decide
    have h0 := hb _ h00
    change g.val.mulVec ![1,0,0] = ![1,0,0]
    ext i
    fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,h0,h1,h2]
  · intro hg
    change g.val.mulVec ![1,0,0] = ![1,0,0] at hg
    constructor
    · simpa [mulVec,dotProduct,Fin.sum_univ_three] using congrFun hg 1
    · simpa [mulVec,dotProduct,Fin.sum_univ_three] using congrFun hg 2

private theorem mover_mem (i : Fin 6) : mover i∈pointParabolicSL := by
  rw [mem_pointParabolicSL_iff]
  fin_cases i <;> decide

private theorem reach_other (v : Fin 3 → ZMod 2) (hv : v≠0)
    (hne : v≠![1,0,0]) : ∃ i : Fin 6, (mover i) • (![0,1,0] : Fin 3 → ZMod 2) = v := by
  have h : ∀ v : Fin 3 → ZMod 2, v≠0 → v≠![1,0,0] →
      ∃ i : Fin 6, (mover i).val.mulVec ![0,1,0] = v := by decide +kernel
  exact h v hv hne

theorem swap_square : swap^2=1 := by decide

theorem swap_not_mem : swap∉pointParabolicSL := by
  rw [mem_pointParabolicSL_iff]
  decide

theorem decomposition (g : SL) (hg : g∉pointParabolicSL) :
    ∃ a∈pointParabolicSL, ∃ b∈pointParabolicSL, g=a*swap*b := by
  have hv : g • (![1,0,0] : Fin 3 → ZMod 2)≠0 :=
    (smul_ne_zero_iff_ne g).mpr (by decide)
  have hne : g • (![1,0,0] : Fin 3 → ZMod 2)≠![1,0,0] := fun h => hg ((fixes_base g).mpr h)
  obtain ⟨i,hi⟩ := reach_other _ hv hne
  let a := mover i
  let b := (a*swap)⁻¹*g
  have he : (a*swap) • (![1,0,0] : Fin 3 → ZMod 2) = g • ![1,0,0] := by
    rw [mul_smul]
    exact hi
  refine ⟨a,mover_mem i,b,?_,?_⟩
  · rw [fixes_base]
    change ((a*swap)⁻¹*g) • (![1,0,0] : Fin 3 → ZMod 2)=![1,0,0]
    rw [mul_smul,← he,inv_smul_smul]
  · dsimp [b]
    group
end PointDoubleCoset
end Matrix.PSL3Two
