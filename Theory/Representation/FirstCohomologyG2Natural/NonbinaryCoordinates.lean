module

public import Theory.Representation.G2Natural

/-!
# Coordinates and regular torus elements for the natural G₂ module

The six off-diagonal octonion coordinates identify a trace-zero class modulo
scalar identities. The split torus acts diagonally with weights
`l, m, l/m, m/l, 1/m, 1/l`. When the field has characteristic two and more
than two elements, `l = t`, `m = t²` give a torus element with no fixed vectors.
This supplies the normalization step in the natural-module cocycle calculation.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(5), printed p.408 / PDF p.419. Coordinates use the attributed ATLAS
split-octonion model imported by `G2Natural`.
-/

@[expose] public section
open Atlas.SplitOctonion
namespace Atlas.G2.Natural.Nonbinary
open Explicit
variable (K : Type*) [Field K] [CharP K 2]
def nonbinaryIndex : Fin 6 → Fin 8 := ![0,1,2,5,6,7]
def offDiagonal : TraceZero K →ₗ[K] (Fin 6 → K) where
  toFun x i := x.val (nonbinaryIndex i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def coordinates : Space K →ₗ[K] (Fin 6 → K) :=
  (scalarLine K).liftQ (offDiagonal K) (by
    rw [scalarLine, Submodule.span_singleton_le_iff_mem]
    change offDiagonal K (identity K) = 0
    ext i
    fin_cases i <;> simp [offDiagonal, nonbinaryIndex, identity, unit])
@[simp] theorem coordinates_mk (x : TraceZero K) (i : Fin 6) :
    coordinates K (mk K x) i = x.val (nonbinaryIndex i) := rfl

theorem coordinates_injective : Function.Injective (coordinates K) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro v hv
  obtain ⟨x,rfl⟩ := mk_surjective K v
  have h (i : Fin 6) : x.val (nonbinaryIndex i) = 0 := congrFun hv i
  have ht : x.val 3 = x.val 4 := by
    have hh := x.property
    change x.val 3 + x.val 4 = 0 at hh
    exact (eq_neg_of_add_eq_zero_left hh).trans (CharTwo.neg_eq _)
  change mk K x = 0
  apply (mk_eq_zero_iff K x).mpr
  refine ⟨x.val 3, ?_⟩
  ext i
  fin_cases i <;> simp [unit, ← ht, nonbinaryIndex] at h ⊢
  all_goals first | exact (h 0).symm | exact (h 1).symm | exact (h 2).symm |
    exact (h 3).symm | exact (h 4).symm | exact (h 5).symm

theorem coordinates_torus (l m : Kˣ) (v : Space K) (i : Fin 6) :
    coordinates K (action K (torus l m) v) i =
      (torusWeights l m (nonbinaryIndex i) : K) * coordinates K v i := by
  obtain ⟨x,rfl⟩ := mk_surjective K v
  rfl

theorem torus_fixed_coordinate (l m : Kˣ) (v : Space K)
    (hv : action K (torus l m) v = v) (i : Fin 6)
    (hi : (torusWeights l m (nonbinaryIndex i) : K) ≠ 1) :
    coordinates K v i = 0 := by
  have h := congrArg (fun w => coordinates K w i) hv
  rw [coordinates_torus] at h
  have hz : ((torusWeights l m (nonbinaryIndex i) : K) - 1) *
      coordinates K v i = 0 := by rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hi)

theorem torus_fixed_eq_zero (l m : Kˣ) (hl : l ≠ 1) (hm : m ≠ 1)
    (hlm : l ≠ m) (v : Space K) (hv : action K (torus l m) v = v) : v = 0 := by
  apply coordinates_injective K
  ext i
  change coordinates K v i = 0
  apply torus_fixed_coordinate K l m v hv i
  have hl' : (l : K) ≠ 1 := by intro h; exact hl (Units.ext h)
  have hm' : (m : K) ≠ 1 := by intro h; exact hm (Units.ext h)
  have hlm' : (l : K) ≠ (m : K) := by exact_mod_cast hlm
  fin_cases i <;> simp [nonbinaryIndex, torusWeights, hl', hm',
    Units.val_inv_eq_inv_val, mul_inv_eq_one₀, inv_mul_eq_one₀, hlm']

theorem exists_regular_torus [Finite K] (hq : 2 < Nat.card K) :
    ∃ l m : Kˣ, l ≠ 1 ∧ m ≠ 1 ∧ l ≠ m := by
  classical
  let := Fintype.ofFinite K
  have hc : ({0,1} : Finset K).card < (Finset.univ : Finset K).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  let u : Kˣ := Units.mk0 t ht'.1
  have hu : u ≠ 1 := by intro h; exact ht'.2 (congrArg Units.val h)
  refine ⟨u, u^2, hu, ?_, ?_⟩
  · intro h
    have h' : t^2 = 1 := congrArg Units.val h
    have hh := (sq_eq_one_iff.mp h')
    rcases hh with hh | hh
    · exact ht'.2 hh
    · exact ht'.2 (hh.trans (CharTwo.neg_eq _))
  · intro h
    have hh : u * 1 = u * u := by simpa only [mul_one, pow_two] using h
    exact hu (mul_left_cancel hh).symm

end Atlas.G2.Natural.Nonbinary
