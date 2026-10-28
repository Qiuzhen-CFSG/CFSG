module
public import Stellmacher.Recognition.LyonsU3Four.TableILargeDifferenceGeometry
public import Stellmacher.Recognition.LyonsU3Four.TableIRowMultiplicity
public import Mathlib.Tactic.IntervalCases
/-!
# Paired large differences and their finite row support

Four Galois translates of a paired magnitude-two difference exhaust every
squared difference-column norm. All other rows have four equal rotating
involution entries. After normalizing the common row sign by its nonzero
involution value, the contribution bound and congruence leave thirteen
constant rows and eight exceptional rows, the latter exactly the two four-row
orbits in Z₁ and Z₂. The finite list retains row indices for multiplicity counting.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 377–378, Cases 2(a) and 3, and Table I.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

private def rotateDiff (r : Fin 4 → ℤ) : Fin 4 → ℤ := ![r 1, r 2, r 3, r 0]
private def orbitDiff (r : Fin 4 → ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![r, rotateDiff r, rotateDiff (rotateDiff r), rotateDiff (rotateDiff (rotateDiff r))]

omit [Fintype I] in
private theorem difference_orbit (hg : d.GaloisSymmetry) (j : I) :
    ∃ e : Fin 4 → I, ∀ k i,
      d.adjacentDifference i (e k) = orbitDiff (fun i => d.adjacentDifference i j) k i := by
  obtain ⟨σ, hs⟩ := hg.adjacentDifference d
  have hr (x : I) (i : Fin 4) : d.adjacentDifference i (σ x) =
      rotateDiff (fun i => d.adjacentDifference i x) i := by
    fin_cases i
    · exact (hs x 1).symm
    · exact (hs x 2).symm
    · exact (hs x 3).symm
    · exact (hs x 0).symm
  refine ⟨![j, σ j, σ (σ j), σ (σ (σ j))], ?_⟩
  intro k i
  fin_cases k <;> simp [orbitDiff, hr]

private theorem orbit_injective (ε : ℤ) (he : ε ^ 2 = 1)
    (r : Fin 4 → ℤ)
    (hr : r = (fun i => ε * ![2, -2, 0, 0] i) ∨
      r = (fun i => ε * ![2, 0, 0, -2] i)) : Function.Injective (orbitDiff r) := by
  rcases sq_eq_one_iff.mp he with he | he <;>
    rcases hr with rfl | rfl <;> subst ε <;> decide

private theorem orbit_norm (ε : ℤ) (he : ε ^ 2 = 1)
    (r : Fin 4 → ℤ)
    (hr : r = (fun i => ε * ![2, -2, 0, 0] i) ∨
      r = (fun i => ε * ![2, 0, 0, -2] i)) (i : Fin 4) :
    ∑ k, (orbitDiff r k i)^2 = 8 := by
  rcases sq_eq_one_iff.mp he with he | he <;>
    rcases hr with rfl | rfl <;> subst ε <;> fin_cases i <;> decide

/-- Four Galois translates exhaust the difference-column norms. -/
theorem paired_difference_support (h : d.Equation3_2) (hg : d.GaloisSymmetry)
    (hp : d.HasPairedLargeDifferences) :
    ∃ (e : Fin 4 ↪ I),
      (∀ j, (∀ k, j ≠ e k) → ∀ i, d.adjacentDifference i j = 0) ∧
      (∀ j, ∃ a δ : ℤ, ∃ k : Fin 4, (δ = 0 ∨ δ = 2 ∨ δ = -2) ∧
        ∀ i : Fin 4, d.iDz i.succ j = a + if i = k then δ else 0) := by
  classical
  obtain ⟨j, ε, hε, hj⟩ := hp
  obtain ⟨e, he⟩ := d.difference_orbit hg j
  have hinj : Function.Injective e := by
    intro a b hab
    apply orbit_injective ε hε _ hj
    funext i
    rw [← he, ← he, hab]
  have hn (i : Fin 4) : ∑ k, d.adjacentDifference i (e k)^2 = 8 := by
    simp_rw [he]
    exact orbit_norm ε hε _ hj i
  have hz (x : I) (hx : ∀ k, x ≠ e k) (i : Fin 4) :
      d.adjacentDifference i x = 0 := by
    let s : Finset I := Finset.univ.image e
    have hs : ∑ y ∈ s, d.adjacentDifference i y ^ 2 = 8 := by
      rw [Finset.sum_image]
      · exact hn i
      · exact fun a _ b _ hab => hinj hab
    have hx' : x ∉ s := by simp [s, eq_comm, hx]
    have hb : ∑ y ∈ insert x s, d.adjacentDifference i y ^ 2 ≤ 8 := by
      rw [← h.adjacentDifference_sq_sum d i]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_insert hx', hs] at hb
    nlinarith [sq_nonneg (d.adjacentDifference i x)]
  refine ⟨⟨e, hinj⟩, hz, ?_⟩
  intro x
  by_cases hx : ∃ k, x = e k
  · obtain ⟨k, rfl⟩ := hx
    have hh := he k
    generalize e k = y at hh ⊢
    rcases sq_eq_one_iff.mp hε with hε | hε <;>
      rcases hj with hj | hj <;> subst ε <;> rw [hj] at hh
    all_goals
      fin_cases k <;>
        simp [orbitDiff, rotateDiff, adjacentDifference] at hh
    all_goals
      have h0 := hh 0
      have h1 := hh 1
      have h2 := hh 2
      have h3 := hh 3
      simp at h0 h1 h2 h3
    all_goals
      first
      | refine ⟨d.iDz 1 y, 2, 1, Or.inr (Or.inl rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 1 y, -2, 1, Or.inr (Or.inr rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 1 y, 2, 2, Or.inr (Or.inl rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 1 y, -2, 2, Or.inr (Or.inr rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 1 y, 2, 3, Or.inr (Or.inl rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 1 y, -2, 3, Or.inr (Or.inr rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 2 y, 2, 0, Or.inr (Or.inl rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
      | refine ⟨d.iDz 2 y, -2, 0, Or.inr (Or.inr rfl), ?_⟩
        intro i; fin_cases i <;> simp <;> omega
  · have hh := hz x (by simpa using hx)
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    simp [adjacentDifference] at h0 h1 h2
    refine ⟨d.iDz 1 x, 0, 0, Or.inl rfl, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData



namespace Stellmacher.Recognition.LyonsU3Four.TableIPairedRows

def row : Fin 21 → TableIRow := ![
  ![-3, 1, 0, 0, 0, 0],
  ![-3, 1, 1, 1, 1, 1],
  ![-2, 2, 1, 1, 1, 1],
  ![-2, 2, 2, 2, 2, 2],
  ![-1, -1, 1, 1, 1, 1],
  ![-1, 3, 2, 2, 2, 2],
  ![-1, 3, 3, 3, 3, 3],
  ![0, 0, 1, 1, 1, 1],
  ![1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![2, 2, 1, 1, 1, 1],
  ![2, 2, 2, 2, 2, 2],
  ![-1, 1, -1, 1, 1, 1],
  ![-1, 1, 1, -1, 1, 1],
  ![-1, 1, 1, 1, -1, 1],
  ![-1, 1, 1, 1, 1, -1],
  ![-1, 1, 2, 0, 0, 0],
  ![-1, 1, 0, 2, 0, 0],
  ![-1, 1, 0, 0, 2, 0],
  ![-1, 1, 0, 0, 0, 2]]

def rotate (r : TableIRow) : TableIRow := ![r 0, r 1, r 5, r 2, r 3, r 4]
def rotation : Fin 21 → Fin 21 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 13, 18, 19, 20, 17]

theorem row_injective : Function.Injective row := by decide

theorem row_rotation (k : Fin 21) : row (rotation k) = rotate (row k) := by
  revert k
  decide

theorem rotate_injective : Function.Injective rotate := by
  intro r s h
  funext k
  fin_cases k
  · exact congrFun h 0
  · exact congrFun h 1
  · exact congrFun h 3
  · exact congrFun h 4
  · exact congrFun h 5
  · exact congrFun h 2

def z (r : TableIRow) : ℤ := ∑ i : Fin 5, r i.succ

def contribution (r : TableIRow) : ℤ :=
  4 * r 0 ^ 2 + (∑ i : Fin 5, r i.succ ^ 2) +
    3 * ∑ i : Fin 5, ∑ h ∈ Finset.Iio i, (r h.succ - r i.succ)^2

def shape (t x a δ : ℤ) (k : Fin 4) : TableIRow :=
  ![![t,x,a+δ,a,a,a], ![t,x,a,a+δ,a,a],
    ![t,x,a,a,a+δ,a], ![t,x,a,a,a,a+δ]] k

def gram (k l : Fin 6) : ℤ :=
  if k = 0 then (if l = 0 then 16 else 0)
  else if l = 0 then 0 else 4 * (3 + if k = l then 1 else 0)

structure MultiplicityConditions (n : Fin 21 → ℕ) : Prop where
  principal_pos : 0 < n 8
  rotation_eq : ∀ k, n (rotation k) = n k
  gram_eq : ∀ k l, ∑ a, (n a : ℤ) * row a k * row a l = gram k l

private def q (t x a e : ℤ) : ℤ :=
  4*t^2 + x^2 + 3*a^2 + (a+e)^2 + 9*(x-a)^2 + 3*(x-a-e)^2 + 9*e^2

private theorem q_bounds (t x a e : ℤ) (h : q t x a e < 64) :
    (-3 ≤ t ∧ t ≤ 3) ∧ (-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ a ∧ a ≤ 3) := by
  dsimp [q] at h
  have ht : 4*t^2 < 64 := by
    nlinarith only [h, sq_nonneg x, sq_nonneg a, sq_nonneg (a+e),
      sq_nonneg (x-a), sq_nonneg (x-a-e), sq_nonneg e]
  have hx : 4*x^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (3*x-4*a-e), sq_nonneg e]
  have ha : 4*a^2 < 64 := by
    nlinarith only [h, sq_nonneg t, sq_nonneg (x+e), sq_nonneg (x-a),
      sq_nonneg (x-a-e), sq_nonneg e]
  constructor
  · constructor <;> nlinarith only [ht]
  constructor
  · constructor <;> nlinarith only [hx]
  · constructor <;> nlinarith only [ha]

private theorem contribution_explicit (t x a b c d : ℤ) : contribution ![t,x,a,b,c,d] =
    4*t^2+x^2+a^2+b^2+c^2+d^2+
    3*((x-a)^2+(x-b)^2+(a-b)^2+(x-c)^2+(a-c)^2+(b-c)^2+
      (x-d)^2+(a-d)^2+(b-d)^2+(c-d)^2) := by
  have hi (i : Fin 5) : Finset.Iio i = Finset.univ.filter (· < i) := by
    ext j; simp
  simp [contribution, hi, Finset.sum_filter, Fin.sum_univ_succ]
  ring

private theorem shape_contribution (t x a e : ℤ) (k : Fin 4) :
    contribution (shape t x a e k) = q t x a e := by
  fin_cases k <;> simp [shape, contribution_explicit, q] <;> ring

private theorem shape_z (t x a e : ℤ) (k : Fin 4) :
    z (shape t x a e k) = x + 4*a + e := by
  fin_cases k <;> simp [shape, z, Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem finite_coverage : ∀ t x a : Fin 7, ∀ e : Fin 3,
    q ((t:ℤ)-3) ((x:ℤ)-3) ((a:ℤ)-3) (2*((e:ℤ)-1)) < 64 →
    Int.ModEq 4 ((t:ℤ)-3) (((x:ℤ)-3) + 4*((a:ℤ)-3) + 2*((e:ℤ)-1)) →
    0 < ((x:ℤ)-3) + 4*((a:ℤ)-3) + 2*((e:ℤ)-1) →
    ∀ k : Fin 4, ∃ j : Fin 21,
      shape ((t:ℤ)-3) ((x:ℤ)-3) ((a:ℤ)-3) (2*((e:ℤ)-1)) k = row j := by
  decide

private theorem bounded_seven (x : ℤ) (h : -3 ≤ x ∧ x ≤ 3) :
    ∃ k : Fin 7, x = (k : ℤ) - 3 := by
  refine ⟨⟨(x+3).toNat, by omega⟩, ?_⟩
  change x = ((x+3).toNat : ℤ) - 3
  omega

theorem shape_covered (t x a δ : ℤ) (k : Fin 4)
    (hδ : δ = 0 ∨ δ = 2 ∨ δ = -2)
    (hc : contribution (shape t x a δ k) < 64)
    (hm : Int.ModEq 4 t (z (shape t x a δ k)))
    (hz : 0 < z (shape t x a δ k)) :
    ∃ j : Fin 21, shape t x a δ k = row j := by
  rw [shape_contribution] at hc
  rw [shape_z] at hm hz
  obtain ⟨ht, hx, ha⟩ := q_bounds t x a δ hc
  obtain ⟨t', rfl⟩ := bounded_seven t ht
  obtain ⟨x', rfl⟩ := bounded_seven x hx
  obtain ⟨a', rfl⟩ := bounded_seven a ha
  have he : ∃ e : Fin 3, δ = 2*((e : ℤ)-1) := by
    rcases hδ with rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
  obtain ⟨e, rfl⟩ := he
  exact finite_coverage t' x' a' e hc hm hz k
end Stellmacher.Recognition.LyonsU3Four.TableIPairedRows
