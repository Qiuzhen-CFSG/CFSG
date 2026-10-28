module

public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import Theory.SpecificGroups.PSL3Four.Collineations.MatrixFrames
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.FivePointQuotients.Action

/-!
# A frame stabilizer in PG(2,4) has at most two elements

Use the normalized points `[0,0,1]`, `[0,1,a]`, and `[1,a,b]`.
A frame and the extra point `[1,ω,0]` generate all 21 points by joins and
intersections. The displayed local field identities check these constructions.
The frame itself fixes the three prime-field points of the line at infinity,
so the extra point has only two possible images. This bounds the pointwise
frame stabilizer by two, without assuming a semilinear representation.

Source: the elementary PG(2,4) calculation for the plane-action step of
Aschbacher–Smith F.4.8(2), printed p.278. The coordinate rigidity proof follows
the pattern of `Theory/Combinatorics/ProjectivePlaneThreeFrameRigidity.lean`.
-/

open Matrix Projectivization Configuration Matrix.PSL3Four
open Matrix.PSL3Four.SylowModel
open Matrix.PSL3Four.SylowModel.MatrixRealization
open scoped Matrix
namespace Configuration.PlaneFour
noncomputable section
local instance : DecidableEq F := Classical.decEq _
private abbrev Chart := Option (F ⊕ F × F)
private def chartVector : Chart → Fin 3 → F
  | none => ![0,0,1]
  | some (.inl a) => ![0,1,a]
  | some (.inr (a,b)) => ![1,a,b]
private theorem chartVector_ne_zero (x : Chart) : chartVector x ≠ 0 := by
  rcases x with _ | (a | ⟨a,b⟩)
  all_goals simp [chartVector, funext_iff, Fin.forall_fin_succ]
private def chart (x : Chart) : PG := mk F (chartVector x) (chartVector_ne_zero x)
private theorem chart_injective : Function.Injective chart := by
  intro x y he
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff _ _ _ _ _).mp he
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  rcases x with _ | (u | ⟨u,v⟩) <;> rcases y with _ | (z | ⟨z,w⟩)
  all_goals simp_all [chartVector, Units.smul_def, Units.ne_zero]
private theorem chart_surjective : Function.Surjective chart := by
  apply ((Nat.bijective_iff_injective_and_card chart).mpr ⟨chart_injective, ?_⟩).2
  rw [card_projectivePlane]
  let := Fintype.ofFinite F
  have hc : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card, card_F]
  simp [Chart, Nat.card_eq_fintype_card, hc]
private def label : Fin 21 → Chart :=
  ![none, some (.inl 0), some (.inl 1), some (.inl omega), some (.inl (omega+1)),
    some (.inr (0,0)), some (.inr (0,1)), some (.inr (0,omega)), some (.inr (0,omega+1)),
    some (.inr (1,0)), some (.inr (1,1)), some (.inr (1,omega)), some (.inr (1,omega+1)),
    some (.inr (omega,0)), some (.inr (omega,1)), some (.inr (omega,omega)), some (.inr (omega,omega+1)),
    some (.inr (omega+1,0)), some (.inr (omega+1,1)), some (.inr (omega+1,omega)), some (.inr (omega+1,omega+1))]
private def representative (i : Fin 21) : PG := chart (label i)
private def representativeVector (i : Fin 21) : Fin 3 → F := chartVector (label i)
private theorem representative_surjective : Function.Surjective representative := by
  intro p
  obtain ⟨x,rfl⟩ := chart_surjective p
  rcases x with _ | (a | ⟨a,b⟩)
  · exact ⟨0,rfl⟩
  · rcases field_cases a with rfl | rfl | rfl | rfl
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
    · exact ⟨4,rfl⟩
  · rcases field_cases a with rfl | rfl | rfl | rfl <;>
      rcases field_cases b with rfl | rfl | rfl | rfl
    all_goals first
      | exact ⟨5,rfl⟩ | exact ⟨6,rfl⟩ | exact ⟨7,rfl⟩ | exact ⟨8,rfl⟩
      | exact ⟨9,rfl⟩ | exact ⟨10,rfl⟩ | exact ⟨11,rfl⟩ | exact ⟨12,rfl⟩
      | exact ⟨13,rfl⟩ | exact ⟨14,rfl⟩ | exact ⟨15,rfl⟩ | exact ⟨16,rfl⟩
      | exact ⟨17,rfl⟩ | exact ⟨18,rfl⟩ | exact ⟨19,rfl⟩ | exact ⟨20,rfl⟩
private theorem representative_incidence (i j : Fin 21) :
    representative i ∈ representative j ↔ representativeVector i ⬝ᵥ representativeVector j = 0 :=
  Projectivization.orthogonal_mk _ _

private theorem fixed_line (c : FullCollineation) (i j k : Fin 21)
    (hij : representative i ≠ representative j)
    (hik : representativeVector i ⬝ᵥ representativeVector k = 0)
    (hjk : representativeVector j ⬝ᵥ representativeVector k = 0)
    (hi : Collineation.pointHom PG PG c (representative i) = representative i)
    (hj : Collineation.pointHom PG PG c (representative j) = representative j) :
    Collineation.lineHom PG PG c (representative k) = representative k := by
  have hik' := (Collineation.mem_iff c (representative i) (representative k)).mpr
    ((representative_incidence i k).mpr hik)
  have hjk' := (Collineation.mem_iff c (representative j) (representative k)).mpr
    ((representative_incidence j k).mpr hjk)
  rw [hi] at hik'
  rw [hj] at hjk'
  exact (Nondegenerate.eq_or_eq hik' hjk' ((representative_incidence i k).mpr hik)
    ((representative_incidence j k).mpr hjk)).resolve_left hij

private theorem fixed_point (c : FullCollineation) (j k i : Fin 21)
    (hjk : representative j ≠ representative k)
    (hij : representativeVector i ⬝ᵥ representativeVector j = 0)
    (hik : representativeVector i ⬝ᵥ representativeVector k = 0)
    (hj : Collineation.lineHom PG PG c (representative j) = representative j)
    (hk : Collineation.lineHom PG PG c (representative k) = representative k) :
    Collineation.pointHom PG PG c (representative i) = representative i := by
  have hij' := (Collineation.mem_iff c (representative i) (representative j)).mpr
    ((representative_incidence i j).mpr hij)
  have hik' := (Collineation.mem_iff c (representative i) (representative k)).mpr
    ((representative_incidence i k).mpr hik)
  rw [hj] at hij'
  rw [hk] at hik'
  exact (Nondegenerate.eq_or_eq hij' ((representative_incidence i j).mpr hij)
    hik' ((representative_incidence i k).mpr hik)).resolve_right hjk

private theorem omega_sq : omega ^ 2 = omega + 1 := omega_frobenius
private theorem omega_add_one_sq : (omega + 1) ^ 2 = omega := by
  change fieldFrobenius (omega + 1) = omega
  rw [map_add, map_one, omega_frobenius]
  simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
local macro "coord" : tactic => `(tactic| (
  simp [representativeVector, chartVector, label, dotProduct, Fin.sum_univ_three,
    mul_add, add_mul, ← pow_two, omega_sq, omega_add_one_sq, add_assoc, add_comm, add_left_comm,
    CharTwo.add_self_eq_zero]))
local macro "separate" : tactic => `(tactic| (
  apply chart_injective.ne
  simp [label, omega_ne_zero, omega_ne_one, Ne.symm omega_ne_zero, Ne.symm omega_ne_one]))


private theorem frame_and_extra_fixed_eq_one (c : FullCollineation)
    (h : ∀ i : Fin 4, Collineation.pointHom PG PG c (frame i) = frame i)
    (p13 : Collineation.pointHom PG PG c (representative 13) = representative 13) : c = 1 := by
  have p5 := h 0
  have p1 := h 1
  have p0 := h 2
  have p10 := h 3
  have l5 := fixed_line c 0 1 5 (by separate) (by coord) (by coord) p0 p1
  have l1 := fixed_line c 0 5 1 (by separate) (by coord) (by coord) p0 p5
  have l9 := fixed_line c 0 10 9 (by separate) (by coord) (by coord) p0 p10
  have l17 := fixed_line c 0 13 17 (by separate) (by coord) (by coord) p0 p13
  have l0 := fixed_line c 1 5 0 (by separate) (by coord) (by coord) p1 p5
  have l6 := fixed_line c 1 10 6 (by separate) (by coord) (by coord) p1 p10
  have l2 := fixed_line c 5 10 2 (by separate) (by coord) (by coord) p5 p10
  have l19 := fixed_line c 10 13 19 (by separate) (by coord) (by coord) p10 p13
  have p9 := fixed_point c 0 9 9 (by separate) (by coord) (by coord) l0 l9
  have p6 := fixed_point c 1 6 6 (by separate) (by coord) (by coord) l1 l6
  have p8 := fixed_point c 1 19 8 (by separate) (by coord) (by coord) l1 l19
  have p2 := fixed_point c 2 5 2 (by separate) (by coord) (by coord) l2 l5
  have p15 := fixed_point c 2 17 15 (by separate) (by coord) (by coord) l2 l17
  have p3 := fixed_point c 5 19 3 (by separate) (by coord) (by coord) l5 l19
  have p14 := fixed_point c 6 17 14 (by separate) (by coord) (by coord) l6 l17
  have l7 := fixed_line c 1 8 7 (by separate) (by coord) (by coord) p1 p8
  have l8 := fixed_line c 1 15 8 (by separate) (by coord) (by coord) p1 p15
  have l4 := fixed_line c 3 5 4 (by separate) (by coord) (by coord) p3 p5
  have l14 := fixed_line c 3 6 14 (by separate) (by coord) (by coord) p3 p6
  have l3 := fixed_line c 5 14 3 (by separate) (by coord) (by coord) p5 p14
  have p17 := fixed_point c 0 14 17 (by separate) (by coord) (by coord) l0 l14
  have p7 := fixed_point c 1 8 7 (by separate) (by coord) (by coord) l1 l8
  have p20 := fixed_point c 2 7 20 (by separate) (by coord) (by coord) l2 l7
  have p4 := fixed_point c 3 5 4 (by separate) (by coord) (by coord) l3 l5
  have p12 := fixed_point c 3 7 12 (by separate) (by coord) (by coord) l3 l7
  have p19 := fixed_point c 3 8 19 (by separate) (by coord) (by coord) l3 l8
  have p18 := fixed_point c 4 6 18 (by separate) (by coord) (by coord) l4 l6
  have p16 := fixed_point c 4 7 16 (by separate) (by coord) (by coord) l4 l7
  have p11 := fixed_point c 4 8 11 (by separate) (by coord) (by coord) l4 l8
  apply Collineation.ext_points
  intro p
  obtain ⟨i,rfl⟩ := representative_surjective p
  change Collineation.pointHom PG PG c (representative i) = representative i
  fin_cases i <;> assumption

private theorem omega_add_one_ne_zero : omega + 1 ≠ 0 := by
  intro h
  apply omega_ne_one
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using
    congrArg (· + (1 : F)) h

private theorem remaining_point_cases (p : PG) (hp : p ∈ representative 0)
    (h5 : p ≠ representative 5) (h1 : p ≠ representative 1)
    (h9 : p ≠ representative 9) : p = representative 13 ∨ p = representative 17 := by
  obtain ⟨i,rfl⟩ := representative_surjective p
  rw [representative_incidence] at hp
  fin_cases i
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact (h5 rfl).elim
    | exact (h1 rfl).elim
    | exact (h9 rfl).elim
    | simp [representativeVector, chartVector, label, dotProduct, Fin.sum_univ_three,
        omega_ne_zero, omega_add_one_ne_zero] at hp

private theorem frame_fixed_extra_cases (c : FullCollineation)
    (h : ∀ i : Fin 4, Collineation.pointHom PG PG c (frame i) = frame i) :
    Collineation.pointHom PG PG c (representative 13) = representative 13 ∨
      Collineation.pointHom PG PG c (representative 13) = representative 17 := by
  have p5 := h 0
  have p1 := h 1
  have p0 := h 2
  have p10 := h 3
  have l0 := fixed_line c 1 5 0 (by separate) (by coord) (by coord) p1 p5
  have l9 := fixed_line c 0 10 9 (by separate) (by coord) (by coord) p0 p10
  have p9 := fixed_point c 0 9 9 (by separate) (by coord) (by coord) l0 l9
  have hn (k : Fin 21)
      (hk : Collineation.pointHom PG PG c (representative k) = representative k)
      (hn : representative 13 ≠ representative k) :
      Collineation.pointHom PG PG c (representative 13) ≠ representative k := by
    intro he
    exact hn ((Collineation.pointHom PG PG c).injective (he.trans hk.symm))
  apply remaining_point_cases
  · have hi := (Collineation.mem_iff c (representative 13) (representative 0)).mpr
      ((representative_incidence 13 0).mpr (by coord))
    rwa [l0] at hi
  · exact hn 5 p5 (by separate)
  · exact hn 1 p1 (by separate)
  · exact hn 9 p9 (by separate)

private theorem ext_frame_extra {c d : FullCollineation}
    (h : ∀ i : Fin 4, Collineation.pointHom PG PG c (frame i) =
      Collineation.pointHom PG PG d (frame i))
    (he : Collineation.pointHom PG PG c (representative 13) =
      Collineation.pointHom PG PG d (representative 13)) : c = d := by
  apply inv_mul_eq_one.mp
  apply frame_and_extra_fixed_eq_one
  · intro i
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [← h i]
    exact (Collineation.pointHom PG PG c).symm_apply_apply _
  · simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    rw [← he]
    exact (Collineation.pointHom PG PG c).symm_apply_apply _

public abbrev FrameFixer := {c : FullCollineation //
  ∀ i : Fin 4, Collineation.pointHom PG PG c (frame i) = frame i}

public theorem card_frameFixer_le_two : Nat.card FrameFixer ≤ 2 := by
  classical
  let f : FrameFixer → Bool := fun c => decide
    (Collineation.pointHom PG PG c.val (representative 13) = representative 13)
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    apply ext_frame_extra (fun i => (c.property i).trans (d.property i).symm)
    have hc := frame_fixed_extra_cases c.val c.property
    have hd := frame_fixed_extra_cases d.val d.property
    by_cases hp : Collineation.pointHom PG PG c.val (representative 13) = representative 13
    · have hq : Collineation.pointHom PG PG d.val (representative 13) = representative 13 := by
        simpa [f, hp] using he.symm
      exact hp.trans hq.symm
    · have hq : Collineation.pointHom PG PG d.val (representative 13) ≠ representative 13 := by
        simpa [f, hp] using he.symm
      exact (hc.resolve_left hp).trans (hd.resolve_left hq).symm
  simpa using Nat.card_le_card_of_injective f hf
end
end Configuration.PlaneFour
