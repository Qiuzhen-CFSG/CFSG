module
public import Theory.Combinatorics.ProjectivePlaneThreeFrame
public import Mathlib.Tactic.FinCases

/-!
# A quadrangle and its diagonal points

In a plane of order three there are thirteen points. The three sides of a
triangle cover at most twelve, so there is a fourth vertex outside them.
The six joining lines give the quadrangle, and the intersections of opposite
sides give its seven-point frame. Line uniqueness excludes every unwanted
vertex or diagonal incidence.

This supplies the geometric input to the elementary uniqueness proof for the
plane of order three (Wong, Theorem 6(b), printed p.111,
10.1017/S1446788700022771).
-/

public section

namespace Configuration.Three

/-- Four vertices in general position, with their six joining lines labeled
AB, AC, AD, BC, BD, CD. -/
structure Quadrangle (P L : Type*) [Membership P L] where
  point : Fin 4 → P
  side : Fin 6 → L
  incident : ∀ i j, point i ∈ side j ↔
    i.castLE (by decide) ∈ line (j.castLE (by decide))

section Existence

variable {P L : Type*} [Membership P L] [Finite P] [Finite L]
  [ProjectivePlane P L] (h : ∀ l : L, pointCount P l = 4)

include h in
theorem exists_quadrangle : Nonempty (Quadrangle P L) := by
  classical
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨C, A, B, _, ab, aux, hCab, _, _, hAab, hAaux, _, hBab, hBaux⟩ :=
    ProjectivePlane.exists_config (P := P) (L := L)
  have hAB : A ≠ B := fun he => hBaux (he ▸ hAaux)
  have hAC : A ≠ C := fun he => hCab (he ▸ hAab)
  have hBC : B ≠ C := fun he => hCab (he ▸ hBab)
  let ac : L := HasLines.mkLine hAC
  let bc : L := HasLines.mkLine hBC
  obtain ⟨hAac, hCac⟩ := HasLines.mkLine_ax (L := L) hAC
  obtain ⟨hBbc, hCbc⟩ := HasLines.mkLine_ax (L := L) hBC
  change A ∈ ac at hAac
  change C ∈ ac at hCac
  change B ∈ bc at hBbc
  change C ∈ bc at hCbc
  let t : L → Finset P := fun l => Finset.univ.filter (fun p => p ∈ l)
  have ht (l : L) : (t l).card = 4 := by
    simpa only [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype] using h l
  have hs : ((t ab ∪ t ac) ∪ t bc).card ≤ 12 := by
    have h₁ := Finset.card_union_le (t ab) (t ac)
    have h₂ := Finset.card_union_le (t ab ∪ t ac) (t bc)
    rw [ht, ht] at h₁
    rw [ht] at h₂
    omega
  have hP : Fintype.card P = 13 := by simpa using card_points h
  obtain ⟨D, _, hD⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := t ab ∪ t ac ∪ t bc) (t := Finset.univ) (by simpa [hP] using (lt_of_le_of_lt hs (by decide : 12 < 13)))
  simp only [Finset.mem_union, t, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hD
  obtain ⟨⟨hDab, hDac⟩, hDbc⟩ := hD
  have hAD : A ≠ D := fun he => hDab (he ▸ hAab)
  have hBD : B ≠ D := fun he => hDab (he ▸ hBab)
  have hCD : C ≠ D := fun he => hDac (he ▸ hCac)
  let ad : L := HasLines.mkLine hAD
  let bd : L := HasLines.mkLine hBD
  let cd : L := HasLines.mkLine hCD
  obtain ⟨hAad, hDad⟩ := HasLines.mkLine_ax (L := L) hAD
  obtain ⟨hBbd, hDbd⟩ := HasLines.mkLine_ax (L := L) hBD
  obtain ⟨hCcd, hDcd⟩ := HasLines.mkLine_ax (L := L) hCD
  change A ∈ ad at hAad
  change D ∈ ad at hDad
  change B ∈ bd at hBbd
  change D ∈ bd at hDbd
  change C ∈ cd at hCcd
  change D ∈ cd at hDcd
  have hunique : ∀ (p r : P) (l m : L), p ∈ l → r ∈ l → p ∈ m → r ∈ m →
      p = r ∨ l = m := fun _ _ _ _ => Nondegenerate.eq_or_eq
  refine ⟨⟨![A, B, C, D], ![ab, ac, ad, bc, bd, cd], ?_⟩⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [line] <;>
    grind only

end Existence

private theorem quadrangle_sides_distinguished : ∀ j k : Fin 6,
    (∀ i : Fin 4, i.castLE (by decide) ∈ line (j.castLE (by decide)) ↔
      i.castLE (by decide) ∈ line (k.castLE (by decide))) → j = k := by
  decide +kernel

private def firstSide : Fin 3 → Fin 6 := ![0, 1, 2]
private def secondSide : Fin 3 → Fin 6 := ![5, 4, 3]

private theorem opposite_ne : ∀ d, firstSide d ≠ secondSide d := by decide +kernel

private theorem diagonal_incidence : ∀ (d : Fin 3) (j : Fin 6),
    (⟨d.val + 4, by omega⟩ : Fin 13) ∈ line (j.castLE (by decide)) ↔
      j = firstSide d ∨ j = secondSide d := by
  decide +kernel

private theorem opposite_obstruction : ∀ (d : Fin 3) (j : Fin 6),
    j ≠ firstSide d → j ≠ secondSide d → ∃ i : Fin 4,
      i.castLE (by decide) ∈ line ((firstSide d).castLE (by decide)) ∧
      i.castLE (by decide) ∈ line (j.castLE (by decide)) ∧
      i.castLE (by decide) ∉ line ((secondSide d).castLE (by decide)) := by
  decide +kernel

namespace Quadrangle

variable {P L : Type*} [Membership P L] (q : Quadrangle P L)

theorem side_injective : Function.Injective q.side := by
  intro j k hjk
  apply quadrangle_sides_distinguished j k
  intro i
  rw [← q.incident, ← q.incident, hjk]

variable [HasPoints P L]

omit [HasPoints P L] in
private theorem opposite_distinct (d : Fin 3) : q.side (firstSide d) ≠ q.side (secondSide d) :=
  fun he => opposite_ne d (q.side_injective he)

/-- Intersection of a pair of opposite sides. -/
noncomputable def diagonal (d : Fin 3) : P := HasPoints.mkPoint (opposite_distinct q d)

theorem diagonal_mem_iff (d : Fin 3) (j : Fin 6) :
    q.diagonal d ∈ q.side j ↔
      (⟨d.val + 4, by omega⟩ : Fin 13) ∈ line (j.castLE (by decide)) := by
  obtain ⟨hu, hv⟩ := HasPoints.mkPoint_ax (P := P) (opposite_distinct q d)
  change q.diagonal d ∈ q.side (firstSide d) at hu
  change q.diagonal d ∈ q.side (secondSide d) at hv
  rw [diagonal_incidence]
  constructor
  · intro hj
    by_contra hn
    obtain ⟨hju, hjv⟩ := not_or.mp hn
    obtain ⟨i, hiu, hij, hiv⟩ := opposite_obstruction d j hju hjv
    rw [← q.incident] at hiu hij hiv
    have he : q.diagonal d = q.point i :=
      (Nondegenerate.eq_or_eq hu hiu hj hij).resolve_right
        (fun he => hju (q.side_injective he).symm)
    exact hiv (he ▸ hv)
  · rintro (rfl | rfl)
    · exact hu
    · exact hv

/-- Adjoin the three diagonal points to a quadrangle. -/
noncomputable def toFrame : Frame P L where
  point i := if hi : i.val < 4 then q.point ⟨i.val, hi⟩
    else q.diagonal ⟨i.val - 4, by omega⟩
  side := q.side
  incident i j := by
    split_ifs with hi
    · exact q.incident ⟨i.val, hi⟩ j
    · rw [q.diagonal_mem_iff]
      have he : (⟨(i.val - 4) + 4, by omega⟩ : Fin 13) = i.castLE (by decide) := by
        apply Fin.ext
        dsimp
        omega
      rw [he]

end Quadrangle

variable {P L : Type*} [Membership P L] [Finite P] [Finite L]
  [ProjectivePlane P L]

/-- Every projective plane with four points on each line has a quadrangle frame. -/
theorem exists_frame (h : ∀ l : L, pointCount P l = 4) : Nonempty (Frame P L) := by
  obtain ⟨q⟩ := exists_quadrangle h
  exact ⟨q.toFrame⟩

/-- Every projective plane of order three admits the thirteen-point side labeling. -/
theorem exists_sideChart (h : ∀ l : L, pointCount P l = 4) : Nonempty (SideChart P L) := by
  obtain ⟨f⟩ := exists_frame h
  exact ⟨f.toSideChart h⟩

end Configuration.Three
