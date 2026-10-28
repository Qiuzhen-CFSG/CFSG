module
public import Mathlib.Combinatorics.Configuration
public import Mathlib.Data.Fintype.EquivFin

/-!
# An affine grid in a projective plane of order four

Choose an ideal line and an affine point. The four affine points on a diagonal
label the vertical and horizontal pencils through two other ideal points.
Their intersections give sixteen distinct affine points. The five ideal points
complete a bijection, and line uniqueness proves the grid incidence formulas.

This is the geometric input for elementary order-four plane recognition in the
PSL₃(4) branch of Aschbacher–Smith F.4.8(2), printed p.278, used in F.4.26,
printed p.288. It uses only the projective-plane axioms and five points per line.
-/
@[expose] public section
noncomputable section
namespace Configuration.Four
variable {P L : Type*} [Membership P L] [Finite P] [Finite L] [ProjectivePlane P L]
variable (h : ∀ l : L, pointCount P l = 5)
include h

theorem order_eq_four : ProjectivePlane.order P L = 4 := by
  obtain ⟨_, _, _, l, _⟩ := ProjectivePlane.exists_config (P := P) (L := L)
  have := h l
  rw [ProjectivePlane.pointCount_eq] at this
  omega

theorem card_points : Nat.card P = 21 := by
  let : Fintype P := Fintype.ofFinite P
  rw [Nat.card_eq_fintype_card, ProjectivePlane.card_points P L, order_eq_four h]
  rfl

theorem card_lines : Nat.card L = 21 := by
  let : Fintype L := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card, ProjectivePlane.card_lines P L, order_eq_four h]
  rfl

omit h [Finite P] [Finite L] [ProjectivePlane P L] in
structure Grid where
  point : ((Fin 4 × Fin 4) ⊕ Fin 5) ≃ P
  infinity : L
  vertical : Fin 4 → L
  horizontal : Fin 4 → L
  diagonal : L
  infinity_affine : ∀ i j, point (.inl (i,j)) ∉ infinity
  infinity_ideal : ∀ k, point (.inr k) ∈ infinity
  vertical_affine : ∀ i j k, point (.inl (i,j)) ∈ vertical k ↔ i = k
  vertical_ideal : ∀ i k, point (.inr i) ∈ vertical k ↔ i = 0
  horizontal_affine : ∀ i j k, point (.inl (i,j)) ∈ horizontal k ↔ j = k
  horizontal_ideal : ∀ i k, point (.inr i) ∈ horizontal k ↔ i = 1
  diagonal_affine : ∀ i j, point (.inl (i,j)) ∈ diagonal ↔ i = j
  diagonal_ideal : ∀ i, point (.inr i) ∈ diagonal ↔ i = 2

omit h [Finite P] [Finite L] in
private theorem line_eq {a b : P} {l m : L} (hab : a ≠ b)
    (hal : a ∈ l) (hbl : b ∈ l) (ham : a ∈ m) (hbm : b ∈ m) : l = m :=
  (Nondegenerate.eq_or_eq hal hbl ham hbm).resolve_left hab

omit h [Finite P] [Finite L] in
private theorem point_eq {a b : P} {l m : L} (hlm : l ≠ m)
    (hal : a ∈ l) (hbl : b ∈ l) (ham : a ∈ m) (hbm : b ∈ m) : a = b :=
  (Nondegenerate.eq_or_eq hal hbl ham hbm).resolve_right hlm

/-- Choose an affine origin outside a prescribed line. -/
private theorem exists_off_line (l : L) : ∃ p : P, p ∉ l := by
  classical
  by_contra hn
  have ha : ∀ p : P, p ∈ l := by simpa using hn
  have he : Nat.card {p : P // p ∈ l} = Nat.card P :=
    Nat.card_congr (Equiv.subtypeUnivEquiv ha)
  have hc := h l
  change Nat.card {p : P // p ∈ l} = 5 at hc
  rw [he, card_points h] at hc
  omega

/-- Every order-four projective plane admits an affine grid whose chosen
transversal is the diagonal. -/
theorem exists_grid : Nonempty (Grid (P := P) (L := L)) := by
  classical
  let : Fintype P := Fintype.ofFinite P
  obtain ⟨_, _, _, I, _⟩ := ProjectivePlane.exists_config (P := P) (L := L)
  let E : Fin 5 ≃ {p : P // p ∈ I} :=
    (Fintype.equivFinOfCardEq (by simpa [pointCount, Nat.card_eq_fintype_card] using h I)).symm
  let u : Fin 5 → P := fun i => (E i).val
  have hu : Function.Injective u := fun i j hij => E.injective (Subtype.ext hij)
  have huI (i) : u i ∈ I := (E i).property
  obtain ⟨o, ho⟩ := exists_off_line h I
  have hDo : u 2 ≠ o := fun he => ho (he ▸ huI 2)
  let d : L := HasLines.mkLine hDo
  obtain ⟨hDd, hod⟩ := HasLines.mkLine_ax (L := L) hDo
  change u 2 ∈ d at hDd
  change o ∈ d at hod
  have hdI : d ≠ I := fun he => ho (he ▸ hod)
  have hid (i) : u i ∈ d ↔ i = 2 := by
    constructor
    · intro hi
      exact hu (point_eq hdI hi hDd (huI i) (huI 2))
    · rintro rfl; exact hDd
  let T := {p : {p : P // p ∈ d} // p.val ≠ u 2}
  have hT : Fintype.card T = 4 := by
    have hd : Fintype.card {p : P // p ∈ d} = 5 := by
      simpa [pointCount, Nat.card_eq_fintype_card] using h d
    have ht : Fintype.card {p : {p : P // p ∈ d} // p.val = u 2} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      exact ⟨⟨⟨u 2, hDd⟩, rfl⟩, fun p => Subtype.ext (Subtype.ext p.property)⟩
    change Fintype.card {p : {p : P // p ∈ d} // ¬ p.val = u 2} = 4
    rw [Fintype.card_subtype_compl, hd, ht]
  let X : Fin 4 ≃ T := (Fintype.equivFinOfCardEq hT).symm
  let x : Fin 4 → P := fun i => (X i).val.val
  have hx : Function.Injective x := fun i j hij =>
    X.injective (Subtype.ext (Subtype.ext hij))
  have hxd (i) : x i ∈ d := (X i).val.property
  have hxD (i) : x i ≠ u 2 := (X i).property
  have hxI (i) : x i ∉ I := fun hi =>
    hxD i (point_eq hdI (hxd i) hDd hi (huI 2))
  have hxu (i k) : x i ≠ u k := fun he => hxI i (he ▸ huI k)
  let v : Fin 4 → L := fun i => HasLines.mkLine (hxu i 0).symm
  let w : Fin 4 → L := fun i => HasLines.mkLine (hxu i 1).symm
  have hv (i) : u 0 ∈ v i ∧ x i ∈ v i := HasLines.mkLine_ax (L := L) _
  have hw (i) : u 1 ∈ w i ∧ x i ∈ w i := HasLines.mkLine_ax (L := L) _
  have hvI (i) : v i ≠ I := fun he => hxI i (he ▸ (hv i).2)
  have hwI (i) : w i ≠ I := fun he => hxI i (he ▸ (hw i).2)
  have huv (k i) : u k ∈ v i ↔ k = 0 := by
    constructor
    · intro hk; exact hu (point_eq (hvI i) hk (hv i).1 (huI k) (huI 0))
    · rintro rfl; exact (hv i).1
  have huw (k i) : u k ∈ w i ↔ k = 1 := by
    constructor
    · intro hk; exact hu (point_eq (hwI i) hk (hw i).1 (huI k) (huI 1))
    · rintro rfl; exact (hw i).1
  have hvd (i) : v i ≠ d := by
    intro he
    have := (hid 0).mp (he ▸ (hv i).1)
    exact (by decide : (0 : Fin 5) ≠ 2) this
  have hwd (i) : w i ≠ d := by
    intro he
    have := (hid 1).mp (he ▸ (hw i).1)
    exact (by decide : (1 : Fin 5) ≠ 2) this
  have hvv : Function.Injective v := by
    intro i j he
    exact hx (point_eq (hvd i) (hv i).2 (he ▸ (hv j).2) (hxd i) (hxd j))
  have hww : Function.Injective w := by
    intro i j he
    exact hx (point_eq (hwd i) (hw i).2 (he ▸ (hw j).2) (hxd i) (hxd j))
  have hvw (i j) : v i ≠ w j := by
    intro he
    have := (huw 0 j).mp (he ▸ (hv i).1)
    exact (by decide : (0 : Fin 5) ≠ 1) this
  let a : Fin 4 × Fin 4 → P := fun ij => HasPoints.mkPoint (hvw ij.1 ij.2)
  have ha (i j) : a (i,j) ∈ v i ∧ a (i,j) ∈ w j := HasPoints.mkPoint_ax (P := P) _
  have haI (i j) : a (i,j) ∉ I := by
    intro hi
    have he := point_eq (hvI i) (ha i j).1 (hv i).1 hi (huI 0)
    have := (huw 0 j).mp (he ▸ (ha i j).2)
    exact (by decide : (0 : Fin 5) ≠ 1) this
  have hav (i j k) : a (i,j) ∈ v k ↔ i = k := by
    constructor
    · intro hk
      apply hvv
      exact line_eq (show a (i,j) ≠ u 0 from fun he => haI i j (he ▸ huI 0))
        (ha i j).1 (hv i).1 hk (hv k).1
    · rintro rfl; exact (ha i j).1
  have haw (i j k) : a (i,j) ∈ w k ↔ j = k := by
    constructor
    · intro hk
      apply hww
      exact line_eq (show a (i,j) ≠ u 1 from fun he => haI i j (he ▸ huI 1))
        (ha i j).2 (hw j).1 hk (hw k).1
    · rintro rfl; exact (ha i j).2
  have haa : Function.Injective a := by
    rintro ⟨i,j⟩ ⟨k,l⟩ he
    exact Prod.ext ((hav i j k).mp (he ▸ (ha k l).1))
      ((haw i j l).mp (he ▸ (ha k l).2))
  have had (i j) : a (i,j) ∈ d ↔ i = j := by
    constructor
    · intro hd
      have he := point_eq (hvd i) (ha i j).1 (hv i).2 hd (hxd i)
      exact hww (line_eq (hxu i 1) (he ▸ (ha i j).2) (hw j).1 (hw i).2 (hw i).1) |>.symm
    · rintro rfl
      have he := point_eq (hvw i i) (ha i i).1 (hv i).2 (ha i i).2 (hw i).2
      exact he ▸ hxd i
  let p : ((Fin 4 × Fin 4) ⊕ Fin 5) → P := Sum.elim a u
  have hp : Function.Injective p := by
    intro s t he
    rcases s with ⟨i,j⟩ | k <;> rcases t with ⟨m,n⟩ | l
    · exact congrArg Sum.inl (haa he)
    · change a (i,j) = u l at he
      exact (haI i j (he ▸ huI l)).elim
    · change u k = a (m,n) at he
      exact (haI m n (he.symm ▸ huI k)).elim
    · exact congrArg Sum.inr (hu he)
  let ep : ((Fin 4 × Fin 4) ⊕ Fin 5) ≃ P := Equiv.ofBijective p
    ((Nat.bijective_iff_injective_and_card p).mpr ⟨hp, by
      calc
        Nat.card ((Fin 4 × Fin 4) ⊕ Fin 5) = 21 := by simp
        _ = Nat.card P := (card_points h).symm⟩)
  exact ⟨⟨ep, I, v, w, d, haI, huI, hav, huv, haw, huw, had, hid⟩⟩
end Configuration.Four
