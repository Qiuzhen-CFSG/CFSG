module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Convert

/-!
# Type-preserving automorphisms of even cycles

The automorphisms of `cycleGraph (2*m)` that preserve the parity of vertex
values form `DihedralGroup m`, of order `2*m`, for every `m>1`, including
`m=2`. A rotation by `a : ZMod m` sends `x` to `x + double a`; the reflection
`sr a` sends `x` to `-x - double a`. One-step rotations of the uncolored
cycle are excluded by the parity requirement.

The structural proof determines an automorphism from its values at zero and
one: at each subsequent vertex there is only one neighbor other than the
previous vertex. Parity determines the even image of zero, and the image of
one selects a rotation or a reflection. No length-specific computation is
used. Any proper Boolean coloring agrees with parity up to a global swap.
Conjugation along `Embedding.isoInduceRange` therefore identifies the full
color-preserving automorphism group of any genuinely embedded cycle.

This supplies the automorphism-group step in Aschbacher–Smith F.3.6, printed
p.272, combined manuscript (1 March 2004), `refs/quasithin.pdf`. The faithful
quotient action is a separate input to `surjective_of_injective_induced`;
its construction and the other clauses of F.3.6 belong to the source assembly.
The literal geometric application is in `CycleAutomorphismsEdge`.
-/

@[expose] public section

namespace GroupAction.DihedralPolygon.CycleAutomorphisms
open SimpleGraph

variable {V : Type*}

/-- Vertex permutations preserving adjacency in both directions. -/
def graphAut (Γ : SimpleGraph V) : Subgroup (Equiv.Perm V) where
  carrier := {f | ∀ x y, Γ.Adj (f x) (f y) ↔ Γ.Adj x y}
  one_mem' := by simp
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    have h' := hf (f⁻¹ x) (f⁻¹ y)
    convert h'.symm using 1; simp

/-- The permutation subgroup is the actual graph-isomorphism automorphism group. -/
def graphAutEquivIso (Γ : SimpleGraph V) : graphAut Γ ≃ (Γ ≃g Γ) where
  toFun f := { toEquiv := f.1, map_rel_iff' := fun {x y} => f.property x y }
  invFun f := ⟨f.toEquiv, fun _ _ => f.map_rel_iff⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem graphAutEquivIso_mul (Γ : SimpleGraph V) (f g : graphAut Γ) :
    graphAutEquivIso Γ (f * g) = (graphAutEquivIso Γ g).trans (graphAutEquivIso Γ f) := by
  apply RelIso.ext
  intro x
  rfl

/-- The subgroup of graph automorphisms preserving every vertex color. -/
def colorPreserving (Γ : SimpleGraph V) (color : V → Bool) : Subgroup (graphAut Γ) where
  carrier := {f | ∀ v, color (f.1 v) = color v}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro f g hf hg v
    exact (hf (g.1 v)).trans (hg v)
  inv_mem' := by
    intro f hf v
    have h := hf (f.1.symm v)
    simpa using h.symm

/-- The Boolean vertex type: `true` exactly on odd vertex values. -/
def parity {n : ℕ} (v : Fin n) : Bool := decide (v.val % 2 = 1)

/-- The type-preserving subgroup of the automorphism group of the even cycle. -/
def parityPreserving (m : ℕ) : Subgroup (graphAut (cycleGraph (2 * m))) :=
  colorPreserving _ parity

variable {n : ℕ} [NeZero n]

private theorem adj_iff (hn : 2 ≤ n) (u v : Fin n) :
    (cycleGraph n).Adj u v ↔ u = v + 1 ∨ v = u + 1 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      rw [cycleGraph_adj]
      simp only [sub_eq_iff_eq_add]
      simp [add_comm]

private theorem fin_succ_mk {k : ℕ} (hk : k + 1 < n) :
    (⟨k + 1, hk⟩ : Fin n) = (⟨k, by omega⟩ : Fin n) + (1 : Fin n) := by
  have hn1 : 1 < n := by omega
  have h1 : ((1 : Fin n).val) = 1 := Nat.mod_eq_of_lt hn1
  apply Fin.ext
  simp only [Fin.val_add_eq_ite]
  split_ifs with h
  · exfalso
    omega
  · omega

private theorem neighbors (hn : 2 ≤ n) {x y z w : Fin n}
    (hy : (cycleGraph n).Adj x y) (hz : (cycleGraph n).Adj x z)
    (hw : (cycleGraph n).Adj x w) (hzy : z ≠ y) (hwy : w ≠ y) : z = w := by
  rw [adj_iff hn] at hy hz hw
  rcases hy with hy | hy <;> rcases hz with hz | hz <;> rcases hw with hw | hw
  all_goals grind

/-- A cycle automorphism is determined by the images of two consecutive vertices. -/
theorem ext_zero_one (hn : 2 < n) (f g : graphAut (cycleGraph n))
    (h0 : f.1 0 = g.1 0) (h1 : f.1 1 = g.1 1) : f = g := by
  have h : ∀ k : ℕ, ∀ hk : k < n,
      f.1 (⟨k, hk⟩ : Fin n) = g.1 (⟨k, hk⟩ : Fin n) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        intro hk
        simpa using h0
    | one =>
        intro hk
        have hval : ((1 : Fin n).val) = 1 := Nat.mod_eq_of_lt (by omega)
        have he : (⟨1, hk⟩ : Fin n) = 1 := by apply Fin.ext; exact hval.symm
        simpa [he] using h1
    | more k ih ih' =>
        intro hk
        have hk0 : k < n := by omega
        have hk1 : k + 1 < n := by omega
        let vk : Fin n := ⟨k, hk0⟩
        let vk1 : Fin n := ⟨k + 1, hk1⟩
        let vk2 : Fin n := ⟨k + 2, hk⟩
        have ha : (cycleGraph n).Adj vk1 vk := by
          rw [adj_iff (by omega)]
          exact Or.inl (by simpa [vk, vk1] using fin_succ_mk (n := n) (k := k) hk1)
        have hb : (cycleGraph n).Adj vk1 vk2 := by
          rw [adj_iff (by omega)]
          exact Or.inr (by simpa [vk1, vk2] using
            (fin_succ_mk (n := n) (k := k + 1) (by omega)))
        have hne : vk2 ≠ vk := by
          intro hh
          have hh' := congrArg Fin.val hh
          simp [vk, vk2] at hh'
        refine neighbors (x := f.1 vk1) (y := f.1 vk) (z := f.1 vk2) (w := g.1 vk2)
          (by omega) ((f.property (vk1) (vk)).mpr ha)
          ((f.property (vk1) (vk2)).mpr hb) ?_ ?_ ?_
        · rw [ih' hk1]
          exact (g.property (vk1) (vk2)).mpr hb
        · exact fun hh => hne (f.1.injective hh)
        · rw [ih hk0]
          exact fun hh => hne (g.1.injective hh)
  apply Subtype.ext
  apply Equiv.ext
  intro v
  exact h v.val v.isLt

/-- Translation by a vertex of the cycle. -/
def rotation (hn : 2 ≤ n) (a : Fin n) : graphAut (cycleGraph n) :=
  ⟨Equiv.addRight a, by
    intro x y
    simp only [adj_iff hn]
    change ((x + a) = (y + a) + 1 ∨ (y + a) = (x + a) + 1) ↔ _
    constructor <;> intro h
    · rcases h with h | h
      · left; exact add_right_cancel (b := a) (by simpa [add_assoc, add_comm a 1] using h)
      · right; exact add_right_cancel (b := a) (by simpa [add_assoc, add_comm a 1] using h)
    · rcases h with h | h
      · left; rw [h]; simp [add_assoc, add_comm]
      · right; rw [h]; simp [add_assoc, add_comm]⟩

private theorem refl_step (x y a : Fin n) :
    (-x - a = (-y - a) + 1) ↔ y = x + 1 := by
  constructor
  · intro h
    have hy : -y - a = (-x - a) - 1 := by
      calc
        -y - a = ((-y - a) + 1) - 1 := by abel
        _ = (-x - a) - 1 := by rw [← h]
    calc
      y = -((-y - a) + a) := by abel
      _ = -(((-x - a) - 1) + a) := by rw [hy]
      _ = x + 1 := by abel
  · intro h
    have hx : x = y - 1 := by
      calc
        x = (x + 1) - 1 := by abel
        _ = y - 1 := by rw [h]
    calc
      -x - a = -((y - 1) + a) := by rw [hx]; abel
      _ = (-y - a) + 1 := by abel

/-- The reflection with vertex formula `x ↦ -x - a`. -/
def reflection (hn : 2 ≤ n) (a : Fin n) : graphAut (cycleGraph n) :=
  ⟨{
    toFun := fun x => -x - a
    invFun := fun x => -x - a
    left_inv := by intro x; dsimp; abel
    right_inv := by intro x; dsimp; abel
  }, by
    intro x y
    simp only [adj_iff hn]
    change ((-x - a) = (-y - a) + 1 ∨ (-y - a) = (-x - a) + 1) ↔ _
    constructor <;> intro h
    · rcases h with h | h
      · right; exact refl_step x y a |>.mp h
      · left; exact refl_step y x a |>.mp h
    · rcases h with h | h
      · right; exact refl_step y x a |>.mpr h
      · left; exact refl_step x y a |>.mpr h⟩

variable {m : ℕ} [NeZero m] [NeZero (2 * m)]

/-- Doubling embeds the additive residues modulo `m` in the even vertices. -/
def double : ZMod m →+ Fin (2 * m) where
  toFun a := ⟨2 * a.val, by have := a.val_lt; omega⟩
  map_zero' := by ext; simp
  map_add' a b := by
    apply Fin.ext
    change 2 * (a + b).val = (2 * a.val + 2 * b.val) % (2 * m)
    rw [ZMod.val_add, ← Nat.mul_add, Nat.mul_mod_mul_left]

@[simp] theorem double_val (a : ZMod m) : (double a).val = 2 * a.val := rfl

theorem double_injective : Function.Injective (double : ZMod m → Fin (2 * m)) := by
  intro a b h
  apply ZMod.val_injective
  have := congrArg Fin.val h
  simp only [double_val] at this
  omega

private theorem parity_add_double (x : Fin (2 * m)) (a : ZMod m) :
    parity (x + double a) = parity x := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hx := x.isLt
  have ha := a.val_lt
  simp only [parity, Fin.val_add_eq_ite]
  by_cases h : 2 * m ≤ x.val + (double a).val
  · simp only [if_pos h]
    congr 1
    have hzero : 2 * m ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).2 ⟨m, by omega⟩
    have hadd : x.val + (double a).val ≡ x.val [MOD 2] := by
      simpa only [double_val, Nat.add_zero] using Nat.ModEq.add (Nat.ModEq.refl _)
        ((Nat.modEq_zero_iff_dvd).2 ⟨a.val, by omega⟩)
    have hsub := Nat.ModEq.sub h (by omega) hadd hzero
    have hrem : (x.val + (double a).val - 2 * m) % 2 = x.val % 2 := by
      change (x.val + (double a).val - 2 * m) % 2 = (x.val - 0) % 2 at hsub
      simpa only [Nat.sub_zero] using hsub
    rw [hrem]
  · simp only [if_neg h]
    congr 1
    have hadd : x.val + (double a).val ≡ x.val [MOD 2] := by
      simpa only [double_val, Nat.add_zero] using Nat.ModEq.add (Nat.ModEq.refl _)
        ((Nat.modEq_zero_iff_dvd).2 ⟨a.val, by omega⟩)
    have hrem : (x.val + (double a).val) % 2 = x.val % 2 := by
      change (x.val + (double a).val) % 2 = x.val % 2 at hadd
      exact hadd
    rw [hrem]

private theorem parity_neg (x : Fin (2 * m)) : parity (-x) = parity x := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hx := x.isLt
  simp only [parity, Fin.val_neg]
  by_cases h : x = 0
  · have hv : x.val = 0 := by simp [h]
    simp only [if_pos h]
    congr 1
    simp [hv]
  · simp only [if_neg h]
    congr 1
    have hrem : (2 * m - x.val) % 2 = x.val % 2 := by
      have hcases := Nat.mod_two_eq_zero_or_one x.val
      rcases hcases with h0 | h1
      · rw [h0]
        omega
      · rw [h1]
        omega
    rw [hrem]

/-- The standard dihedral action on the even cycle. Rotations move two steps. -/
def dihedralHom (hm : 1 < m) : DihedralGroup m →* parityPreserving m where
  toFun
    | .r a => ⟨rotation (by omega) (double a), by
        intro x
        exact parity_add_double x a⟩
    | .sr a => ⟨reflection (by omega) (double a), fun x => by
        change parity (-x - double a) = parity x
        rw [sub_eq_add_neg, ← map_neg]
        exact (parity_add_double (-x) (-a)).trans (parity_neg x)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change x + double (0 : ZMod m) = x
    simp
  map_mul' := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    cases a <;> cases b <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    all_goals simp only [rotation, reflection, Subgroup.coe_mul,
      Equiv.Perm.mul_apply, Equiv.coe_addRight, map_add, map_sub]
    all_goals try dsimp [Equiv.addRight, Units.mulRight]
    all_goals try simp only [neg_sub]
    all_goals abel


@[simp] theorem dihedralHom_r_apply (hm : 1 < m) (a : ZMod m) (x : Fin (2 * m)) :
    ((dihedralHom hm (.r a)).1).1 x = x + double a := rfl

@[simp] theorem dihedralHom_sr_apply (hm : 1 < m) (a : ZMod m) (x : Fin (2 * m)) :
    ((dihedralHom hm (.sr a)).1).1 x = -x - double a := rfl

/-- Explicit vertex values: rotations add twice the residue. -/
theorem dihedralHom_r_val (hm : 1 < m) (a : ZMod m) (x : Fin (2 * m)) :
    (((dihedralHom hm (.r a)).1).1 x).val = (x.val + 2 * a.val) % (2 * m) := by
  change (x.val + (double a).val) % (2 * m) = _
  rfl

/-- The even vertices are exactly the doubled residues. -/
theorem exists_double_of_parity_false (v : Fin (2 * m)) (hv : parity v = false) :
    ∃ a : ZMod m, double a = v := by
  have heven : v.val % 2 = 0 := by
    simp only [parity, decide_eq_false_iff_not] at hv
    omega
  have hlt : v.val / 2 < m := by have := v.isLt; omega
  refine ⟨(v.val / 2 : ℕ), ?_⟩
  apply Fin.ext
  rw [double_val, ZMod.val_natCast_of_lt hlt]
  omega

/-- No extra automorphisms occur: a type-preserving automorphism has one of
exactly the standard rotation/reflection formulas. This includes the square. -/
theorem dihedralHom_surjective (hm : 1 < m) : Function.Surjective (dihedralHom hm) := by
  intro f
  have hc : parity (f.1.1 0) = false := by
    have h := f.property 0
    exact h.trans (by rfl)
  obtain ⟨a, ha⟩ := exists_double_of_parity_false (f.1.1 0) hc
  have hadj : (cycleGraph (2 * m)).Adj (0 : Fin (2 * m)) 1 := by
    rw [adj_iff (by omega)]
    exact Or.inr (by simp)
  have h := (f.1.property 0 1).mpr hadj
  rw [adj_iff (by omega)] at h
  rcases h with h | h
  · refine ⟨.sr (-a), ?_⟩
    apply Subtype.ext
    apply ext_zero_one (by omega)
    · change -0 - double (-a) = f.1.1 0
      simpa using ha
    · change -1 - double (-a) = f.1.1 1
      rw [map_neg, sub_neg_eq_add, ha, h]
      abel
  · refine ⟨.r a, ?_⟩
    apply Subtype.ext
    apply ext_zero_one (by omega)
    · change 0 + double a = f.1.1 0
      simpa using ha
    · change 1 + double a = f.1.1 1
      rw [ha, h]
      abel

/-- The standard action is faithful, including at `m=2`. -/
theorem dihedralHom_injective (hm : 1 < m) : Function.Injective (dihedralHom hm) := by
  apply (injective_iff_map_eq_one (dihedralHom hm)).mpr
  intro g hg
  have h0 := congrArg (fun f : parityPreserving m => f.1.1 (0 : Fin (2 * m))) hg
  have h1 := congrArg (fun f : parityPreserving m => f.1.1 (1 : Fin (2 * m))) hg
  cases g with
  | r a =>
    have hd : double a = 0 := by simpa using h0
    have ha : a = 0 := double_injective (hd.trans (map_zero double).symm)
    simp [ha]
  | sr a =>
    have hd : double a = 0 := by simpa using h0
    have he : -(1 : Fin (2 * m)) = 1 := by simpa [hd] using h1
    have hval := congrArg Fin.val he
    have hone : ((1 : Fin (2 * m)).val) = 1 := by
      change 1 % (2 * m) = 1
      exact Nat.mod_eq_of_lt (by omega : (1 : ℕ) < 2 * m)
    have hne : (1 : Fin (2 * m)) ≠ 0 := by
      intro hh
      have := congrArg Fin.val hh
      simp only [hone, Fin.val_zero] at this
      omega
    simp only [Fin.val_neg, if_neg hne, hone] at hval
    omega

omit [NeZero m] [NeZero (2 * m)] in
/-- The full type-preserving automorphism group of a `2*m`-cycle is `D_(2*m)`. -/
noncomputable def dihedralEquiv (hm : 1 < m) : DihedralGroup m ≃* parityPreserving m := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero (2 * m) := ⟨by omega⟩
  exact MulEquiv.ofBijective (dihedralHom hm) ⟨dihedralHom_injective hm, dihedralHom_surjective hm⟩

omit [NeZero m] [NeZero (2 * m)] in
theorem card_parityPreserving (hm : 1 < m) : Nat.card (parityPreserving m) = 2 * m := by
  rw [← Nat.card_congr (dihedralEquiv hm).toEquiv, DihedralGroup.nat_card]


omit [NeZero m] in
/-- Every proper two-coloring of a cycle alternates in its standard coordinates. -/
theorem color_formula (hm : 1 < m) (c : Fin (2 * m) → Bool)
    (hc : ∀ {x y}, (cycleGraph (2 * m)).Adj x y → c x ≠ c y) (v : Fin (2 * m)) :
    c v = (c 0 ^^ parity v) := by
  have h : ∀ k : ℕ, ∀ hk : k < 2 * m,
      c (⟨k, hk⟩ : Fin (2 * m)) = (c 0 ^^ decide (k % 2 = 1)) := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
      intro hk
      have hk0 : k < 2 * m := by omega
      have hadj : (cycleGraph (2 * m)).Adj (⟨k + 1, hk⟩ : Fin (2 * m)) ⟨k, hk0⟩ := by
        rw [adj_iff (by omega)]
        exact Or.inl (fin_succ_mk hk)
      have hne := hc hadj
      have hn := Bool.eq_not_of_ne hne
      rw [ih hk0] at hn
      rw [hn]
      have hp : decide ((k + 1) % 2 = 1) = !decide (k % 2 = 1) := by
        by_cases h : k % 2 = 1
        · have h' : (k + 1) % 2 ≠ 1 := by omega
          simp [h, h']
        · have h' : (k + 1) % 2 = 1 := by omega
          simp [h, h']
      rw [hp]
      cases c 0 <;> cases decide (k % 2 = 1) <;> rfl
  exact h v.val v.isLt

omit [NeZero m] in
/-- Proper colorings detect exactly the same vertex types as parity. -/
theorem color_eq_iff_parity_eq (hm : 1 < m) (c : Fin (2 * m) → Bool)
    (hc : ∀ {x y}, (cycleGraph (2 * m)).Adj x y → c x ≠ c y)
    (x y : Fin (2 * m)) : c x = c y ↔ parity x = parity y := by
  rw [color_formula hm c hc x, color_formula hm c hc y, Bool.xor_right_inj]

omit [NeZero m] in
/-- Replacing the standard parity colors by any proper coloring leaves exactly
this subgroup of automorphisms. -/
theorem colorPreserving_eq_parityPreserving (hm : 1 < m) (c : Fin (2 * m) → Bool)
    (hc : ∀ {x y}, (cycleGraph (2 * m)).Adj x y → c x ≠ c y) :
    colorPreserving (cycleGraph (2 * m)) c = parityPreserving m := by
  apply Subgroup.ext
  intro f
  change (∀ v, c (f.1 v) = c v) ↔ ∀ v, parity (f.1 v) = parity v
  exact forall_congr' fun v => color_eq_iff_parity_eq hm c hc (f.1 v) v

section Transport
variable {W : Type*} {Γ : SimpleGraph V} {Δ : SimpleGraph W}

/-- Conjugating the actual vertex permutations along a graph isomorphism. -/
def conjugate (e : Γ ≃g Δ) (f : graphAut Γ) : graphAut Δ :=
  ⟨e.toEquiv.symm.trans (f.1.trans e.toEquiv), by
    intro x y
    exact e.map_rel_iff.trans ((f.property _ _).trans e.symm.map_rel_iff)⟩

@[simp] theorem conjugate_apply (e : Γ ≃g Δ) (f : graphAut Γ) (x : W) :
    (conjugate e f).1 x = e (f.1 (e.symm x)) := rfl

/-- Transport of the color-preserving subgroup by a genuine graph isomorphism. -/
noncomputable def colorPreservingCongr (e : Γ ≃g Δ) (c : W → Bool) :
    colorPreserving Γ (c ∘ e) ≃* colorPreserving Δ c where
  toFun f := ⟨conjugate e f.1, by
    intro x
    change c (e (f.1.1 (e.symm x))) = c x
    have h := f.property (e.symm x)
    simpa only [Function.comp_apply, RelIso.apply_symm_apply] using h⟩
  invFun f := ⟨conjugate e.symm f.1, by
    intro x
    change c (e (e.symm (f.1.1 (e x)))) = c (e x)
    rw [RelIso.apply_symm_apply]
    exact f.property (e x)⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e.symm (e (f.1.1 (e.symm (e x)))) = f.1.1 x
    simp
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e (e.symm (f.1.1 (e (e.symm x)))) = f.1.1 x
    simp
  map_mul' f g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e (f.1.1 (g.1.1 (e.symm x))) =
      e (f.1.1 (e.symm (e (g.1.1 (e.symm x)))))
    rw [RelIso.symm_apply_apply]

@[simp] theorem colorPreservingCongr_apply (e : Γ ≃g Δ) (c : W → Bool)
    (f : colorPreserving Γ (c ∘ e)) (x : W) :
    ((colorPreservingCongr e c f).1).1 x = e (f.1.1 (e.symm x)) := rfl

omit [NeZero m] [NeZero (2 * m)] in
/-- The color-preserving automorphisms of the actual induced image of an embedded
cycle. The comparison uses `e.isoInduceRange`, not a separately postulated model. -/
noncomputable def inducedDihedralEquiv (hm : 1 < m)
    (e : cycleGraph (2 * m) ↪g Γ) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y) :
    DihedralGroup m ≃* colorPreserving (Γ.induce (Set.range e)) (fun x => color x.1) := by
  letI : NeZero m := ⟨by omega⟩
  letI : NeZero (2 * m) := ⟨by omega⟩
  let iso := e.isoInduceRange
  let c : Set.range e → Bool := fun x => color x.1
  have hcol : ∀ {x y}, (cycleGraph (2 * m)).Adj x y →
      (c ∘ iso) x ≠ (c ∘ iso) y := by
    intro x y h
    exact hc (e.map_rel_iff.mpr h)
  exact (dihedralEquiv hm).trans
    ((MulEquiv.subgroupCongr (colorPreserving_eq_parityPreserving hm (c ∘ iso) hcol).symm).trans
      (colorPreservingCongr iso c))

/-- The transported action is conjugation along the embedding's induced-range
isomorphism, with the standard concrete cycle action on its domain. -/
theorem inducedDihedralEquiv_apply (hm : 1 < m)
    (e : cycleGraph (2 * m) ↪g Γ) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (d : DihedralGroup m) (v : Set.range e) :
    ((inducedDihedralEquiv hm e color hc d).1).1 v =
      e.isoInduceRange (((dihedralHom hm d).1).1 (e.isoInduceRange.symm v)) := rfl

omit [NeZero m] [NeZero (2 * m)] in
/-- The induced image has precisely `2*m` type-preserving automorphisms. -/
theorem card_induced_colorPreserving (hm : 1 < m)
    (e : cycleGraph (2 * m) ↪g Γ) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y) :
    Nat.card (colorPreserving (Γ.induce (Set.range e)) (fun x => color x.1)) = 2 * m := by
  rw [← Nat.card_congr (inducedDihedralEquiv hm e color hc).toEquiv, DihedralGroup.nat_card]

omit [NeZero m] [NeZero (2 * m)] in
/-- A faithful dihedral action fills the full type-preserving automorphism group.
Constructing that faithful action is the separate F.3.6 quotient obligation. -/
theorem surjective_of_injective_induced (hm : 1 < m)
    (e : cycleGraph (2 * m) ↪g Γ) (color : V → Bool)
    (hc : ∀ {x y}, Γ.Adj x y → color x ≠ color y)
    (ρ : DihedralGroup m →* colorPreserving (Γ.induce (Set.range e)) (fun x => color x.1))
    (hρ : Function.Injective ρ) : Function.Surjective ρ := by
  let : NeZero m := ⟨by omega⟩
  exact (Finite.injective_iff_surjective_of_equiv (inducedDihedralEquiv hm e color hc).toEquiv).mp hρ

end Transport

end GroupAction.DihedralPolygon.CycleAutomorphisms
