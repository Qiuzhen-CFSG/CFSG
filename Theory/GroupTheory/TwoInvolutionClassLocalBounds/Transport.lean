module
public import Theory.GroupTheory.TwoInvolutionClassLocalBounds.Basic

/-!
# Transport of local conjugacy covers

Exchanging a commuting marked pair identifies its common stabilizer. The
class-size formula therefore compares the two local orbits using only the
orders of the two full centralizers. Multiplication by the central mark
then gives the slice needed by the refined half-order fiber bound.

Source motivation: Aschbacher–Smith, A.6.3, printed p. 64; the orbitwise
refinement retains the conjugators used by A.6.2.
-/

@[expose] public section
namespace Theory.GroupTheory.TwoInvolutionClassLocalBounds
variable {G : Type*} [Group G]

/-- The marked element, regarded as an element of its full centralizer. -/
def mark (x : G) : Centralizer x :=
  ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

private theorem commute_mark {x : G} (a : Centralizer x) : Commute (a : G) x :=
  Subgroup.mem_centralizer_singleton_iff.mp a.property

private theorem conj_mark {x : G} (a : Centralizer x) :
    MulAut.conj a (mark x) = mark x := by
  apply Subtype.ext
  change (a : G) * x * (a : G)⁻¹ = x
  exact mul_inv_eq_iff_eq_mul.mpr (commute_mark a).eq

/-- Translating a local class by the central mark preserves local conjugacy. -/
theorem isConj_mul_mark_iff {x : G} (a b : Centralizer x) :
    IsConj (a * mark x) (b * mark x) ↔ IsConj a b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    have he : MulAut.conj c (a * mark x) = b * mark x := hc
    rw [map_mul, conj_mark] at he
    exact mul_right_cancel he
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨c, ?_⟩
    change MulAut.conj c (a * mark x) = b * mark x
    rw [map_mul, conj_mark, show MulAut.conj c a = b from hc]

/-- Translation by the central mark gives an equivalence of the actual local classes. -/
def localOrbitMulMarkEquiv {x : G} (a : Centralizer x) :
    LocalOrbit a ≃ LocalOrbit (a * mark x) where
  toFun u := ⟨u.val * mark x, (isConj_mul_mark_iff a u.val).mpr u.property⟩
  invFun u := ⟨u.val * (mark x)⁻¹, by
    apply (isConj_mul_mark_iff a _).mp
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using u.property⟩
  left_inv u := by apply Subtype.ext; simp only [mul_assoc, mul_inv_cancel, mul_one]
  right_inv u := by apply Subtype.ext; simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- The stabilizer of a local class is the literal common centralizer. -/
def localStabilizerEquiv {x : G} (a : Centralizer x) :
    Subgroup.centralizer ({a} : Set (Centralizer x)) ≃
      ↥(Centralizer x ⊓ Centralizer (a : G)) where
  toFun u := ⟨u.val.val, u.val.property,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp u.property))⟩
  invFun u := ⟨⟨u.val, u.property.1⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp u.property.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An automorphism transports the common centralizer of a marked pair. -/
def commonCentralizerEquiv (e : G ≃* G) (x y : G) :
    ↥(Centralizer x ⊓ Centralizer y) ≃
      ↥(Centralizer (e x) ⊓ Centralizer (e y)) where
  toFun u := ⟨e u.val, by
    constructor
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using congrArg e
        (Subgroup.mem_centralizer_singleton_iff.mp u.property.1)
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using congrArg e
        (Subgroup.mem_centralizer_singleton_iff.mp u.property.2)⟩
  invFun u := ⟨e.symm u.val, by
    constructor
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm
        (Subgroup.mem_centralizer_singleton_iff.mp u.property.1)
    · apply Subgroup.mem_centralizer_singleton_iff.mpr
      simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm
        (Subgroup.mem_centralizer_singleton_iff.mp u.property.2)⟩
  left_inv u := by apply Subtype.ext; exact e.symm_apply_apply _
  right_inv u := by apply Subtype.ext; exact e.apply_symm_apply _

/-- Exchange the marked pair after moving its second member to a fixed representative. -/
def swappedMark {x y : G} (a : Centralizer x) (g : G)
    (hg : MulAut.conj g (a : G) = y) : Centralizer y :=
  ⟨MulAut.conj g x, Subgroup.mem_centralizer_singleton_iff.mpr (by
    have h : Commute (MulAut.conj g x) (MulAut.conj g (a : G)) :=
      (commute_mark a).symm.map (MulAut.conj g)
    rw [hg] at h
    exact h.eq)⟩

/-- The common stabilizer is the same on both sides of marked-pair exchange. -/
theorem local_stabilizer_card_swap [Finite G] {x y : G} (a : Centralizer x)
    (g : G) (hg : MulAut.conj g (a : G) = y) :
    Nat.card (Subgroup.centralizer ({a} : Set (Centralizer x))) =
      Nat.card (Subgroup.centralizer ({swappedMark a g hg} : Set (Centralizer y))) := by
  rw [Nat.card_congr (localStabilizerEquiv a),
    Nat.card_congr (localStabilizerEquiv (swappedMark a g hg)),
    Nat.card_congr (commonCentralizerEquiv (MulAut.conj g) x (a : G))]
  rw [hg]
  change Nat.card ↥(Centralizer (MulAut.conj g x) ⊓ Centralizer y) =
    Nat.card ↥(Centralizer y ⊓ Centralizer (MulAut.conj g x))
  rw [inf_comm]

/-- Local orbit sizes exchange in the ratio of the two full centralizer orders. -/
theorem local_orbit_card_swap [Finite G] {x y : G} (a : Centralizer x)
    (g : G) (hg : MulAut.conj g (a : G) = y) :
    Nat.card (LocalOrbit a) * Nat.card (Centralizer y) =
      Nat.card (LocalOrbit (swappedMark a g hg)) * Nat.card (Centralizer x) := by
  have h1 := ConjClasses.nat_card_carrier_mul_card_centralizer a
  have h2 := ConjClasses.nat_card_carrier_mul_card_centralizer (swappedMark a g hg)
  change Nat.card (LocalOrbit a) * _ = _ at h1
  change Nat.card (LocalOrbit (swappedMark a g hg)) * _ = _ at h2
  rw [← local_stabilizer_card_swap a g hg] at h2
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := Subgroup.centralizer ({a} : Set (Centralizer x))))
  rw [← h1, ← h2]
  ring

private theorem conj_comp (g h u : G) :
    MulAut.conj (g * h) u = MulAut.conj g (MulAut.conj h u) := by
  simp only [MulAut.conj_apply]
  group

private theorem conj_inverse_cancel (g u : G) :
    MulAut.conj g⁻¹ (MulAut.conj g u) = u := by
  simp only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel, mul_one]

/-- Conjugate marked pairs give conjugate exchanged marks in the other full centralizer. -/
theorem swappedMark_isConj {x y : G} (a b : Centralizer x)
    (g h : G) (hg : MulAut.conj g (a : G) = y) (hh : MulAut.conj h (b : G) = y)
    (hab : IsConj a b) : IsConj (swappedMark a g hg) (swappedMark b h hh) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  have hc' : MulAut.conj (c : G) (a : G) = (b : G) := congrArg Subtype.val hc
  have hcx : MulAut.conj (c : G) x = x :=
    mul_inv_eq_iff_eq_mul.mpr (commute_mark c).eq
  let k := h * (c : G) * g⁻¹
  have hky : MulAut.conj k y = y := by
    dsimp only [k]
    calc
      _ = MulAut.conj h (MulAut.conj (c : G) (MulAut.conj g⁻¹ y)) := by
        rw [conj_comp, conj_comp]
      _ = MulAut.conj h (MulAut.conj (c : G) (a : G)) := by
        rw [← hg, conj_inverse_cancel]
      _ = y := by rw [hc', hh]
  have hkm : MulAut.conj k (MulAut.conj g x) = MulAut.conj h x := by
    dsimp only [k]
    rw [conj_comp, conj_comp, conj_inverse_cancel, hcx]
  apply isConj_iff.mpr
  refine ⟨⟨k, Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp hky)⟩, ?_⟩
  exact Subtype.ext hkm

/-- Exchanging the marks preserves the ambient class of their product. -/
def swappedSlice {x y b : G} (a : Slice x y b) (g : G)
    (hg : MulAut.conj g (a.val : G) = y) : Slice y x b := by
  let q : Centralizer y := swappedMark a.val g hg
  refine ⟨q, isConj_iff.mpr ⟨g, rfl⟩, ?_⟩
  have hp : IsConj b (MulAut.conj g ((a.val : G) * x)) :=
    a.property.2.trans (isConj_iff.mpr ⟨g, rfl⟩)
  rw [map_mul, hg] at hp
  change IsConj b ((q : G) * y)
  have hq : (q : G) * y = y * (q : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp q.property
  exact hq.symm ▸ hp

/-- A local class cover transports across the incidence of marked commuting pairs.
The class-size bound changes by the exact ratio of the two full centralizers. -/
theorem exists_swapped_cover [Finite G] {ι : Type*} {x y b : G}
    (w : ι → Slice x y b) (n : ι → ℕ) {r : ℕ} (hr : 0 < r)
    (hcard : Nat.card (Centralizer x) = r * Nat.card (Centralizer y))
    (hcover : ∀ u : Slice x y b, ∃ i, IsConj (w i).val u.val)
    (hbound : ∀ i, Nat.card (LocalOrbit (w i).val) ≤ r * n i) :
    ∃ v : ι → Slice y x b,
      (∀ u : Slice y x b, ∃ i, IsConj (v i).val u.val) ∧
      (∀ i, Nat.card (LocalOrbit (v i).val) ≤ n i) := by
  classical
  have hg (i : ι) : ∃ g : G, MulAut.conj g ((w i).val : G) = y :=
    isConj_iff.mp (w i).property.1.symm
  let g (i : ι) := (hg i).choose
  have hgi (i : ι) : MulAut.conj (g i) ((w i).val : G) = y := (hg i).choose_spec
  let v (i : ι) := swappedSlice (w i) (g i) (hgi i)
  refine ⟨v, ?_, ?_⟩
  · intro u
    obtain ⟨h, hh⟩ := isConj_iff.mp u.property.1.symm
    let a := swappedSlice u h hh
    obtain ⟨i, hi⟩ := hcover a
    have ha : MulAut.conj h⁻¹ (a.val : G) = y := conj_inverse_cancel h y
    have hs := swappedMark_isConj (w i).val a.val (g i) h⁻¹ (hgi i) ha hi
    have he : swappedMark a.val h⁻¹ ha = u.val := by
      apply Subtype.ext
      change MulAut.conj h⁻¹ x = (u.val : G)
      exact (congrArg (MulAut.conj h⁻¹) hh).symm.trans
        (conj_inverse_cancel h (u.val : G))
    exact ⟨i, he ▸ hs⟩
  · intro i
    have he := local_orbit_card_swap (w i).val (g i) (hgi i)
    rw [hcard] at he
    have hi : Nat.card (LocalOrbit (w i).val) =
        r * Nat.card (LocalOrbit (v i).val) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Centralizer y))
      calc
        _ = Nat.card (LocalOrbit (swappedMark (w i).val (g i) (hgi i))) *
            (r * Nat.card (Centralizer y)) := he
        _ = _ := by change _ = r * Nat.card (LocalOrbit (swappedMark (w i).val (g i) (hgi i))) * _; ring
    exact Nat.le_of_mul_le_mul_left (hi.symm.trans_le (hbound i)) hr

private theorem square {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  simpa only [hx, pow_two] using pow_orderOf_eq_one x

/-- Translating a slice by an involutory mark exchanges the two ambient colors. -/
def sliceMulMarkEquiv {x a b : G} (hx : orderOf x = 2) :
    Slice x a b ≃ Slice x b a where
  toFun u := ⟨u.val * mark x, u.property.2, by
    change IsConj a (((u.val : G) * x) * x)
    simpa only [mul_assoc, square hx, mul_one] using u.property.1⟩
  invFun u := ⟨u.val * mark x, u.property.2, by
    change IsConj b (((u.val : G) * x) * x)
    simpa only [mul_assoc, square hx, mul_one] using u.property.1⟩
  left_inv u := by
    apply Subtype.ext; apply Subtype.ext
    change ((u.val : G) * x) * x = (u.val : G)
    rw [mul_assoc, square hx, mul_one]
  right_inv u := by
    apply Subtype.ext; apply Subtype.ext
    change ((u.val : G) * x) * x = (u.val : G)
    rw [mul_assoc, square hx, mul_one]

/-- The cover of the `t,t` slice at `z` induces the required local cover of
the `t,z` slice at `t`, with bounds divided by the centralizer ratio. -/
theorem exists_transported_cover [Finite G] {ι : Type*} {z t : G}
    (ht : orderOf t = 2) (w : ι → Slice z t t) (n : ι → ℕ) {r : ℕ} (hr : 0 < r)
    (hcard : Nat.card (Centralizer z) = r * Nat.card (Centralizer t))
    (hcover : ∀ u : Slice z t t, ∃ i, IsConj (w i).val u.val)
    (hbound : ∀ i, Nat.card (LocalOrbit (w i).val) ≤ r * n i) :
    ∃ v : ι → Slice t t z,
      (∀ u : Slice t t z, ∃ i, IsConj (v i).val u.val) ∧
      (∀ i, Nat.card (LocalOrbit (v i).val) ≤ n i) := by
  obtain ⟨q, hqcover, hqbound⟩ := exists_swapped_cover w n hr hcard hcover hbound
  let e : Slice t z t ≃ Slice t t z := sliceMulMarkEquiv ht
  refine ⟨fun i => e (q i), ?_, ?_⟩
  · intro u
    obtain ⟨i, hi⟩ := hqcover (e.symm u)
    have hh := (isConj_mul_mark_iff (q i).val (e.symm u).val).mpr hi
    have he : (e.symm u).val * mark t = u.val :=
      congrArg Subtype.val (e.apply_symm_apply u)
    exact ⟨i, he ▸ hh⟩
  · intro i
    change Nat.card (LocalOrbit ((q i).val * mark t)) ≤ n i
    rw [← Nat.card_congr (localOrbitMulMarkEquiv (q i).val)]
    exact hqbound i

end Theory.GroupTheory.TwoInvolutionClassLocalBounds
end
