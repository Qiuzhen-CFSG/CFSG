module

public import Stellmacher.Recognition.SuzukiThreeAction
import Mathlib.Tactic.Group

/-!
# Bruhat coordinates for Suzuki's degree-28 action

The regular root group supplies unique coordinates on the large Bruhat cell.
An element swapping the two base points normalizes their common stabilizer.
These action-theoretic facts are the input to Suzuki's centralizer analysis.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
 group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections II–III, especially Lemmas 1–2 and 9–12.
-/

namespace Stellmacher.Recognition

open MulAction

namespace SuzukiThreeHypotheses

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- Evaluation at a point other than the base point is injective on the root group. -/
public theorem root_smul_injective (b : Ω) (hb : b ≠ a) :
    Function.Injective (fun q : Q => ((q : stabilizer G a) : G) • b) := by
  intro q r he
  obtain ⟨s, _, hs⟩ := h.regular b (((r : stabilizer G a) : G) • b) hb (by
    intro hr
    apply hb
    exact (MulAction.injective ((r : stabilizer G a) : G))
      (hr.trans (mem_stabilizer_iff.mp r.val.property).symm))
  exact (hs q he).trans (hs r rfl).symm

/-- A nonidentity root element fixes only the base point. -/
public theorem root_smul_eq_self_iff (b : Ω) (hb : b ≠ a) (q : Q) :
    ((q : stabilizer G a) : G) • b = b ↔ q = 1 := by
  constructor
  · intro he
    apply h.root_smul_injective b hb
    simpa using he
  · rintro rfl
    simp

omit h in
/-- An element exchanging two points conjugates their common stabilizer into itself. -/
public theorem swap_conj_mem_twoPoint (b : Ω) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b) :
    t⁻¹ * ((k : stabilizer G a) : G) * t ∈ stabilizer G a ∧
      (t⁻¹ * ((k : stabilizer G a) : G) * t) • b = b := by
  have hka : ((k : stabilizer G a) : G) • a = a :=
    mem_stabilizer_iff.mp (k : stabilizer G a).property
  have hkb : ((k : stabilizer G a) : G) • b = b :=
    mem_stabilizer_iff.mp k.property
  constructor
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, hta, hkb, ← hta, inv_smul_smul]
  · rw [mul_smul, mul_smul, htb, hka, ← htb, inv_smul_smul]

omit h in
/-- Conjugation on the two-point stabilizer induced by interchanging its points. -/
public def swapConj (b : Ω) (t : G) (hta : t • a = b) (htb : t • b = a) :
    stabilizer (stabilizer G a) b →* stabilizer (stabilizer G a) b where
  toFun k := ⟨⟨t⁻¹ * ((k : stabilizer G a) : G) * t,
    (swap_conj_mem_twoPoint b t hta htb k).1⟩,
    (swap_conj_mem_twoPoint b t hta htb k).2⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; simp
  map_mul' k l := by
    apply Subtype.ext
    apply Subtype.ext
    change t⁻¹ * (_ * _) * t = (t⁻¹ * _ * t) * (t⁻¹ * _ * t)
    group

omit h in
/-- The ambient value of the induced conjugation. -/
public theorem swapConj_coe (b : Ω) (t : G) (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b) :
    (((swapConj b t hta htb k) : stabilizer G a) : G) =
      t⁻¹ * ((k : stabilizer G a) : G) * t := by
  rfl

/-- Existence of the large-cell coordinates `u k t v` (Suzuki, Lemma 1). -/
public theorem exists_bruhat (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a) (x : G)
    (hx : x ∉ stabilizer G a) :
    ∃ (u : Q) (k : stabilizer (stabilizer G a) b) (v : Q),
      x = ((u : stabilizer G a) : G) * ((k : stabilizer G a) : G) * t *
        ((v : stabilizer G a) : G) := by
  have hxa : x • a ≠ a := hx
  have hxia : x⁻¹ • a ≠ a := by
    intro he
    apply hxa
    exact (inv_smul_eq_iff.mp he).symm
  obtain ⟨u, hu, _⟩ := h.regular b (x • a) hb hxa
  obtain ⟨v, hv, _⟩ := h.regular (x⁻¹ • a) b hxia hb
  have hv' : (((v : stabilizer G a) : G)⁻¹) • b = x⁻¹ • a := by
    rw [← hv, inv_smul_smul]
  have hua : ((u : stabilizer G a) : G) • a = a :=
    mem_stabilizer_iff.mp (u : stabilizer G a).property
  have hva : ((v : stabilizer G a) : G) • a = a :=
    mem_stabilizer_iff.mp (v : stabilizer G a).property
  have htia : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
  have htib : t⁻¹ • b = a := by rw [← hta, inv_smul_smul]
  let z := ((u : stabilizer G a) : G)⁻¹ * x *
    ((v : stabilizer G a) : G)⁻¹ * t⁻¹
  have hza : z • a = a := by
    dsimp [z]
    simp only [mul_smul, htia, hv', smul_inv_smul]
    exact inv_smul_eq_iff.mpr hua.symm
  have hzb : z • b = b := by
    dsimp [z]
    have hvi : ((v : stabilizer G a) : G)⁻¹ • a = a :=
      inv_smul_eq_iff.mpr hva.symm
    simp only [mul_smul, htib, hvi]
    exact inv_smul_eq_iff.mpr hu.symm
  refine ⟨u, ⟨⟨z, hza⟩, hzb⟩, v, ?_⟩
  change x = _ * z * t * _
  dsimp [z]
  group

/-- Uniqueness of the large-cell coordinates (Suzuki, Lemma 1). -/
public theorem bruhat_injective (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a) :
    Function.Injective (fun p : Q × stabilizer (stabilizer G a) b × Q =>
      ((p.1 : stabilizer G a) : G) * ((p.2.1 : stabilizer G a) : G) * t *
        ((p.2.2 : stabilizer G a) : G)) := by
  rintro ⟨u, k, v⟩ ⟨u', k', v'⟩ he
  have hva : ((v : stabilizer G a) : G) • a = a := v.val.property
  have hva' : ((v' : stabilizer G a) : G) • a = a := v'.val.property
  have hua : ((u : stabilizer G a) : G) • a = a := u.val.property
  have hua' : ((u' : stabilizer G a) : G) • a = a := u'.val.property
  have hka : ((k : stabilizer G a) : G) • a = a := k.val.property
  have hka' : ((k' : stabilizer G a) : G) • a = a := k'.val.property
  have hkb : ((k : stabilizer G a) : G) • b = b := k.property
  have hkb' : ((k' : stabilizer G a) : G) • b = b := k'.property
  have hu : u = u' := by
    apply h.root_smul_injective b hb
    have he' := congrArg (fun g : G => g • a) he
    simpa only [mul_smul, hva, hva', hta, hkb, hkb'] using he'
  have htia : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
  have hv : v = v' := by
    have he' := congrArg (fun g : G => g⁻¹ • a) he
    have hui : ((u : stabilizer G a) : G)⁻¹ • a = a := inv_smul_eq_iff.mpr hua.symm
    have hui' : ((u' : stabilizer G a) : G)⁻¹ • a = a := inv_smul_eq_iff.mpr hua'.symm
    have hki : ((k : stabilizer G a) : G)⁻¹ • a = a := inv_smul_eq_iff.mpr hka.symm
    have hki' : ((k' : stabilizer G a) : G)⁻¹ • a = a := inv_smul_eq_iff.mpr hka'.symm
    have hvInv : v⁻¹ = v'⁻¹ := by
      apply h.root_smul_injective b hb
      simpa only [mul_inv_rev, mul_smul, hui, hui', hki, hki', htia, Subgroup.coe_inv] using he'
    exact inv_injective hvInv
  have hk : k = k' := by
    subst u'
    subst v'
    dsimp only at he
    have hval := mul_left_cancel (mul_right_cancel (mul_right_cancel he))
    exact Subtype.ext (Subtype.ext hval)
  subst u'
  subst k'
  subst v'
  rfl

/-- The involutions in the large cell are conjugates by roots of involutions
in the torus coset (Suzuki, Lemma 1, last assertion). -/
public theorem bruhat_sq_eq_one_iff (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (u : Q) (k : stabilizer (stabilizer G a) b) (v : Q) :
    (((u : stabilizer G a) : G) * ((k : stabilizer G a) : G) * t *
      ((v : stabilizer G a) : G)) ^ 2 = 1 ↔
    v = u⁻¹ ∧ (((k : stabilizer G a) : G) * t) ^ 2 = 1 := by
  let w := ((u : stabilizer G a) : G) * ((k : stabilizer G a) : G) * t *
    ((v : stabilizer G a) : G)
  have hua : ((u : stabilizer G a) : G) • a = a := u.val.property
  have hva : ((v : stabilizer G a) : G) • a = a := v.val.property
  have hka : ((k : stabilizer G a) : G) • a = a := k.val.property
  have hkb : ((k : stabilizer G a) : G) • b = b := k.property
  have hui : ((u : stabilizer G a) : G)⁻¹ • a = a :=
    inv_smul_eq_iff.mpr hua.symm
  have hki : ((k : stabilizer G a) : G)⁻¹ • a = a :=
    inv_smul_eq_iff.mpr hka.symm
  have htia : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
  constructor
  · intro hw
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by simpa [w, pow_two] using hw)
    have hvu : v⁻¹ = u := by
      apply h.root_smul_injective b hb
      have he := congrArg (fun g : G => g • a) hwi
      simpa only [w, mul_inv_rev, mul_smul, hui, hki, htia, hva, hta, hkb,
        Subgroup.coe_inv] using he
    have hv : v = u⁻¹ := by rw [← hvu, inv_inv]
    refine ⟨hv, ?_⟩
    rw [hv] at hw
    calc
      _ = ((u : stabilizer G a) : G)⁻¹ *
          (((u : stabilizer G a) : G) * ((k : stabilizer G a) : G) * t *
            (((u⁻¹ : Q) : stabilizer G a) : G)) ^ 2 * ((u : stabilizer G a) : G) := by
        simp only [Subgroup.coe_inv, pow_two]
        group
      _ = 1 := by rw [hw]; group
  · rintro ⟨rfl, hkt⟩
    calc
      _ = ((u : stabilizer G a) : G) * (((k : stabilizer G a) : G) * t) ^ 2 *
          ((u : stabilizer G a) : G)⁻¹ := by
        simp only [Subgroup.coe_inv, pow_two]
        group
      _ = 1 := by rw [hkt]; group

/-- A torus element centralized by an element outside the point stabilizer is
fixed by the interchange of the two points (Suzuki, Lemma 2, first step). -/
public theorem swap_conj_eq_of_commute_outside (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b) (x : G)
    (hx : x ∉ stabilizer G a)
    (hcomm : ((k : stabilizer G a) : G) * x = x * ((k : stabilizer G a) : G)) :
    t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G) := by
  obtain ⟨u, l, v, hx'⟩ := h.exists_bruhat b hb t hta htb x hx
  have htia : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
  have htib : t⁻¹ • b = a := by rw [← hta, inv_smul_smul]
  have hkT := swap_conj_mem_twoPoint b t⁻¹ htia htib k
  simp only [inv_inv] at hkT
  let kT : stabilizer (stabilizer G a) b :=
    ⟨⟨t * ((k : stabilizer G a) : G) * t⁻¹, hkT.1⟩, hkT.2⟩
  let u' : Q := ⟨k.val * u.val * k.val⁻¹,
    (inferInstance : Q.Normal).conj_mem u.val u.property k.val⟩
  let v' : Q := ⟨k.val⁻¹ * v.val * k.val,
    (inferInstance : Q.Normal).conj_mem' v.val v.property k.val⟩
  have he : (u', k * l, v) = (u, l * kT, v') := by
    apply h.bruhat_injective b hb t hta htb
    change
      (((k : stabilizer G a) : G) * ((u : stabilizer G a) : G) *
        ((k : stabilizer G a) : G)⁻¹) *
        (((k : stabilizer G a) : G) * ((l : stabilizer G a) : G)) * t *
        ((v : stabilizer G a) : G) =
      ((u : stabilizer G a) : G) *
        (((l : stabilizer G a) : G) * (t * ((k : stabilizer G a) : G) * t⁻¹)) * t *
        (((k : stabilizer G a) : G)⁻¹ * ((v : stabilizer G a) : G) *
          ((k : stabilizer G a) : G))
    calc
      _ = ((k : stabilizer G a) : G) * x := by rw [hx']; group
      _ = x * ((k : stabilizer G a) : G) := hcomm
      _ = _ := by rw [hx']; group
  have heK : k * l = l * kT := congrArg (fun p => p.2.1) he
  let _ : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  have hk : k = kT := by
    rw [mul_comm' k l] at heK
    exact mul_left_cancel heK
  have hkval : ((k : stabilizer G a) : G) =
      t * ((k : stabilizer G a) : G) * t⁻¹ :=
    congrArg (fun z : stabilizer (stabilizer G a) b => ((z : stabilizer G a) : G)) hk
  calc
    _ = t⁻¹ * (t * ((k : stabilizer G a) : G) * t⁻¹) * t :=
      congrArg (fun z : G => t⁻¹ * z * t) hkval
    _ = _ := by group

/-- If swapping the points moves a torus element, that element fixes no
nonidentity root element (Suzuki, Lemma 2, second step). -/
public theorem root_eq_one_of_commute_of_swap_conj_ne (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b)
    (hk : t⁻¹ * ((k : stabilizer G a) : G) * t ≠ ((k : stabilizer G a) : G))
    (q : Q) (hq : ((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) =
      ((q : stabilizer G a) : G) * ((k : stabilizer G a) : G)) : q = 1 := by
  by_contra hqne
  have htia : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
  have htib : t⁻¹ • b = a := by rw [← hta, inv_smul_smul]
  let _ : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  obtain ⟨m, hm⟩ := (swapConj b t⁻¹ htia htib).map_cyclic
  have hkm : t * ((k : stabilizer G a) : G) * t⁻¹ =
      ((k : stabilizer G a) : G) ^ m := by
    have he := congrArg
      (fun z : stabilizer (stabilizer G a) b => ((z : stabilizer G a) : G)) (hm k)
    simpa only [swapConj_coe, inv_inv, Subgroup.coe_zpow] using he
  let x := t⁻¹ * ((q : stabilizer G a) : G) * t
  have hx : x ∉ stabilizer G a := by
    intro hx
    have hfix : t⁻¹ • (((q : stabilizer G a) : G) • b) = a := by
      simpa only [x, mem_stabilizer_iff, mul_smul, hta] using hx
    have hqb : ((q : stabilizer G a) : G) • b = b := by
      simpa only [hta] using inv_smul_eq_iff.mp hfix
    exact hqne ((h.root_smul_eq_self_iff b hb q).mp hqb)
  have hcommPow := (show Commute ((k : stabilizer G a) : G)
    ((q : stabilizer G a) : G) from hq).zpow_left m
  rw [← hkm] at hcommPow
  have hxcomm : ((k : stabilizer G a) : G) * x =
      x * ((k : stabilizer G a) : G) := by
    dsimp [x]
    calc
      _ = t⁻¹ * ((t * ((k : stabilizer G a) : G) * t⁻¹) *
          ((q : stabilizer G a) : G)) * t := by group
      _ = t⁻¹ * (((q : stabilizer G a) : G) *
          (t * ((k : stabilizer G a) : G) * t⁻¹)) * t := by rw [hcommPow.eq]
      _ = _ := by group
  exact hk (h.swap_conj_eq_of_commute_outside b hb t hta htb k x hx hxcomm)

/-- The centralizer of a torus element moved by the swap is contained in the
two-point stabilizer (Suzuki, Lemma 2). -/
public theorem fixes_pair_of_commute_of_swap_conj_ne (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b)
    (hk : t⁻¹ * ((k : stabilizer G a) : G) * t ≠ ((k : stabilizer G a) : G))
    (x : G) (hxcomm : ((k : stabilizer G a) : G) * x =
      x * ((k : stabilizer G a) : G)) : x • a = a ∧ x • b = b := by
  have hxa : x • a = a := by
    by_contra hxa
    exact hk (h.swap_conj_eq_of_commute_outside b hb t hta htb k x hxa hxcomm)
  have hxb : x • b ≠ a := by
    intro he
    exact hb ((MulAction.injective x) (he.trans hxa.symm))
  obtain ⟨q, hq, _⟩ := h.regular b (x • b) hb hxb
  have hqa : ((q : stabilizer G a) : G) • a = a := q.val.property
  let lG := ((q : stabilizer G a) : G)⁻¹ * x
  have hla : lG • a = a := by
    dsimp only [lG]
    rw [mul_smul, hxa]
    exact inv_smul_eq_iff.mpr hqa.symm
  have hlb : lG • b = b := by
    dsimp only [lG]
    rw [mul_smul]
    exact inv_smul_eq_iff.mpr hq.symm
  let l : stabilizer (stabilizer G a) b := ⟨⟨lG, hla⟩, hlb⟩
  let _ : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  have hkl : ((k : stabilizer G a) : G) * lG =
      lG * ((k : stabilizer G a) : G) :=
    congrArg (fun z : stabilizer (stabilizer G a) b => ((z : stabilizer G a) : G))
      (mul_comm' k l)
  have hxq : x = ((q : stabilizer G a) : G) * lG := by dsimp [lG]; group
  have hkq : ((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) =
      ((q : stabilizer G a) : G) * ((k : stabilizer G a) : G) := by
    apply mul_right_cancel (b := lG)
    calc
      _ = ((k : stabilizer G a) : G) * x := by rw [hxq]; group
      _ = x * ((k : stabilizer G a) : G) := hxcomm
      _ = _ := by rw [hxq, mul_assoc, ← hkl]; group
  have hqone := h.root_eq_one_of_commute_of_swap_conj_ne b hb t hta htb k hk q hkq
  exact ⟨hxa, by simpa [hqone] using hq.symm⟩

/-- Conjugation by the two-point stabilizer is faithful on the root group. -/
public theorem twoPoint_eq_one_of_centralizes_root [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (k : stabilizer (stabilizer G a) b)
    (hk : ∀ q : Q, ((k : stabilizer G a) : G) * ((q : stabilizer G a) : G) =
      ((q : stabilizer G a) : G) * ((k : stabilizer G a) : G)) : k = 1 := by
  have hka : ((k : stabilizer G a) : G) • a = a := k.val.property
  have hkb : ((k : stabilizer G a) : G) • b = b := k.property
  have he : ((k : stabilizer G a) : G) = 1 := by
    apply eq_of_smul_eq_smul (fun y : Ω => ?_)
    rw [one_smul]
    by_cases hy : y = a
    · simpa [hy] using hka
    · obtain ⟨q, hq, _⟩ := h.regular b y hb hy
      calc
        ((k : stabilizer G a) : G) • y =
            ((k : stabilizer G a) : G) • (((q : stabilizer G a) : G) • b) :=
          congrArg (fun z : Ω => ((k : stabilizer G a) : G) • z) hq.symm
        _ = (((k : stabilizer G a) : G) * ((q : stabilizer G a) : G)) • b :=
          (mul_smul _ _ _).symm
        _ = y := by rw [hk q, mul_smul, hkb, hq]
  exact Subtype.ext (Subtype.ext he)

end SuzukiThreeHypotheses
end Stellmacher.Recognition
