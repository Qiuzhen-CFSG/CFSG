module

public import Theory.Combinatorics.SimpleGraph.QuadrangleTwentySeven.Canonical
public import Mathlib.Data.Finite.Perm
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The automorphism bound for the 27-point quadrangle

An automorphism is determined by the image of a point, a chosen nonneighbor,
and the induced permutation of the five common-neighbor coordinates. This
provides the source bound `27 * 16 * 5! = 51840`.
-/

public section

open SimpleGraph
namespace Theory.Combinatorics.QuadrangleTwentySeven
universe u

abbrev AutoCode {V : Type u} (Γ : SimpleGraph V) : Type u :=
  Σ a : V, (↥(Far Γ a) × Equiv.Perm (Fin 5))


theorem farImage {V : Type u} {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
    {x y : V} (e : Γ ≃g Γ) (hy : Γᶜ.Adj x y) : Γᶜ.Adj (e x) (e y) :=
  ⟨e.injective.ne hy.1, fun hh => hy.2 (e.map_rel_iff'.mp hh)⟩

noncomputable def commonMap {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {x y : V} (e : Γ ≃g Γ) :
    Γ.commonNeighbors x y ≃ Γ.commonNeighbors (e x) (e y) where
  toFun z := ⟨e z.1, e.map_rel_iff'.mpr z.2.1, e.map_rel_iff'.mpr z.2.2⟩
  invFun z := ⟨e.symm z.1, by simpa using e.symm.map_rel_iff'.mpr z.2.1, by simpa using e.symm.map_rel_iff'.mpr z.2.2⟩
  left_inv z := by simp
  right_inv z := by simp

noncomputable def commonFin {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] (h : Γ.IsSRGWith 27 10 1 5) {a b : V}
    (hab : Γᶜ.Adj a b) : Fin 5 ≃ Γ.commonNeighbors a b :=
  (Equiv.cast (congrArg Fin (h.of_not_adj hab.1 hab.2).symm)).trans (Fintype.equivFin _).symm


noncomputable def autoCode {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {x y : V} (h : Γ.IsSRGWith 27 10 1 5)
    (hy : Γᶜ.Adj x y) (e : Γ ≃g Γ) : AutoCode Γ := by
  let hye := farImage e hy
  let p : Equiv.Perm (Fin 5) :=
    (commonFin h hy).trans ((commonMap e).trans (commonFin h hye).symm)
  exact ⟨e x, ⟨⟨e y,hye⟩,p⟩⟩


@[simp] theorem autoCode_perm_apply {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {x y : V} (h : Γ.IsSRGWith 27 10 1 5)
    (hy : Γᶜ.Adj x y) (e : Γ ≃g Γ) (i : Fin 5) :
    commonFin h (farImage e hy) ((autoCode h hy e).2.2 i) =
      commonMap e (commonFin h hy i) := by
  simp [autoCode]

private theorem iso_ext_of_common {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {x y : V} (h : Γ.IsSRGWith 27 10 1 5)
    (hy : Γᶜ.Adj x y) (e f : Γ ≃g Γ)
    (hxy : e x = f x)
    (hcommon : ∀ z : Γ.commonNeighbors x y, e z.1 = f z.1) : e = f := by
  let D := frame h hy
  let he : Γᶜ.Adj (e x) (e y) := farImage e hy
  let E := frame h he
  have hnear (i : Fin 5) (b : Bool) : e (D.point i b) = f (D.point i b) := by
    have hfalse : e (D.point i false) = f (D.point i false) := by
      exact hcommon ⟨D.point i false, D.near i false, D.selected i⟩
    cases b with
    | false => exact hfalse
    | true =>
      obtain ⟨k,c,hk⟩ := E.near_cases (e.map_rel_iff'.mpr (D.near i false))
      have hc : c = false := by
        have ha : Γ.Adj (e y) (E.point k c) := by
          rw [hk]
          exact e.map_rel_iff'.mpr (D.selected i)
        have hu : Γ.Adj (e y) (E.point k false) := E.selected k
        by_cases hc0 : c = false
        · exact hc0
        · have hc1 : c = true := Bool.eq_true_of_not_eq_false hc0
          exact (E.not_both h (⟨e y, he.1, he.2⟩ : Far Γ (e x)) k)
            ⟨by simpa using hu, by simpa [hc1] using ha⟩ |>.elim
      subst c
      have hm : Γ.Adj (E.point k false) (e (D.point i true)) := by
        rw [hk]
        exact e.map_rel_iff'.mpr (D.paired' i false)
      obtain ⟨j,d,hje⟩ := E.near_cases (e.map_rel_iff'.mpr (D.near i true))
      have hcoord := (E.adj_points_iff h k j false d).mp (by simpa [hje] using hm)
      rcases hcoord with ⟨rfl, hd⟩
      have hd' : d = true := Bool.eq_true_of_not_eq_false hd.symm
      subst d
      have hm' : Γ.Adj (E.point k false) (f (D.point i true)) := by
        rw [hk]
        change Γ.Adj (e (D.point i false)) (f (D.point i true))
        rw [hfalse]
        exact f.map_rel_iff'.mpr (D.paired' i false)
      have hfnear : Γ.Adj (e x) (f (D.point i true)) := by
        rw [hxy]
        exact f.map_rel_iff'.mpr (D.near i true)
      obtain ⟨j,d,hjf⟩ := E.near_cases hfnear
      have hcoord := (E.adj_points_iff h k j false d).mp (by simpa [hjf] using hm')
      rcases hcoord with ⟨rfl, hd⟩
      have hd' : d = true := Bool.eq_true_of_not_eq_false hd.symm
      subst d
      exact hje.symm.trans hjf
  apply RelIso.ext
  intro z
  by_cases hxz : z = x
  · simpa [hxz] using hxy
  by_cases haz : Γ.Adj x z
  · obtain ⟨i,b,hz⟩ := D.near_cases haz
    exact (congrArg e hz.symm).trans ((hnear i b).trans (congrArg f hz))
  · let ze : Far Γ (e x) := ⟨e z, fun heq => hxz (e.injective heq.symm),
      fun ha => haz (e.map_rel_iff'.mp ha)⟩
    let zf : Far Γ (e x) := ⟨f z, fun heq => hxz (f.injective (heq.symm.trans hxy)),
      fun ha => haz (f.map_rel_iff'.mp (hxy ▸ ha))⟩
    have hzfar : ze = zf := by
      apply E.far_eq_of_near_pattern h he
      intro a
      obtain ⟨i,b,ha⟩ := E.near_cases a.property
      let u : Near Γ x := ⟨e.symm a.val, by simpa using e.symm.map_rel_iff'.mpr a.property⟩
      obtain ⟨j,c,hj⟩ := D.near_cases u.property
      have hua : e u.val = a.val := by simp [u]
      have huf : e u.val = f u.val := by
        simpa [hj] using hnear j c
      constructor
      · intro hza
        change Γ.Adj (f z) a
        rw [← hua, huf]
        apply f.map_rel_iff'.mpr
        rw [← hua] at hza
        exact e.map_rel_iff'.mp hza
      · intro hza
        change Γ.Adj (e z) a
        rw [← hua]
        apply e.map_rel_iff'.mpr
        rw [← hua, huf] at hza
        exact f.map_rel_iff'.mp hza
    exact congrArg Subtype.val hzfar


private theorem commonFin_val_transport {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] (h : Γ.IsSRGWith 27 10 1 5)
    {a b a' b' : V} (p : Γᶜ.Adj a b) (q : Γᶜ.Adj a' b')
    (ha : a = a') (hb : b = b') (i : Fin 5) :
    (commonFin h p i).val = (commonFin h q i).val := by
  cases ha
  cases hb
  rfl

private theorem autoCode_injective {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] {x y : V} (h : Γ.IsSRGWith 27 10 1 5)
    (hy : Γᶜ.Adj x y) : Function.Injective (autoCode h hy) := by
  intro e f hc
  have hxy : e x = f x := congrArg Sigma.fst hc
  have hyy : e y = f y := congrArg (fun q : AutoCode Γ => (q.2.1).val) hc
  have hp : (autoCode h hy e).2.2 = (autoCode h hy f).2.2 :=
    congrArg (fun q => q.2.2) hc
  apply iso_ext_of_common h hy e f hxy
  intro z
  let i : Fin 5 := (commonFin h hy).symm z
  have hi : commonFin h hy i = z := by simp [i]
  have htransport :
      (commonFin h (farImage e hy) ((autoCode h hy f).2.2 i)).val =
        (commonFin h (farImage f hy) ((autoCode h hy f).2.2 i)).val :=
    commonFin_val_transport h (farImage e hy) (farImage f hy) hxy hyy _
  have hpe := congrArg Subtype.val (autoCode_perm_apply h hy e i)
  have hpf := congrArg Subtype.val (autoCode_perm_apply h hy f i)
  rw [hi] at hpe hpf
  have hm : (commonMap e z).val = (commonMap f z).val := by
    calc
      (commonMap e z).val = (commonFin h (farImage e hy)
          ((autoCode h hy e).2.2 i)).val := hpe.symm
      _ = (commonFin h (farImage f hy)
          ((autoCode h hy f).2.2 i)).val := by
            rw [hp]
            exact htransport
      _ = (commonMap f z).val := hpf
  exact hm

theorem autoCode_card {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] (h : Γ.IsSRGWith 27 10 1 5) : Nat.card (AutoCode Γ) = 27 * 16 * 120  := by
  classical
  let _ : Fintype (Equiv.Perm (Fin 5)) := Fintype.ofFinite _
  change Nat.card (Σ a : V, (↥(Far Γ a) × Equiv.Perm (Fin 5))) = _
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card]
  have hp : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_perm, Nat.card_eq_fintype_card]
    decide
  rw [hp]
  simp_rw [far_card h]
  simp [Finset.sum_const, h.card]


theorem automorphism_card_le {V : Type u} [Fintype V] {Γ : SimpleGraph V}
    [DecidableRel Γ.Adj] (h : Γ.IsSRGWith 27 10 1 5) :
    Nat.card (Γ ≃g Γ) ≤ 51840 := by
  classical
  have hpos : 0 < Fintype.card V := by rw [h.card]; decide
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  have hfpos : 0 < Fintype.card (Far Γ x) := by rw [far_card h]; decide
  obtain ⟨y, hy⟩ := Fintype.card_pos_iff.mp hfpos
  have hle : Nat.card (Γ ≃g Γ) ≤ Nat.card (AutoCode Γ) :=
    Nat.card_le_card_of_injective (autoCode h hy) (autoCode_injective h hy)
  rw [autoCode_card h] at hle
  simpa only [show 27 * 16 * 120 = 51840 by decide] using hle


end Theory.Combinatorics.QuadrangleTwentySeven
