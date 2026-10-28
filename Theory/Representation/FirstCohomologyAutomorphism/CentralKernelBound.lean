module
public import Theory.Representation.FirstCohomology
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.Group

/-!
# Bounding centralizing actors by commutator cocycles

A subgroup centralizing an invariant layer acts on a perfect subgroup by
commutator cocycles. Project these through specified module coordinates and
an actual quotient of the perfect subgroup. When the coordinate kernel is
central, the three-subgroups lemma makes the cocycle kernel centralize the
whole perfect subgroup. Its order is therefore bounded by the cocycle-space
order times the actual centralizer order.

This is the group-theoretic form of the connecting-map bound in
Aschbacher--Smith C.1.13(b), printed pp.124--125, used in12.6.2,p.828.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G A W : Type*} [Group G] [Finite G] [Group A]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A centralizing actor is detected modulo its centralizer by quotient-valued
commutator cocycles. Perfectness removes the central error in the coordinates. -/
theorem card_le_cocycles_mul_centralizer
    (P L N : Subgroup G) [Group.IsPerfect L]
    (hLN : L ≤ normalizer (N : Set G))
    (hPN : P ≤ centralizer (N : Set G)) (hcomm : ⁅P,L⁆ ≤ N)
    (f : L →* A) (hf : Function.Surjective f)
    (m : N →* Multiplicative W) (ρ : Representation (ZMod 2) A W)
    (he : ∀ (l : L) (n : N),
      m (N.normalizerMonoidHom ⟨l,hLN l.property⟩ n) =
        Multiplicative.ofAdd (ρ (f l) (m n).toAdd))
    (hk : ∀ n : N, m n = 1 → (n : G) ∈ centralizer (L : Set G))
    (hd : ∀ (p : P) (l : L), f l = 1 →
      m ⟨⁅(p : G),(l : G)⁆,hcomm (commutator_mem_commutator p.property l.property)⟩ = 1)
    [Finite (cocycles ρ)] :
    Nat.card P ≤ Nat.card (cocycles ρ) * Nat.card ((centralizer (L : Set G)).subgroupOf P) := by
  classical
  let d (p : P) (l : L) : N :=
    ⟨⁅(p : G),(l : G)⁆,hcomm (commutator_mem_commutator p.property l.property)⟩
  let c (p : P) (l : L) : W := (m (d p l)).toAdd
  have hc (p : P) (l t : L) : c p (l*t) = ρ (f l) (c p t) + c p l := by
    have hdlt : d p (l*t) = d p l * N.normalizerMonoidHom ⟨l,hLN l.property⟩ (d p t) := by
      apply Subtype.ext
      change ⁅(p:G),(l:G)*(t:G)⁆ = ⁅(p:G),(l:G)⁆ * ((l:G)*⁅(p:G),(t:G)⁆*(l:G)⁻¹)
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    dsimp only [c]
    rw [hdlt,map_mul,he]
    change (m (d p l)).toAdd + ρ (f l) (m (d p t)).toAdd = _
    exact add_comm _ _
  have hc0 (p : P) (l : L) (hl : f l = 1) : c p l = 0 :=
    congrArg Multiplicative.toAdd (hd p l hl)
  have hsame (p : P) {l t : L} (h : f l = f t) : c p l = c p t := by
    have hh := hc p t (t⁻¹*l)
    have hz := hc0 p (t⁻¹*l) (by rw [map_mul,map_inv,h,inv_mul_cancel])
    simpa only [mul_inv_cancel_left,hz,map_zero,zero_add] using hh
  let b (a : A) : L := (hf a).choose
  have hb (a : A) : f (b a) = a := (hf a).choose_spec
  let z (p : P) : cocycles ρ := ⟨fun a => c p (b a),by
    intro a t
    exact (hsame p (show f (b (a*t)) = f (b a*b t) by rw [map_mul,hb,hb,hb])).trans
      (by rw [hc,hb])⟩
  have hz (p : P) (l : L) : (z p).val (f l) = c p l := hsame p (hb (f l))
  have hmul (p q : P) (l : L) : d (p*q) l = d q l * d p l := by
    apply Subtype.ext
    change ⁅(p:G)*(q:G),(l:G)⁆ = ⁅(q:G),(l:G)⁆ * ⁅(p:G),(l:G)⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      ←hPN p.property _ (d q l).property,mul_inv_cancel_right]
  let F : P →* Multiplicative (cocycles ρ) := {
    toFun := fun p => Multiplicative.ofAdd (z p)
    map_one' := by
      apply Subtype.ext
      funext a
      change (m (d 1 (b a))).toAdd = 0
      have hd1 : d 1 (b a) = 1 := Subtype.ext (commutatorElement_one_left _)
      rw [hd1,map_one]
      rfl
    map_mul' := by
      intro p q
      apply Subtype.ext
      funext a
      change (m (d (p*q) (b a))).toAdd = (m (d p (b a))).toAdd + (m (d q (b a))).toAdd
      rw [hmul,map_mul]
      exact add_comm _ _ }
  let C := F.ker.map P.subtype
  have hCL : ⁅C,L⁆ ≤ centralizer (L : Set G) := by
    apply commutator_le.mpr
    rintro x ⟨p,hp,rfl⟩ l hl
    apply hk (d p ⟨l,hl⟩)
    have hh := congrArg (fun w : Multiplicative (cocycles ρ) => w.toAdd.val (f ⟨l,hl⟩)) hp
    change (z p).val (f ⟨l,hl⟩) = 0 at hh
    rw [hz] at hh
    exact Multiplicative.toAdd.injective hh
  have hCLbot : ⁅⁅C,L⁆,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hCL
  have hLC : ⁅L,C⁆ = ⊥ := by
    have hh : ⁅⁅L,L⁆,C⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
      (by simpa only [commutator_comm L C] using hCLbot) hCLbot
    simpa only [commutator_eq_self] using hh
  have hFC : F.ker ≤ (centralizer (L : Set G)).subgroupOf P := by
    intro p hp
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLC)
      (mem_map_of_mem P.subtype hp)
  have hcard := card_eq_card_quotient_mul_card_subgroup F.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange F).toEquiv] at hcard
  calc
    Nat.card P = Nat.card F.range * Nat.card F.ker := hcard
    _ ≤ Nat.card (Multiplicative (cocycles ρ)) *
        Nat.card ((centralizer (L : Set G)).subgroupOf P) :=
      Nat.mul_le_mul (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
        (card_le_of_le hFC)
    _ = _ := by rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (cocycles ρ) ≃ cocycles ρ)]
end Theory.GroupTheory
