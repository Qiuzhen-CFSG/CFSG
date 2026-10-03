module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Odd centralizer index for isolated involutions

If an involution `t` has no distinct conjugate commuting with it, its
centralizer has odd index. Conjugation by `t` permutes the conjugacy class
of `t` with square equal to the identity. Isolation makes `t` its unique
fixed point, so the class cardinality is congruent to one modulo two.
Orbit-stabilizer identifies that cardinality with the centralizer index.

This is the local reduction used in the proof of Glauberman's Z-star theorem.
The argument is ported from the historical `Submission/OddIndex.lean` at
commit `c3503435`, using Mathlib's fixed-point congruence theorem in place of
the historical explicit pair-removal induction. The hypotheses and conclusion
are unchanged mathematically; a `Finite` instance suffices for the group.
-/

namespace Glauberman.ZStar

/-- The centralizer of an isolated involution has odd index. -/
public theorem odd_index_of_centralizer
    {G : Type*} [Group G] [Finite G] {t : G} (ht2 : t * t = 1) (_ht1 : t ≠ 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) : Odd (Subgroup.centralizer {t}).index := by
  classical
  let C := MulAction.orbit (ConjAct G) t
  let : Fintype C := Fintype.ofFinite C
  let f : Function.End C := fun x => ConjAct.toConjAct t • x
  have hf : f ^ (2 ^ 1) = 1 := by
    funext x
    change ConjAct.toConjAct t • (ConjAct.toConjAct t • x) = x
    rw [← mul_smul, ← map_mul, ht2, map_one, one_smul]
  let a : C := ⟨t, MulAction.mem_orbit_self t⟩
  have ha : f a = a := by
    apply Subtype.ext
    change t * t * t⁻¹ = t
    simp
  have hfixed : ∀ x : C, f x = x → x = a := by
    intro x hx
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
    have hxv := congrArg Subtype.val hx
    change t * x.val * t⁻¹ = x.val at hxv
    have hcomm : x.val * t = t * x.val := by
      calc
        x.val * t = (t * x.val * t⁻¹) * t := congrArg (· * t) hxv.symm
        _ = t * x.val := by simp [mul_assoc]
    apply Subtype.ext
    change x.val = t
    have hg' : ConjAct.ofConjAct g * t * (ConjAct.ofConjAct g)⁻¹ = x.val := hg
    rw [← hg'] at hcomm ⊢
    exact hisolated (ConjAct.ofConjAct g) hcomm
  let : Unique (Function.fixedPoints f) :=
    { default := ⟨a, ha⟩
      uniq := fun x => Subtype.ext (hfixed x.val x.property) }
  have hcard := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  rw [Fintype.card_unique (α := Function.fixedPoints f)] at hcard
  have hodd : Odd (Nat.card C) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact hcard
  have hindex : (Subgroup.centralizer {t}).index = Nat.card C := by
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    calc
      _ = (MulAction.stabilizer (ConjAct G) t).index :=
        Subgroup.index_comap_of_surjective
          (MulAction.stabilizer (ConjAct G) t)
          (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective
      _ = Nat.card C := MulAction.index_stabilizer (ConjAct G) t
  rwa [hindex]

end Glauberman.ZStar
