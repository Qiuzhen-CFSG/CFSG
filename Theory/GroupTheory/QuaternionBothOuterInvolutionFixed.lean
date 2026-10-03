module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Conj
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Tactic.Group

/-!
# Fixed points of outer involutions on both quaternion factors

An involution preserving two commuting quaternion factors, and acting outerly
on each, has an elementary abelian fixed subgroup when the factors generate
the ambient group.

A kernel-checked finite table proves the key local identity: for an outer
involutory quaternion automorphism, a central displacement `x⁻¹ * e x` equals
`x²`. This includes both the fixed central elements and the inverted
noncentral axis. The normal-form encoding follows
`SpecificGroups/QuaternionEightOuterInvolution.lean`.

Write a fixed element as `b*c`. Its two displacements multiply to one, so
each lies in the intersection of the factors and is therefore central in its
own factor. The local identity gives `(b*c)² = b²*c² = 1`. Exponent two
then implies commutativity. In fact, the proof does not need the stipulated
order of the intersection.

Source: Janko–Thompson (1970), §4, printed pp.390–391, case (b)(i),
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
set_option maxRecDepth 10000 in
private theorem displacement_table : ∀ p : Q × Q,
    (∀ x : Q, pairMap p (pairMap p x) = x) →
    (¬ ∃ q : Q, ∀ x : Q, pairMap p x = q*x*q⁻¹) →
    ∀ x : Q, (∀ y : Q, y * (x⁻¹ * pairMap p x) = (x⁻¹ * pairMap p x)*y) →
      x^2 = x⁻¹ * pairMap p x := by
  decide
end QuaternionGroup

namespace QuaternionGroup
private theorem square_eq_displacement (e : MulAut (QuaternionGroup 2))
    (he : e^2 = 1) (ho : ¬ ∃ z, e = MulAut.conj z)
    (x : QuaternionGroup 2) (hx : x⁻¹ * e x ∈ Subgroup.center (QuaternionGroup 2)) :
    x^2 = x⁻¹ * e x := by
  let p : Q × Q := (e (a 1), e (xa 0))
  have hp (y : Q) : pairMap p y = e y := by
    cases y with
    | a i =>
      change (e (a 1)) ^ i.val = e (a i)
      rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
    | xa i =>
      change e (xa 0) * (e (a 1)) ^ i.val = e (xa i)
      rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
  have hi : ∀ y : Q, pairMap p (pairMap p y) = y := by
    intro y
    simpa only [hp, pow_two, MulAut.mul_apply, MulAut.one_apply] using
      DFunLike.congr_fun he y
  have hn : ¬ ∃ z : Q, ∀ y : Q, pairMap p y = z*y*z⁻¹ := by
    rintro ⟨z, hz⟩
    apply ho
    refine ⟨z, ?_⟩
    ext y
    exact (hp y).symm.trans (hz y)
  simpa only [hp] using displacement_table p hi hn x
    (by simpa only [hp] using Subgroup.mem_center_iff.mp hx)

private theorem square_eq_displacement_of_equiv {G : Type*} [Group G]
    (model : G ≃* QuaternionGroup 2) (e : MulAut G)
    (he : e^2 = 1) (ho : ¬ ∃ z, e = MulAut.conj z)
    (x : G) (hx : x⁻¹ * e x ∈ Subgroup.center G) : x^2 = x⁻¹ * e x := by
  let a := MulAut.congr model e
  have ha : a^2 = 1 := by dsimp [a]; rw [← map_pow, he, map_one]
  have ho' : ¬ ∃ z, a = MulAut.conj z := by
    rintro ⟨z, hz⟩
    apply ho
    refine ⟨model.symm z, ?_⟩
    ext y
    apply model.injective
    have h := DFunLike.congr_fun hz (model y)
    simpa [a, MulAut.congr_apply, MulAut.conj_apply] using h
  have hx' : (model x)⁻¹ * a (model x) ∈ Subgroup.center (QuaternionGroup 2) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := model.surjective y
    simpa [a, MulAut.congr_apply] using
      congrArg model (Subgroup.mem_center_iff.mp hx z)
  apply model.injective
  simpa [a, MulAut.congr_apply] using square_eq_displacement a ha ho' (model x) hx'
end QuaternionGroup

namespace Subgroup
open scoped Pointwise

private theorem factor_square_eq_displacement
    {G : Type*} [Group G] (B : Subgroup G)
    (model : B ≃* QuaternionGroup 2) (e : MulAut G) (he : e^2 = 1)
    (hBB : B.map e.toMonoidHom = B)
    (hBO : ¬ ∃ b : B, ∀ x : B, e (x : G) = (b : G)*x*(b : G)⁻¹)
    (b : B) (hd : ∀ x : B, (x : G) * ((b : G)⁻¹ * e b) =
      ((b : G)⁻¹ * e b) * x) : (b : G)^2 = (b : G)⁻¹ * e b := by
  let f : MulAut B := (e.subgroupMap B).trans (MulEquiv.subgroupCongr hBB)
  have hf (x : B) : (f x : G) = e x := rfl
  have hf2 : f^2 = 1 := by
    ext x
    change (f (f x) : G) = x
    rw [hf, hf]
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using
      DFunLike.congr_fun he (x : G)
  have hfo : ¬ ∃ z, f = MulAut.conj z := by
    rintro ⟨z, hz⟩
    apply hBO
    refine ⟨z, fun x => ?_⟩
    have h := congrArg Subtype.val (DFunLike.congr_fun hz x)
    exact h
  have hc : b⁻¹ * f b ∈ center B := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (hd x)
  exact congrArg Subtype.val
    (QuaternionGroup.square_eq_displacement_of_equiv model f hf2 hfo b hc)

/-- If an involution preserves two commuting quaternion factors and restricts
to an outer automorphism on each, its fixed subgroup is elementary abelian. -/
public theorem elementary_fixed_of_quaternion_both_outer_involution
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hsup : B ⊔ C = ⊤) (_hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (e : MulAut G) (he : e^2=1)
    (hBB : B.map e.toMonoidHom=B) (hCC : C.map e.toMonoidHom=C)
    (hBO : ¬ ∃ b : B, ∀ x : B, e (x : G) = (b : G)*x*(b : G)⁻¹)
    (hCO : ¬ ∃ c : C, ∀ x : C, e (x : G) = (c : G)*x*(c : G)⁻¹) :
    IsElementaryAbelian 2 (e.toMonoidHom.eqLocus (MonoidHom.id G)) := by
  obtain ⟨modelB⟩ := hB
  obtain ⟨modelC⟩ := hC
  have hsq (x : e.toMonoidHom.eqLocus (MonoidHom.id G)) : x^2=1 := by
    have hnorm : B ≤ normalizer (C : Set G) := by
      apply le_trans ?_ (centralizer_le_normalizer _)
      intro b hb c hc
      exact (hcomm b hb c hc).symm
    have hx : (x : G) ∈ (B : Set G) * (C : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B C hnorm, hsup]
      trivial
    obtain ⟨b, hb, c, hc, hbc⟩ := hx
    change b*c = (x : G) at hbc
    have hfixed : e (b*c) = b*c := by rw [hbc]; exact x.property
    have heb : e b ∈ B := hBB ▸ mem_map.mpr ⟨b,hb,rfl⟩
    have hec : e c ∈ C := hCC ▸ mem_map.mpr ⟨c,hc,rfl⟩
    let db := b⁻¹ * e b
    let dc := c⁻¹ * e c
    have hdbB : db ∈ B := B.mul_mem (B.inv_mem hb) heb
    have hdcC : dc ∈ C := C.mul_mem (C.inv_mem hc) hec
    have hprod : db * dc = 1 := by
      apply mul_left_cancel (a := b*c)
      calc
        (b*c) * (db*dc) = b * (c*db) * dc := by group
        _ = b * (db*c) * dc := by rw [← hcomm db hdbB c hc]
        _ = e b * e c := by dsimp [db, dc]; group
        _ = (b*c)*1 := by rw [← map_mul, hfixed, mul_one]
    have hdbC : db ∈ C := by
      rw [eq_inv_of_mul_eq_one_left hprod]
      exact C.inv_mem hdcC
    have hdcB : dc ∈ B := by
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact B.inv_mem hdbB
    have hb2 : b^2 = db := factor_square_eq_displacement B modelB e he hBB hBO
      ⟨b,hb⟩ (fun y => hcomm y y.property db hdbC)
    have hc2 : c^2 = dc := factor_square_eq_displacement C modelC e he hCC hCO
      ⟨c,hc⟩ (fun y => (hcomm dc hdcB y y.property).symm)
    apply Subtype.ext
    change (x : G)^2 = 1
    rw [← hbc, (show Commute b c from hcomm b hb c hc).mul_pow, hb2, hc2, hprod]
  have hinv (x : e.toMonoidHom.eqLocus (MonoidHom.id G)) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hsq x
  exact {
    toIsMulCommutative := ⟨⟨fun a b => by
      calc
        a*b = (a*b)⁻¹ := (hinv _).symm
        _ = b*a := by rw [mul_inv_rev, hinv, hinv]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
end Subgroup
