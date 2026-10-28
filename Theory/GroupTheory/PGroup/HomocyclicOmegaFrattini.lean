module

public import Theory.GroupTheory.PGroup.HomocyclicFrattini
public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The natural power bridge between homocyclic Frattini and omega quotients

For a finite coordinate group `(Z/p^a)^κ`, with `a ≥ 1`, the power map
`x ↦ x^(p^(a-1))` has kernel the Frattini subgroup and image `Ω₁`.
Coordinate divisibility proves both assertions. Transport through any actual
homocyclic isomorphism gives the same power formula on the original group;
that formula proves equivariance under every automorphism, without choosing
unrelated bases for the two elementary quotients.

The final constructions compare the Frattini quotients of the full group and
its omega subgroup, both in the homocyclic case and for exponent-p groups
(including the exponent-p extraspecial groups).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the homocyclic
and extraspecial alternatives in A.3.6, pp.43–45, and the inversion used in
the first paragraph of the proof of 13.1.9, p.869.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace HomocyclicOmegaFrattini

private theorem coord_ker (p a : ℕ) [Fact p.Prime] (ha : 1 ≤ a) (z : ZMod (p^a)) :
    (p^(a-1) : ℕ) • z = 0 ↔
      ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p) z = 0 := by
  have hp : 0 < p^(a-1) := pow_pos (Fact.out : p.Prime).pos _
  have hpa : p^a = p^(a-1)*p := by rw [← pow_succ, Nat.sub_add_cancel ha]
  have hz : (p^(a-1) : ℕ) • z = ((p^(a-1)*z.val : ℕ) : ZMod (p^a)) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul]
  rw [hz, ZMod.natCast_eq_zero_iff]
  conv_lhs => lhs; rw [hpa]
  rw [Nat.mul_dvd_mul_iff_left hp]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

private theorem coord_surj (p a : ℕ) [Fact p.Prime] (ha : 1 ≤ a) (z : ZMod (p^a))
    (hz : p • z = 0) : ∃ y : ZMod (p^a), (p^(a-1) : ℕ) • y = z := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpa : p^a = p*p^(a-1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  have hd : p^(a-1) ∣ z.val := by
    have hh : ((p*z.val : ℕ) : ZMod (p^a)) = 0 := by
      simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hz
    rw [ZMod.natCast_eq_zero_iff] at hh
    have hh' : p * p^(a-1) ∣ p * z.val := hpa ▸ hh
    exact (Nat.mul_dvd_mul_iff_left hp).mp hh'
  obtain ⟨y, hy⟩ := hd
  refine ⟨y, ?_⟩
  rw [nsmul_eq_mul, ← Nat.cast_mul, ← hy, ZMod.natCast_zmod_val]

variable (κ : Type*) (p a : ℕ) [Fact p.Prime] (ha : 1 ≤ a)

include ha in
omit [Fact p.Prime] in
private theorem pow_mem (x : StandardHomocyclicCover κ (p^a)) :
    x ^ (p^(a-1)) ∈ omega (StandardHomocyclicCover κ (p^a)) (p := p) 1 := by
  rw [OmegaAction.omega_eq_pow_ker]
  change (x ^ (p^(a-1))) ^ (p^1) = 1
  rw [pow_one, ← pow_mul, ← pow_succ, Nat.sub_add_cancel ha]
  apply Multiplicative.toAdd.injective
  funext i
  change (p^a) • x.toAdd i = 0
  rw [nsmul_eq_mul]
  simp

noncomputable def powerMap : StandardHomocyclicCover κ (p^a) →*
    omega (StandardHomocyclicCover κ (p^a)) (p := p) 1 :=
  (powMonoidHom (p^(a-1))).codRestrict _ (by exact pow_mem κ p a ha)

theorem powerMap_ker [Fintype κ] :
    (powerMap κ p a ha).ker = frattini (StandardHomocyclicCover κ (p^a)) := by
  rw [standardHomocyclicCover_frattini_eq_reduction_ker κ p a ha]
  ext x
  change (⟨x ^ (p^(a-1)), _⟩ : omega (StandardHomocyclicCover κ (p^a)) (p := p) 1) = 1 ↔ _
  rw [Subtype.ext_iff]
  change x ^ (p^(a-1)) = 1 ↔ standardHomocyclicCoverReduction κ p a ha x = 1
  constructor
  · intro hx
    apply Multiplicative.toAdd.injective
    funext i
    apply (coord_ker p a ha (x.toAdd i)).mp
    exact congrArg (fun z : StandardHomocyclicCover κ (p^a) => z.toAdd i) hx
  · intro hx
    apply Multiplicative.toAdd.injective
    funext i
    apply (coord_ker p a ha (x.toAdd i)).mpr
    exact congrArg (fun z : StandardHomocyclicCover κ p => z.toAdd i) hx

theorem powerMap_surjective : Function.Surjective (powerMap κ p a ha) := by
  intro x
  have hx : (x : StandardHomocyclicCover κ (p^a)) ^ p = 1 := by
    have h : x.val ∈ (powMonoidHom (p^1) :
        StandardHomocyclicCover κ (p^a) →* _).ker :=
      (OmegaAction.omega_eq_pow_ker (G := StandardHomocyclicCover κ (p^a)) p 1) ▸ x.property
    simpa only [MonoidHom.mem_ker, powMonoidHom_apply, pow_one] using h
  have hcoord : ∀ i : κ, ∃ y : ZMod (p^a), (p^(a-1) : ℕ) • y = x.val.toAdd i := by
    intro i
    apply coord_surj p a ha
    exact congrArg (fun z : StandardHomocyclicCover κ (p^a) => z.toAdd i) hx
  choose y hy using hcoord
  refine ⟨Multiplicative.ofAdd y, ?_⟩
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext i
  exact hy i

noncomputable def standardEquiv [Fintype κ] :
    (StandardHomocyclicCover κ (p^a) ⧸ frattini (StandardHomocyclicCover κ (p^a))) ≃*
      omega (StandardHomocyclicCover κ (p^a)) (p := p) 1 :=
  (QuotientGroup.quotientMulEquivOfEq (powerMap_ker κ p a ha).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (powerMap κ p a ha)
      (powerMap_surjective κ p a ha))

theorem standardEquiv_apply_mk [Fintype κ] (x : StandardHomocyclicCover κ (p^a)) :
    (standardEquiv κ p a ha (QuotientGroup.mk' _ x) : StandardHomocyclicCover κ (p^a)) =
      x ^ (p^(a-1)) := rfl

variable {κ p a}

noncomputable def equiv {Q : Type*} [Group Q] [Fintype κ]
    (e : Q ≃* StandardHomocyclicCover κ (p^a)) :
    (Q ⧸ frattini Q) ≃* omega Q (p := p) 1 :=
  (QuotientGroup.congr _ _ e (frattini_map_equiv e)).trans
    ((standardEquiv κ p a ha).trans
      ((e.symm.subgroupMap (omega (StandardHomocyclicCover κ (p^a)) (p := p) 1)).trans
        (MulEquiv.subgroupCongr (e.symm.map_omega p 1))))

theorem equiv_apply_mk {Q : Type*} [Group Q] [Fintype κ]
    (e : Q ≃* StandardHomocyclicCover κ (p^a)) (x : Q) :
    (equiv ha e (QuotientGroup.mk' _ x) : Q) = x ^ (p^(a-1)) := by
  change e.symm ((standardEquiv κ p a ha (QuotientGroup.mk' _ (e x))) :
    StandardHomocyclicCover κ (p^a)) = _
  rw [standardEquiv_apply_mk, map_pow, e.symm_apply_apply]

theorem equiv_equivariant {Q : Type*} [Group Q] [Fintype κ]
    (e : Q ≃* StandardHomocyclicCover κ (p^a)) (α : MulAut Q) (z : Q ⧸ frattini Q) :
    equiv ha e (quotientAut (frattini Q) α z) =
      OmegaAction.omegaRestriction Q p 1 α (equiv ha e z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) z
  apply Subtype.ext
  rw [quotientAut_apply_mk, equiv_apply_mk]
  change (α x) ^ (p^(a-1)) = α (equiv ha e (QuotientGroup.mk' _ x) : Q)
  rw [equiv_apply_mk, map_pow]

/-- The homocyclic power bridge followed by the elementary omega quotient. -/
noncomputable def quotientEquiv {Q : Type*} [Group Q] [Finite Q] [Fintype κ]
    (e : Q ≃* StandardHomocyclicCover κ (p^a)) :
    (Q ⧸ frattini Q) ≃* (omega Q (p := p) 1 ⧸ frattini (omega Q (p := p) 1)) := by
  let : IsMulCommutative Q := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  let : IsElementaryAbelian p (omega Q (p := p) 1) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative Q
  let : Fact (IsPGroup p (omega Q (p := p) 1)) := ⟨IsElementaryAbelian.isPGroup _ _⟩
  exact (equiv ha e).trans (frattiniQuotientEquivOfIsElementaryAbelian (p := p)).symm

theorem quotientEquiv_apply {Q : Type*} [Group Q] [Finite Q] [Fintype κ]
    (e : Q ≃* StandardHomocyclicCover κ (p^a)) (z : Q ⧸ frattini Q) :
    quotientEquiv ha e z = QuotientGroup.mk' _ (equiv ha e z) := rfl

theorem quotientEquiv_equivariant {Q : Type*} [Group Q] [Finite Q] [Fintype κ]
    (e : Q ≃* StandardHomocyclicCover κ (p^a)) (α : MulAut Q) (z : Q ⧸ frattini Q) :
    quotientEquiv ha e (quotientAut (frattini Q) α z) =
      quotientAut (frattini (omega Q (p := p) 1))
        (OmegaAction.omegaRestriction Q p 1 α) (quotientEquiv ha e z) := by
  simp only [quotientEquiv_apply, quotientAut_apply_mk, equiv_equivariant]

section Exponent
variable {Q : Type*} [Group Q]

/-- For exponent p, inclusion of omega in Q is an isomorphism. -/
def exponentOmegaEquiv (p : ℕ) (hp : ∀ x : Q, x ^ p = 1) : Q ≃* omega Q (p := p) 1 where
  toFun x := ⟨x, subset_closure (by simpa only [Set.mem_ofPred_eq, pow_one] using hp x)⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Exponent-p groups have the same actual Frattini quotient as their omega. -/
noncomputable def exponentQuotientEquiv (p : ℕ) (hp : ∀ x : Q, x ^ p = 1) :
    (Q ⧸ frattini Q) ≃* (omega Q (p := p) 1 ⧸ frattini (omega Q (p := p) 1)) :=
  QuotientGroup.congr _ _ (exponentOmegaEquiv p hp)
    (frattini_map_equiv (exponentOmegaEquiv p hp))

theorem exponentQuotientEquiv_equivariant (p : ℕ) (hp : ∀ x : Q, x ^ p = 1)
    (α : MulAut Q) (z : Q ⧸ frattini Q) :
    exponentQuotientEquiv p hp (quotientAut (frattini Q) α z) =
      quotientAut (frattini (omega Q (p := p) 1))
        (OmegaAction.omegaRestriction Q p 1 α) (exponentQuotientEquiv p hp z) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) z
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' _ (exponentOmegaEquiv p hp (α x)) =
    quotientAut _ _ (QuotientGroup.mk' _ (exponentOmegaEquiv p hp x))
  rw [quotientAut_apply_mk]
  rfl
end Exponent

end HomocyclicOmegaFrattini
