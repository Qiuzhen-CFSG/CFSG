module

public import CFSG.Quasithin.ChapterA.Section01.PStructure
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.SpecificGroups.HeisenbergPrime.InversionFixedPlane
public import Theory.SpecificGroups.HeisenbergPrime.ElementaryPlane
public import Theory.SpecificGroups.HeisenbergPrime.SL2ExtensionAction
public import Theory.SpecificGroups.HeisenbergPrime.SL23InvolutionAction
public import Theory.SpecificGroups.SL2.PrimeCentralExtension
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizerSupplement

/-!
# Odd-prime rank witnesses for extraspecial extensions

This module proves all three clauses of Lemma A.1.33. An element x of order p
centralizing an inverter t has a fixed line on P/Z(P). The Heisenberg model
calculation identifies its full preimage with C_P(x), an elementary abelian
plane. Nontrivial action on the quotient forces x outside P, so adjoining
x gives an elementary abelian subgroup of order p³.

The conjugation action is the literal action on P/Z(P), and P is supplied
with an actual isomorphism to the prime Heisenberg group. The inverter t
is not assumed to have order two.

For clause (2), the quotient action is either trivial or faithful modulo P.
In the trivial case C_L(P) covers L/P; in the faithful case an involution
inverting P/Z(P) has a centralizer covering L/P. In each case the central
p-kernel splits by transfer and cyclicity of the quotient's Sylow
p-subgroups, giving an actual order-p element outside P.

For clause (3), the involution's nontrivial action on P implies inversion
on P/Z(P). The ambient center has order three and contains every element
of C_L(t) acting trivially on P/Z(P). Thus the source subgroup X of order
three with X ≠ Z(L) supplies the nontrivial actor required by clause (1).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma A.1.33, printed p.29.
-/

namespace CFSG.Quasithin.ChapterA.RankActions

open Subgroup
open scoped IsMulCommutative

variable {L : Type*} [Group L] [Finite L]
variable {p : ℕ} [Fact p.Prime]

/-- The elementary rank-three calculation at the end of the fixed-line
argument.  In the source, `E` is the preimage of the fixed line in
`P/Z(P)`, after the inversion identity identifies that preimage with
`C_P(x)`. Keeping centralization of the actual subgroup explicit prevents
using a quotient fixed subgroup as though it were a subgroup of `P`. -/
public theorem primeRank_gt_two_of_extraspecial_fixed_plane
    (_P E : Subgroup L) (x : L)
    [IsElementaryAbelian p E]
    (hEcard : Nat.card E = p ^ 2)
    (hx : orderOf x = p) (hxE : x ∉ E)
    (hcentral : E ≤ centralizer ({x} : Set L)) :
    3 ≤ primeRank p L := by
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join E x hx hxE hcentral hEcard

/-- Construct the actual elementary abelian plane in C_P(x) from the
literal quotient conjugation action and the source inversion hypothesis. -/
public theorem exists_extraspecial_fixed_plane_of_inverter
    (P : Subgroup L) [P.Normal] (e : P ≃* HeisenbergPrime p) (hp : p ≠ 2)
    (t x : L)
    (ht : ∀ v : P ⧸ center P,
      quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹)
    (hx : orderOf x = p) (hxt : x ∈ centralizer ({t} : Set L))
    (hxV : quotientAut (center P) (MulAut.conjNormal x) ≠ 1) :
    ∃ E : Subgroup L, E ≤ P ∧ E ≤ centralizer ({x} : Set L) ∧
      IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  have ha : (MulAut.conjNormal x : MulAut P) ^ p = 1 := by
    rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have hat : Commute (MulAut.conjNormal x : MulAut P) (MulAut.conjNormal t) :=
    (show Commute x t from mem_centralizer_singleton_iff.mp hxt).map MulAut.conjNormal
  let F := (quotientAut (center P) (MulAut.conjNormal x)).fixedSubgroup.comap
    (QuotientGroup.mk' (center P))
  obtain ⟨hF, hcard, hfix⟩ := HeisenbergPrime.InversionFixedPlane.fixed_plane e hp
    (MulAut.conjNormal x) (MulAut.conjNormal t) ha hat ht hxV
  let : IsElementaryAbelian p F := hF
  refine ⟨F.map P.subtype, map_subtype_le F, ?_,
    IsElementaryAbelian.map_subtype, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    have hzfix : MulAut.conjNormal x z = z :=
      (MulAut.mem_fixedSubgroup _ _).mp (hfix ▸ hz)
    have hh := congrArg Subtype.val hzfix
    rw [MulAut.conjNormal_apply] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  · exact (Nat.card_congr (F.equivMapOfInjective P.subtype P.subtype_injective).toEquiv).symm.trans hcard

/-- The fixed plane and the independent element x of order p give the
rank-three obstruction in A.1.33(1). -/
public theorem primeRank_gt_two_of_extraspecial_inverter
    (P : Subgroup L) [P.Normal] (e : P ≃* HeisenbergPrime p) (hp : p ≠ 2)
    (t x : L)
    (ht : ∀ v : P ⧸ center P,
      quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹)
    (hx : orderOf x = p) (hxt : x ∈ centralizer ({t} : Set L))
    (hxV : quotientAut (center P) (MulAut.conjNormal x) ≠ 1) :
    3 ≤ primeRank p L := by
  obtain ⟨E, hEP, hcentral, hE, hcard⟩ :=
    exists_extraspecial_fixed_plane_of_inverter P e hp t x ht hx hxt hxV
  let : IsElementaryAbelian p E := hE
  have hxP : x ∉ P := by
    intro hxP
    apply hxV
    let : IsExtraspecial p P := (HeisenbergPrime.isExtraspecial hp).of_mulEquiv e.symm
    let : IsElementaryAbelian p (P ⧸ center P) :=
      IsExtraspecial.quotient_elementary_abelian p P
    let y : P := ⟨x, hxP⟩
    have hconj : (MulAut.conjNormal x : MulAut P) = MulAut.conj y :=
      MulAut.conjNormal_val (h := y)
    ext v
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center P) v
    rw [quotientAut_apply_mk, hconj, MulAut.conj_apply, map_mul, map_mul, map_inv]
    change _ = QuotientGroup.mk' (center P) z
    rw [mul_comm (QuotientGroup.mk' (center P) y), mul_assoc, mul_inv_cancel, mul_one]
  exact primeRank_gt_two_of_extraspecial_fixed_plane P E x hcard hx
    (fun hxE => hxP (hEP hxE)) hcentral

/-- A.1.33(1), with exactly the source inverter and nontrivial quotient-action
hypotheses. No order condition is imposed on the inverter. -/
public theorem source_lemma_A_1_33_1
    (P : Subgroup L) [P.Normal] (hP : Nonempty (P ≃* HeisenbergPrime p)) (hp : p ≠ 2)
    (h : ∃ t : L,
      (∀ v : P ⧸ center P, quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹) ∧
      ∃ x ∈ centralizer ({t} : Set L), orderOf x = p ∧
        quotientAut (center P) (MulAut.conjNormal x) ≠ 1) :
    2 < primeRank p L := by
  obtain ⟨e⟩ := hP
  obtain ⟨t, ht, x, hxt, hx, hxV⟩ := h
  exact primeRank_gt_two_of_extraspecial_inverter P e hp t x ht hx hxt hxV

/-- An independent element of order p centralizing P joins an elementary
plane in P to give the centralizing branch of A.1.33(2). -/
public theorem primeRank_gt_two_of_extraspecial_centralizing_actor
    (P : Subgroup L) (e : P ≃* HeisenbergPrime p)
    (hp : p ≠ 2) (x : L) (hx : orderOf x = p) (hxP : x ∉ P)
    (hcentral : x ∈ centralizer (P : Set L)) : 2 < primeRank p L := by
  obtain ⟨E, hE, hc⟩ := HeisenbergPrime.exists_elementary_plane hp
  let : IsElementaryAbelian p E := hE
  let f := P.subtype.comp e.symm.toMonoidHom
  let A := E.map f
  have hf : Function.Injective f := P.subtype_injective.comp e.symm.injective
  let : IsElementaryAbelian p A := IsElementaryAbelian.map f
  have hAc : Nat.card A = p ^ 2 :=
    (Nat.card_congr (E.equivMapOfInjective f hf).toEquiv).symm.trans hc
  have hAP : A ≤ P := by
    rintro y ⟨z, hz, rfl⟩
    exact (e.symm z).property
  exact primeRank_gt_two_of_extraspecial_fixed_plane P A x hAc hx
    (fun ha => hxP (hAP ha)) (by
      intro y hy
      exact mem_centralizer_singleton_iff.mpr (hcentral y (hAP hy)))

/-- The centralizing case of A.1.33(2), using an actual centralizer
supplement. Its central p-kernel splits by the transfer theorem. -/
public theorem primeRank_gt_two_of_extraspecial_sl2_centralizer_surjective
    (P : Subgroup L) [P.Normal]
    (e : P ≃* HeisenbergPrime p) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hC : Function.Surjective ((QuotientGroup.mk' P).comp
      (centralizer (P : Set L)).subtype)) : 2 < primeRank p L := by
  let : IsExtraspecial p P :=
    (HeisenbergPrime.isExtraspecial (by omega : p ≠ 2)).of_mulEquiv e.symm
  obtain ⟨x, hxC, hx, hxP⟩ :=
    Matrix.SpecialLinearGroup.exists_prime_order_outside_normal_subgroup
      P (IsExtraspecial.isPGroup p P) hp eQ (centralizer (P : Set L)) hC (by
      intro y hy
      apply mem_center_iff.mpr
      intro z
      exact Subtype.ext (z.property y hy).symm)
  exact primeRank_gt_two_of_extraspecial_centralizing_actor P e (by omega) x hx hxP hxC

/-- The trivial action on P/Z(P) case of A.1.33(2), with the
centralizer supplement and central extension splitting both discharged. -/
public theorem primeRank_gt_two_of_extraspecial_sl2_trivial_action
    (P : Subgroup L) [P.Normal]
    (e : P ≃* HeisenbergPrime p) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (htriv : ∀ x : L, quotientAut (center P) (MulAut.conjNormal x) = 1) :
    2 < primeRank p L := by
  let : IsExtraspecial p P :=
    (HeisenbergPrime.isExtraspecial (by omega : p ≠ 2)).of_mulEquiv e.symm
  exact primeRank_gt_two_of_extraspecial_sl2_centralizer_surjective P e hp eQ
    (IsExtraspecial.centralizer_projection_surjective_of_trivial_quotient_action (p := p) P htriv)

/-- The faithful case of A.1.33(2), conditional on the involution
centralizer geometry. The actual central p-extension is split here, and
the lifted order-p actor is used in the proved clause (1). -/
public theorem primeRank_gt_two_of_extraspecial_sl2_faithful_action
    (P : Subgroup L) [P.Normal]
    (e : P ≃* HeisenbergPrime p) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (t : L)
    (ht : ∀ v : P ⧸ center P,
      quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹)
    (hC : Function.Surjective ((QuotientGroup.mk' P).comp
      (centralizer ({t} : Set L)).subtype))
    (hcentral : ∀ x : centralizer ({t} : Set L), (x : L) ∈ P →
      x ∈ center (centralizer ({t} : Set L)))
    (hfaith : ∀ x : L, x ∉ P → quotientAut (center P) (MulAut.conjNormal x) ≠ 1) :
    2 < primeRank p L := by
  let : IsExtraspecial p P :=
    (HeisenbergPrime.isExtraspecial (by omega : p ≠ 2)).of_mulEquiv e.symm
  obtain ⟨x, hxt, hx, hxP⟩ :=
    Matrix.SpecialLinearGroup.exists_prime_order_outside_normal_subgroup
      P (IsExtraspecial.isPGroup p P) hp eQ (centralizer ({t} : Set L)) hC hcentral
  exact primeRank_gt_two_of_extraspecial_inverter P e (by omega) t x ht hx hxt
    (hfaith x hxP)

/-- Both quotient-action branches of A.1.33(2), with the faithful action,
inverter, centralizer supplement and central extension splitting derived
from the concrete Heisenberg and SL₂ identifications. -/
public theorem primeRank_gt_two_of_extraspecial_sl2
    (P : Subgroup L) [P.Normal]
    (e : P ≃* HeisenbergPrime p) (hp : 3 < p)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    2 < primeRank p L := by
  classical
  by_cases htriv : ∀ x : L, quotientAut (center P) (MulAut.conjNormal x) = 1
  · exact primeRank_gt_two_of_extraspecial_sl2_trivial_action P e hp eQ htriv
  · have hne : ∃ x : L, quotientAut (center P) (MulAut.conjNormal x) ≠ 1 :=
      not_forall.mp htriv
    obtain ⟨t, _ht, hinv, hC, hcentral, hfaith⟩ :=
      HeisenbergPrime.SL2ExtensionAction.exists_involution_centralizer P e hp eQ hne
    exact primeRank_gt_two_of_extraspecial_sl2_faithful_action P e hp eQ t
      hinv hC hcentral hfaith

/-- A.1.33(2): every extension of the prime Heisenberg group by SL₂(p),
with p > 3, has p-rank greater than two. -/
public theorem source_lemma_A_1_33_2
    (P : Subgroup L) [P.Normal] (hP : Nonempty (P ≃* HeisenbergPrime p)) (hp : 3 < p)
    (hQ : Nonempty (L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) :
    2 < primeRank p L := by
  obtain ⟨e⟩ := hP
  obtain ⟨eQ⟩ := hQ
  exact primeRank_gt_two_of_extraspecial_sl2 P e hp eQ

/-- The order-three subgroup step of A.1.33(3). The exact distinction
from Z(L) forces a nontrivial quotient actor once the inverter and
centralizer-action kernel have been identified. Those action facts remain
explicit premises, not consequences asserted from the source here. -/
public theorem primeRank_gt_two_of_extraspecial_three_centralizer_action
    (P : Subgroup L) [P.Normal]
    (e : P ≃* HeisenbergPrime 3) (t : L) (X : Subgroup L)
    (hX : Nat.card X = 3) (hXZ : X ≠ center L)
    (hXt : X ≤ centralizer ({t} : Set L))
    (ht : ∀ v : P ⧸ center P,
      quotientAut (center P) (MulAut.conjNormal t) v = v⁻¹)
    (hZ : Nat.card (center L) = 3)
    (hkernel : ∀ x ∈ centralizer ({t} : Set L),
      quotientAut (center P) (MulAut.conjNormal x) = 1 → x ∈ center L) :
    2 < primeRank 3 L := by
  classical
  have hex : ∃ x ∈ X, quotientAut (center P) (MulAut.conjNormal x) ≠ 1 := by
    by_contra h
    push Not at h
    exact hXZ (eq_of_le_of_card_ge (fun x hx => hkernel x (hXt hx) (h x hx))
      (by omega))
  obtain ⟨x, hxX, hxV⟩ := hex
  have hxne : x ≠ 1 := by
    rintro rfl
    exact hxV (by rw [map_one, map_one])
  have hd : orderOf x ∣ 3 := by
    rw [← hX, Subgroup.orderOf_coe (⟨x, hxX⟩ : X)]
    exact orderOf_dvd_natCard _
  have hx : orderOf x = 3 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
    · exact (hxne (orderOf_eq_one_iff.mp h)).elim
    · exact h
  exact primeRank_gt_two_of_extraspecial_inverter P e (by decide) t x ht hx (hXt hxX) hxV

/-- The involution and subgroup configuration of A.1.33(3) forces
three-rank greater than two. Nontriviality is assumed only on P; inversion
on P/Z(P) and the ambient center calculation are consequences. -/
public theorem primeRank_gt_two_of_extraspecial_three_involution
    (P : Subgroup L) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (eQ : L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (t : L) (ht : orderOf t = 2) (hne : (MulAut.conjNormal t : MulAut P) ≠ 1)
    (X : Subgroup L) (hX : Nat.card X = 3) (hXZ : X ≠ center L)
    (hXt : X ≤ centralizer ({t} : Set L)) : 2 < primeRank 3 L := by
  obtain ⟨hinv, hZ, hkernel⟩ :=
    HeisenbergPrime.SL23InvolutionAction.involution_action_and_center P e eQ t ht hne
  exact primeRank_gt_two_of_extraspecial_three_centralizer_action
    P e t X hX hXZ hXt hinv hZ hkernel

/-- A.1.33(3), retaining both the source action on P and the literal
inequality of the centralized order-three subgroup with Z(L). -/
public theorem source_lemma_A_1_33_3
    (P : Subgroup L) [P.Normal] (hP : Nonempty (P ≃* HeisenbergPrime p)) (hp : p = 3)
    (hQ : Nonempty (L ⧸ P ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (h : ∃ t : L, orderOf t = 2 ∧ (MulAut.conjNormal t : MulAut P) ≠ 1 ∧
      ∃ X : Subgroup L, Nat.card X = 3 ∧ X ≠ center L ∧
        X ≤ centralizer ({t} : Set L)) : 2 < primeRank p L := by
  subst p
  obtain ⟨e⟩ := hP
  obtain ⟨eQ⟩ := hQ
  obtain ⟨t, ht, hne, X, hX, hXZ, hXt⟩ := h
  exact primeRank_gt_two_of_extraspecial_three_involution P e eQ t ht hne X hX hXZ hXt

end CFSG.Quasithin.ChapterA.RankActions
