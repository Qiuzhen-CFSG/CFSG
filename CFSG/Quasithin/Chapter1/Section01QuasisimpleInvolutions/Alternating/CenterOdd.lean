module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Six
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Seven
public import Theory.GroupTheory.CoveringComparisonKernelCard
public import Mathlib.Algebra.Group.TransferInstance

/-!
# Odd centers in the exceptional alternating branches of 1.1.5

The multiplier bounds the center by six. The original quotient action is
permutation induced: the Sylow-fixing restriction proves this for A₆, and
the characteristic-two fixed-group restriction proves it for A₇.

An even center has order two or six. In the first case, uniqueness identifies
the original action with Schur's double-cover lift. Its fixed image has index
two, contradicting fixed-point surjectivity for the original fixed Sylow.
In the second case, Cauchy's theorem constructs a central subgroup of order
three. Odd-core inversion makes it invariant, so quotienting gives the same
contradiction for the descended action and the actual Sylow image. The kernel
order is computed from the commuting covering triangle. Finite-universe
transport follows the double-cover argument in the even-family BinaryFour
module, retaining the literal maps and actions.

This discharges the odd-center premises in the A₆/A₇ simple-or-triple
classification, without assuming an involutory group representative upstairs.
Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--503; GLS3, Theorem
5.2.3 and Proposition 5.2.8(b).
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open GLS3.Chapter5 GLS3.Chapter5.SchurPresentation
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating

private theorem doubleCover_no_fixed_sylow_small
    {G : Type} [Group G] [Finite G] [IsQuasisimple G]
    (n : ℕ) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (a : MulAut G) (ha : a ^ 2 = 1) (P : Sylow 2 G)
    (hP : ∀ x ∈ P, a x = x)
    (σ : Equiv.Perm (Fin (n + 5))) (hσ : orderOf σ = 2)
    (heq : ∀ x, f (a x) =
      MulAut.conjNormal (H := alternatingGroup (Fin (n + 5))) σ (f x)) : False := by
  let b : MulAut (alternatingGroup (Fin (n + 5))) := MulAut.conjNormal σ
  have hfac : f.comp (Covering.ofMulEquiv a) =
      (Covering.ofMulEquiv b).comp f := by
    apply Covering.ext
    exact heq
  have hlift : a = doubleCoverLiftMulAut n f hcard b :=
    doubleCoverLiftMulAut_unique n f hcard b hfac
  have hsurj := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed
    a b f.toMonoidHom f.surjective f.ker_le_center heq ha P hP
  have hmap : (automorphismFixedSubgroup a).map f.toMonoidHom =
      automorphismFixedSubgroup b := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      change b (f x) = f x
      rw [← heq x]
      change a x = x at hx
      rw [hx]
    · intro y hy
      have hy' : y ∈ b.fixedSubgroup := by
        rw [MulAut.mem_fixedSubgroup]
        exact hy
      obtain ⟨x, hx⟩ := hsurj ⟨y, hy'⟩
      refine ⟨x, ?_, congrArg Subtype.val hx⟩
      change a x = x
      exact (MulAut.mem_fixedSubgroup _ _).mp x.property
  obtain ⟨_, hindex, _⟩ := proposition_5_2_8_b n f hcard σ hσ
  change (((automorphismFixedSubgroup (doubleCoverLiftMulAut n f hcard b)).map
    f.toMonoidHom).subgroupOf (automorphismFixedSubgroup b)).index = 2 at hindex
  rw [← hlift, hmap, subgroupOf_self, index_top] at hindex
  omega

private theorem doubleCover_no_fixed_sylow
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (n : ℕ) (f : Covering G (alternatingGroup (Fin (n + 5))))
    (hcard : Nat.card f.toMonoidHom.ker = 2)
    (a : MulAut G) (ha : a ^ 2 = 1) (P : Sylow 2 G)
    (hP : ∀ x ∈ P, a x = x)
    (σ : Equiv.Perm (Fin (n + 5))) (hσ : orderOf σ = 2)
    (heq : ∀ x, f (a x) =
      MulAut.conjNormal (H := alternatingGroup (Fin (n + 5))) σ (f x)) : False := by
  obtain ⟨E, iE, finE, ⟨s⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} G
  let := iE
  let := finE
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv s
  let fE := f.comp (Covering.ofMulEquiv s.symm)
  have hcardE : Nat.card fE.toMonoidHom.ker = 2 := by
    rw [← hcard]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨s.symm x, x.property⟩
      invFun := fun x => ⟨s x, by
        change f (s.symm (s x)) = 1
        rw [s.symm_apply_apply]
        exact x.property⟩
      left_inv := fun x => Subtype.ext (s.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (s.symm_apply_apply x) }
  let aE := MulAut.congr s a
  let PE := P.mapSurjective (f := s.toMonoidHom) s.surjective
  have haE : aE ^ 2 = 1 := by
    change (MulAut.congr s a) ^ 2 = 1
    rw [← map_pow, ha, map_one]
  have hPE : ∀ x ∈ PE, aE x = x := by
    rintro x ⟨y, hy, rfl⟩
    change s (a (s.symm (s y))) = s y
    rw [s.symm_apply_apply, hP y hy]
  apply doubleCover_no_fixed_sylow_small n fE hcardE aE haE PE hPE σ hσ
  intro x
  change f (s.symm (s (a (s.symm x)))) =
    MulAut.conjNormal (H := alternatingGroup (Fin (n + 5))) σ (f (s.symm x))
  rw [s.symm_apply_apply]
  exact heq (s.symm x)


variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {α : MulAut L} {P : Sylow 2 L}

private theorem exceptional_permutation_action (d : MarkedInvolution α P) {n : ℕ}
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) (hn : n = 6 ∨ n = 7) :
    ∃ σ : Equiv.Perm (Fin n), orderOf σ = 2 ∧
      MulAut.centralQuotientAction e α = MulAut.conjNormal σ := by
  obtain ⟨ho, hc, Q, hQ⟩ := d.centralQuotient_model_inputs e
  rcases hn with rfl | rfl
  · obtain ⟨σ, hσ⟩ :=
      AlternatingSix.ShadowLocal.involution_mem_natural_of_fixes_sylow Q _ ho hQ
    change MulAut.conjNormal σ = MulAut.centralQuotientAction e α at hσ
    refine ⟨σ, ?_, hσ.symm⟩
    exact (orderOf_injective _
      (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by decide))
      σ).symm.trans (hσ ▸ ho)
  · obtain ⟨σ, _, hσ⟩ := seven_fixed_action _ ho hc
    refine ⟨σ, ?_, hσ⟩
    exact (orderOf_injective _
      (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by decide))
      σ).symm.trans (hσ ▸ ho)

private theorem center_order_six_impossible (d : MarkedInvolution α P) (n : ℕ)
    (f : Covering L (alternatingGroup (Fin (n + 5))))
    (hk : f.toMonoidHom.ker = center L)
    (hc : Nat.card (center L) = 6)
    (σ : Equiv.Perm (Fin (n + 5))) (hσ : orderOf σ = 2)
    (heq : ∀ x, f (α x) = MulAut.conjNormal σ (f x)) : False := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center L) 3
    (by rw [hc]; decide)
  let N : Subgroup L := (zpowers z).map (center L).subtype
  have hNZ : N ≤ center L := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hNn : N.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hNZ hx) g, mul_inv_cancel_right]
    exact hx⟩
  let : N.Normal := hNn
  have hNcard : Nat.card N = 3 := by
    rw [show Nat.card N = Nat.card (zpowers z) from
      Subgroup.card_map_of_injective (center L).subtype_injective,
      Nat.card_zpowers, hz]
  have hNO : N ≤ pPrimeCore 2 L := le_sSup ⟨hNn, by rw [hNcard]; decide⟩
  have hmap : N.map α.toMonoidHom = N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change α y ∈ N
      rw [d.inverts_odd_core y (hNO hy)]
      exact N.inv_mem hy
    · intro hx
      refine ⟨x⁻¹, N.inv_mem hx, ?_⟩
      change α x⁻¹ = x
      rw [d.inverts_odd_core _ (hNO (N.inv_mem hx)), inv_inv]
  let q := QuotientGroup.mk' N
  let β : MulAut (L ⧸ N) := QuotientGroup.congr N N α hmap
  have hβq (x : L) : β (q x) = q (α x) := rfl
  let fbar : L ⧸ N →* alternatingGroup (Fin (n + 5)) :=
    QuotientGroup.lift N f.toMonoidHom (hNZ.trans hk.ge)
  have hfbar : Function.Surjective fbar := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨q x, rfl⟩
  let : Nontrivial (L ⧸ N) := hfbar.nontrivial
  let : IsQuasisimple (L ⧸ N) := IsQuasisimple.of_surjective q
    (QuotientGroup.mk'_surjective N)
  let c : Covering (L ⧸ N) (alternatingGroup (Fin (n + 5))) :=
    { toMonoidHom := fbar, surjective := hfbar }
  have hcard : Nat.card c.toMonoidHom.ker = 2 := by
    have hh := kernel_card_eq_mul_of_surjective_factor f.toMonoidHom
      fbar q hfbar (QuotientGroup.mk'_surjective N) (by ext x; rfl)
    rw [hk, hc, QuotientGroup.ker_mk', hNcard] at hh
    change 6 = 3 * Nat.card c.toMonoidHom.ker at hh
    omega
  have hβ : β ^ 2 = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    change β (β (q y)) = q y
    rw [hβq, hβq]
    have ha : α (α y) = y := by
      have hh := congrArg (fun a : MulAut L => a y)
        (d.order_two ▸ pow_orderOf_eq_one α)
      simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
    rw [ha]
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hQ : ∀ x ∈ Q, β x = x := by
    rintro x ⟨y, hy, rfl⟩
    rw [hβq, d.fixes y hy]
  apply doubleCover_no_fixed_sylow n c hcard β hβ Q hQ σ hσ
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  exact heq y

/-- A marked involution over an actual A₆ or A₇ central quotient forces
odd center order. All quotient actions and Sylow subgroups are constructed
from the original marking; no cover-recognition premise remains. -/
theorem center_odd_of_exceptional_quotient (d : MarkedInvolution α P) {n : ℕ}
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) (hn : n = 6 ∨ n = 7) :
    Odd (Nat.card (center L)) := by
  have hd := exceptional_alternating_center_card_dvd_six n e hn
  obtain ⟨σ, hσ, ha⟩ := exceptional_permutation_action d e hn
  have hn5 : 5 ≤ n := by omega
  obtain ⟨k, hkdegree⟩ := Nat.exists_eq_add_of_le hn5
  have hnEq : n = k + 5 := hkdegree.trans (Nat.add_comm 5 k)
  clear hkdegree
  subst n
  let f : Covering L (alternatingGroup (Fin (k + 5))) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hk : f.toMonoidHom.ker = center L := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ center L
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have heq (x : L) : f (α x) = MulAut.conjNormal σ (f x) := by
    rw [← ha]
    exact (MulAut.centralQuotientAction_apply e α x).symm
  have h23 : Nat.card (center L) = 1 ∨ Nat.card (center L) = 2 ∨
      Nat.card (center L) = 3 ∨ Nat.card (center L) = 6 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
    have hp : 0 < Nat.card (center L) := Nat.card_pos
    interval_cases h : Nat.card (center L) <;> norm_num at *
  rcases h23 with h | h | h | h
  · rw [h]; decide
  · have hcard : Nat.card f.toMonoidHom.ker = 2 := hk ▸ h
    exact (doubleCover_no_fixed_sylow k f hcard α
      (d.order_two ▸ pow_orderOf_eq_one α) P d.fixes σ hσ heq).elim
  · rw [h]; decide
  · exact (center_order_six_impossible d k f hk h σ hσ heq).elim

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
