module

import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.CommutingProbability
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public import Theory.Alternating.theorem_5_2_3
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option Elab.async false

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN KGroup.GLS3.Chapter5.proposition_5_2_6 -/
set_option maxHeartbeats 800000

noncomputable section

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5

open scoped commutatorElement
open SchurPresentation

/-- Membership in the alternating quasisimple family.  Quasisimplicity is a
separate typeclass assumption in the propositions below, so this predicate
records exactly the central-quotient condition denoted by `K ∈ Alt`. -/
public def IsInAlt (K : Type*) [Group K] [Finite K] : Prop :=
  ∃ n : Nat, 5 ≤ n ∧
    Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))

/-- The printed choice `Z = Z(K)` and `K / Z ≃ A_n` is precisely the
existential content of `K ∈ Alt`. -/
public theorem isInAlt_iff_exists_center_quotient
    {K : Type*} [Group K] [Finite K] :
    IsInAlt K ↔
      ∃ (n : Nat) (Z : Subgroup K),
        5 ≤ n ∧ Z = Subgroup.center K ∧
          Nonempty (K ⧸ Subgroup.center K ≃*
            alternatingGroup (Fin n)) := by
  constructor
  · rintro ⟨n, hn, quotientEquiv⟩
    exact ⟨n, Subgroup.center K, hn, rfl, quotientEquiv⟩
  · rintro ⟨n, Z, hn, rfl, quotientEquiv⟩
    exact ⟨n, hn, quotientEquiv⟩

/-- The quotient map associated to a chosen witness for `K ∈ Alt`. -/
@[expose] public def alternatingQuotientHom
    {K : Type*} [Group K] [Finite K] {n : Nat}
    (quotientEquiv : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    K →* alternatingGroup (Fin n) :=
  quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))

/-- Two permutation subgroups have disjoint supports elementwise. -/
public def HaveDisjointPermutationSupports {n : Nat}
    (A B : Subgroup (alternatingGroup (Fin n))) : Prop :=
  ∀ a : A, ∀ b : B,
    Disjoint a.1.1.support b.1.1.support

public theorem alternatingQuotientHom_surjective
    {K : Type*} [Group K] [Finite K] {n : Nat}
    (quotientEquiv : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    Function.Surjective (alternatingQuotientHom quotientEquiv) := by
  exact quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (Subgroup.center K))

public theorem alternatingQuotientHom_ker
    {K : Type*} [Group K] [Finite K] {n : Nat}
    (quotientEquiv : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    (alternatingQuotientHom quotientEquiv).ker = Subgroup.center K := by
  ext k
  simp [alternatingQuotientHom]

private theorem __ch5_proposition_5_2_6_exists_order_prime_lift_of_coprime_kernel
    {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    (p : Nat) (hp : p.Prime)
    (f : H →* G) (hf : Function.Surjective f)
    (hcop : Nat.Coprime (Nat.card f.ker) p)
    (a : G) (ha : orderOf a = p) :
    ∃ y : H, f y = a ∧ orderOf y = p := by
  let C : Subgroup G := Subgroup.zpowers a
  let E : Subgroup H := C.comap f
  let r : E →* C :=
    (f.comp E.subtype).codRestrict C (by intro x; exact x.2)
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨x, hx⟩ := hf (z : G)
    have hxC : f x ∈ C := by rw [hx]; exact z.2
    refine ⟨⟨x, hxC⟩, ?_⟩
    apply Subtype.ext
    exact hx
  let N : Subgroup E := r.ker
  have hN : N = f.ker.comap E.subtype := by
    ext x
    change r x = 1 ↔ E.subtype x ∈ f.ker
    constructor
    · intro hx
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact MonoidHom.mem_ker.mp hx
  have hcardC : Nat.card C = p := by
    dsimp [C]
    rw [Nat.card_zpowers, ha]
  have hquot : E ⧸ N ≃* C :=
    QuotientGroup.quotientKerEquivOfSurjective r hr
  have hindex : N.index = p := by
    rw [Subgroup.index_eq_card]
    calc
      Nat.card (E ⧸ N) = Nat.card C := Nat.card_congr hquot.toEquiv
      _ = p := hcardC
  have hNcardDvd : Nat.card N ∣ Nat.card f.ker := by
    rw [hN]
    exact Subgroup.card_comap_dvd_of_injective
      f.ker E.subtype E.subtype_injective
  have hcopN : Nat.Coprime (Nat.card N) N.index := by
    rw [hindex]
    exact hcop.coprime_dvd_left hNcardDvd
  obtain ⟨S, hS⟩ := Subgroup.exists_right_complement'_of_coprime hcopN
  have hScard : Nat.card S = p := by
    rw [← hS.symm.index_eq_card, hindex]
  obtain ⟨x, hx⟩ := hf a
  let xE : E :=
    ⟨x, by
      have : f x ∈ C := by rw [hx]; exact Subgroup.mem_zpowers a
      exact this⟩
  have hrx : r xE = ⟨a, Subgroup.mem_zpowers a⟩ := by
    apply Subtype.ext
    exact hx
  have hcomp : Subgroup.IsComplement (N : Set E) (S : Set E) :=
    Subgroup.isComplement'_def.mp hS
  obtain ⟨ns, hss⟩ := hcomp.existsUnique xE
  let sS : S := ns.2
  let s : E := sS
  have hxs : (ns.1 : E) * s = xE := hss.1
  have hrs : r s = ⟨a, Subgroup.mem_zpowers a⟩ := by
    have hn1 : r ns.1 = 1 := MonoidHom.mem_ker.mp ns.1.2
    have h := congrArg r hxs
    rw [map_mul, hn1, one_mul, hrx] at h
    exact h
  have hfs : f (s : H) = a := congrArg Subtype.val hrs
  have hsne : (s : E) ≠ 1 := by
    intro hs1
    have h : f (s : H) = 1 := by rw [hs1]; simp
    rw [hfs] at h
    have ha_ne : a ≠ 1 := by
      intro ha1
      rw [ha1, orderOf_one] at ha
      exact hp.ne_one ha.symm
    exact ha_ne h
  have hdiv : orderOf sS ∣ Nat.card S := orderOf_dvd_natCard sS
  have horder : orderOf sS = p := by
    rw [hScard] at hdiv
    have hne : orderOf sS ≠ 1 := by
      intro h1
      exact hsne (by
        apply Subtype.ext
        simpa [s, Subgroup.orderOf_coe] using (orderOf_eq_one_iff.mp h1))
    exact ((Nat.dvd_prime hp).mp hdiv).resolve_left hne
  refine ⟨s, hfs, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact horder

private theorem __ch5_proposition_5_2_6_exists_order_three_lift_central_alternating
    {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (m : Nat) (hm : 5 ≤ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (a : alternatingGroup (Fin m)) (ha : orderOf a = 3) :
    ∃ y : H, f y = a ∧ orderOf y = 3 := by
  by_cases h3ker : 3 ∣ Nat.card f.ker
  · let K := f.ker
    let : CommGroup (Subgroup.center H) := {
      mul_comm := fun x y => Subtype.ext
        (Subgroup.mem_center_iff.mp x.2 y.1).symm }
    let j : K →* Subgroup.center H :=
      K.subtype.codRestrict (Subgroup.center H) (fun x => hker x.2)
    let : CommGroup K := j.commGroupOfInjective (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.center H => (z : H)) hxy)
    let P : Sylow 3 K := default
    let : (P : Subgroup K).Normal := inferInstance
    obtain ⟨C, hPC⟩ :=
      Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
    let X : Subgroup H := C.map K.subtype
    have hXker : X ≤ f.ker := by
      rintro x ⟨c, hc, rfl⟩
      exact c.2
    have hXcenter : X ≤ Subgroup.center H := hXker.trans hker
    let hXnormal : X.Normal := ⟨fun x hx b => by
      simpa [Subgroup.mem_center_iff.mp (hXcenter hx) b] using hx⟩
    let : X.Normal := hXnormal
    let q : H →* H ⧸ X := QuotientGroup.mk' X
    let fbar : (H ⧸ X) →* alternatingGroup (Fin m) :=
      QuotientGroup.lift X f hXker
    have hqker : q.ker.subgroupOf K = C := by
      rw [show q = QuotientGroup.mk' X by rfl, QuotientGroup.ker_mk']
      change Subgroup.comap K.subtype (C.map K.subtype) = C
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective C
    have hfbarCard : Nat.card fbar.ker = Nat.card P := by
      rw [show fbar = QuotientGroup.lift X f hXker by rfl,
        QuotientGroup.ker_lift]
      let r := q.subgroupMap K
      have hrker : r.ker = C := by
        rw [show r = q.subgroupMap K by rfl,
          Subgroup.ker_subgroupMap, hqker]
      calc
        Nat.card (K.map q) = Nat.card r.range := by
          rw [MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective K),
            Subgroup.card_top]
        _ = r.ker.index := (Subgroup.index_ker r).symm
        _ = C.index := by rw [hrker]
        _ = Nat.card P := hPC.index_eq_card
    have hfbarSurj : Function.Surjective fbar :=
      QuotientGroup.lift_surjective_of_surjective X f hf hXker
    have hfbarCenter : fbar.ker ≤ Subgroup.center (H ⧸ X) := by
      rw [show fbar = QuotientGroup.lift X f hXker by rfl,
        QuotientGroup.ker_lift]
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective X y
      rw [← map_mul, ← map_mul]
      exact congrArg q (Subgroup.mem_center_iff.mp (hker hx) b)
    have hfbarP : IsPGroup 3 fbar.ker := by
      obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
      apply IsPGroup.of_card
      rw [hfbarCard, hk]
    obtain ⟨z, hfbarz, hz⟩ :=
      SchurPresentation.exists_order_three_lift_of_five_le
        m hm fbar hfbarSurj hfbarCenter hfbarP a ha
    have hqkerEq : q.ker = X := QuotientGroup.ker_mk' X
    have hXcard : Nat.card X = Nat.card C := by
      dsimp [X]
      exact Subgroup.card_map_of_injective (K := C) K.subtype_injective
    have hCcard : Nat.card C = P.index := hPC.symm.index_eq_card.symm
    have hqcop : Nat.Coprime (Nat.card q.ker) 3 := by
      rw [hqkerEq, hXcard, hCcard]
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).symm
    obtain ⟨y, hqy, hy⟩ :=
      __ch5_proposition_5_2_6_exists_order_prime_lift_of_coprime_kernel
        3 Nat.prime_three q (QuotientGroup.mk'_surjective X) hqcop z hz
    refine ⟨y, ?_, hy⟩
    have h := congrArg fbar hqy
    simpa [fbar, q] using h.trans hfbarz
  · exact __ch5_proposition_5_2_6_exists_order_prime_lift_of_coprime_kernel
      3 Nat.prime_three f hf
        (Nat.coprime_comm.mp
          (Nat.prime_three.coprime_iff_not_dvd.mpr h3ker))
      a ha

private theorem __ch5_proposition_5_2_6_prime_ne_three_not_dvd_center
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card (Subgroup.center K) := by
  have hp5 : 5 ≤ p :=
    hp.five_le_of_ne_two_of_ne_three hp2 hp3
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  let e : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := e.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp (alternatingQuotientHom quotientEquiv)
  have hf'ker : f'.ker = Subgroup.center K := by
    rw [show f' = eA.toMonoidHom.comp (alternatingQuotientHom quotientEquiv) by rfl,
      MonoidHom.ker_comp_of_injective (alternatingQuotientHom quotientEquiv)
        eA.toMonoidHom eA.injective,
      alternatingQuotientHom_ker quotientEquiv]
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp
      (alternatingQuotientHom_surjective quotientEquiv)
  }
  have hdiv : Nat.card f'.ker ∣
      Nat.card (SchurPresentation.alternatingFreeCentralCovering q).toMonoidHom.ker := by
    simpa [c] using Covering.coveringKernel_card_dvd_of_universal
      (SchurPresentation.alternatingFreeCentralCovering q)
      (SchurPresentation.alternatingFreeCentralCovering_isUniversal q) c
  intro hpcenter
  apply SchurPresentation.not_dvd_natCard_ker_alternatingFreeCentralCovering_of_five_le_prime
    p q hp hp5
  have hpker : p ∣ Nat.card f'.ker := by
    rw [hf'ker]
    exact hpcenter
  exact hpker.trans hdiv

public theorem quotientAction_order
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n p : Nat} (hp : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k))) :
    orderOf quotientAction = p := by
  have hiter : ∀ m : Nat, ∀ k : K,
      (alternatingQuotientHom quotientEquiv) ((x ^ m) k) =
        (quotientAction ^ m) ((alternatingQuotientHom quotientEquiv) k) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro k
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply,
          ih (x k)]
        exact congrArg (quotientAction ^ m)
          (quotientAction_compat k)
  have hpow : quotientAction ^ p = 1 := by
    apply DFunLike.ext _ _
    intro a
    obtain ⟨k, rfl⟩ := alternatingQuotientHom_surjective quotientEquiv a
    have hit := hiter p k
    have hxpow : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    rw [hxpow, MulAut.one_apply] at hit
    exact hit.symm
  have hdvd : orderOf quotientAction ∣ p :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  rcases (Nat.dvd_prime hp).mp hdvd with hone | hp
  · exfalso
    have haone : quotientAction = 1 := orderOf_eq_one_iff.mp hone
    have hxhom : x.toMonoidHom = (1 : MulAut K).toMonoidHom := by
      apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
        (alternatingQuotientHom quotientEquiv)
        (by rw [alternatingQuotientHom_ker quotientEquiv])
      apply MonoidHom.ext
      intro k
      change (alternatingQuotientHom quotientEquiv) (x k) = (alternatingQuotientHom quotientEquiv) k
      calc
        (alternatingQuotientHom quotientEquiv) (x k) =
            quotientAction ((alternatingQuotientHom quotientEquiv) k) :=
          quotientAction_compat k
        _ = (alternatingQuotientHom quotientEquiv) k := by rw [haone]; rfl
    have hxone : x = 1 := by
      apply MulEquiv.ext
      intro k
      exact DFunLike.congr_fun hxhom k
    have h : orderOf x = 1 := by rw [hxone]; exact orderOf_one
    rw [hx] at h
    exact hp.ne_one h
  · exact hp

private theorem __ch5_proposition_5_2_6_oddPrimeOrder_alternatingAut_is_inner
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (alternatingGroup (Fin n))) (hα : orderOf α = p) :
    ∃ a : alternatingGroup (Fin n),
      α = MulAut.conjNormal (a : Equiv.Perm (Fin n)) := by
  have hσ : ∃ σ : Equiv.Perm (Fin n),
      MulAut.conjNormal (H := alternatingGroup (Fin n)) σ = α := by
    by_cases hn6 : n = 6
    · subst n
      let H := naturalAlternatingAutomorphismSubgroup
      let : H.Normal :=
        Subgroup.normal_of_index_eq_two naturalAlternatingAutomorphismSubgroup_index
      let q := QuotientGroup.mk' H
      have hqp : orderOf (q α) ∣ p := by
        rw [← hα]
        exact orderOf_map_dvd q α
      have hq2 : orderOf (q α) ∣ 2 := by
        have hcard : Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ H) = 2 := by
          rw [← H.index_eq_card]
          exact naturalAlternatingAutomorphismSubgroup_index
        rw [← hcard]
        exact orderOf_dvd_natCard (q α)
      have hqone : orderOf (q α) = 1 := by
        rcases (Nat.dvd_prime hp).mp hqp with h1 | hpq
        · exact h1
        · exfalso
          have hpdiv2 : p ∣ 2 := by simpa [hpq] using hq2
          rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv2 with hp1 | hp2eq
          · exact hp.ne_one hp1
          · exact hp2 hp2eq
      have hmem : α ∈ H := by
        apply (QuotientGroup.eq_one_iff α).mp
        exact orderOf_eq_one_iff.mp hqone
      change α ∈ (MulAut.conjNormal
        (H := alternatingGroup (Fin 6))).range at hmem
      rcases hmem with ⟨σ, hσα⟩
      exact ⟨σ, hσα⟩
    · exact (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        n hn hn6).2 α
  obtain ⟨σ, hσα⟩ := hσ
  have hconjInj :=
    GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup
      n ((by omega : 4 ≤ 5).trans hn)
  have hσorder : orderOf σ = p := by
    calc
      orderOf σ = orderOf
          (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ) :=
        (orderOf_injective _ hconjInj σ).symm
      _ = orderOf α := congrArg orderOf hσα
      _ = p := hα
  have hsign : Equiv.Perm.sign σ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · have hpowσ : σ ^ p = 1 := by
        rw [← hσorder]
        exact pow_orderOf_eq_one σ
      have hpowSign := congrArg Equiv.Perm.sign hpowσ
      have hpodd : Odd p := by
        rcases hp.eq_two_or_odd with hp2eq | hpmod
        · exact False.elim (hp2 hp2eq)
        · exact Nat.odd_iff.mpr hpmod
      rw [map_pow, h, hpodd.neg_one_pow, map_one] at hpowSign
      exact False.elim (by norm_num at hpowSign)
  exact ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, hσα.symm⟩

private theorem __ch5_proposition_5_2_6_exists_odd_centralizer_iff
    (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = p) :
    (∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = -1 ∧
      Commute σ a.1) ↔ p + 1 < n := by
  have haPerm : orderOf (a : Equiv.Perm (Fin n)) = p :=
    (Subgroup.orderOf_coe a).trans ha
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · exact (hp2 h).elim
    · exact Nat.odd_iff.mpr h
  have hp3 : 3 ≤ p := by
    have hp2le := hp.two_le
    omega
  have hnotle_iff :
      (¬ Subgroup.centralizer ({(a : Equiv.Perm (Fin n))} :
          Set (Equiv.Perm (Fin n))) ≤ alternatingGroup (Fin n)) ↔
        ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = -1 ∧
          Commute σ a.1 := by
    constructor
    · intro h
      rw [SetLike.not_le_iff_exists] at h
      obtain ⟨σ, hσc, hσodd⟩ := h
      have hsign : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hm1
        · exact False.elim (hσodd (by
            rw [Equiv.Perm.mem_alternatingGroup]
            exact h1))
        · exact hm1
      exact ⟨σ, hsign,
        Subgroup.mem_centralizer_singleton_iff.mp hσc⟩
    · rintro ⟨σ, hsign, hcomm⟩ hle
      have hmem : σ ∈ alternatingGroup (Fin n) := hle
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
      rw [Equiv.Perm.mem_alternatingGroup, hsign] at hmem
      norm_num at hmem
  rw [← hnotle_iff]
  have hcentral_iff :
      Subgroup.centralizer ({(a : Equiv.Perm (Fin n))} :
          Set (Equiv.Perm (Fin n))) ≤ alternatingGroup (Fin n) ↔
        n ≤ p + 1 := by
    constructor
    · intro hcentral
      have hdata := Equiv.Perm.centralizer_le_alternating_iff.mp hcentral
      obtain ⟨r, hcycle⟩ := Equiv.Perm.cycleType_prime_order
        (σ := (a : Equiv.Perm (Fin n))) (by rw [haPerm]; exact hp)
      rw [haPerm] at hcycle
      have hr0 : r = 0 := by
        have hcount := hdata.2.2 p
        rw [hcycle] at hcount
        simp at hcount
        omega
      subst r
      have hsum : (a : Equiv.Perm (Fin n)).cycleType.sum = p := by
        simp [hcycle]
      simpa [hsum] using hdata.2.1
    · intro hbound
      rw [Equiv.Perm.centralizer_le_alternating_iff]
      obtain ⟨r, hcycle⟩ := Equiv.Perm.cycleType_prime_order
        (σ := (a : Equiv.Perm (Fin n))) (by rw [haPerm]; exact hp)
      rw [haPerm] at hcycle
      have hr0 : r = 0 := by
        by_contra hr
        have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
        have hsum : (a : Equiv.Perm (Fin n)).cycleType.sum = p * (r + 1) := by
          simp [hcycle, Nat.mul_add, Nat.mul_comm, Nat.add_comm]
        have hsumle := (a : Equiv.Perm (Fin n)).sum_cycleType_le
        rw [hsum] at hsumle
        have hsumle' : p * (r + 1) ≤ n := by simpa using hsumle
        have h2p : p * 2 ≤ p * (r + 1) :=
          Nat.mul_le_mul_left p (by omega)
        have h2pn : 2 * p ≤ n := by
          simpa [Nat.mul_comm] using h2p.trans hsumle'
        omega
      subst r
      constructor
      · intro c hc
        rw [hcycle] at hc
        simp at hc
        simpa [hc] using hpodd
      constructor
      · have hsum : (a : Equiv.Perm (Fin n)).cycleType.sum = p := by
          simp [hcycle]
        rw [hsum]
        simpa using hbound
      · intro i
        rw [hcycle]
        by_cases hi : i = p <;> simp [hi]
  rw [hcentral_iff]
  omega

private theorem __ch5_proposition_5_2_6_commute_iff_quotient_commute
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {n : Nat}
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin n))
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (h : H) :
    Commute h.1 x ↔
      Commute
        (MulAut.conjNormal (HEquiv h))
        quotientAction := by
  constructor
  · intro hcomm
    apply MulEquiv.ext
    intro a
    obtain ⟨k, rfl⟩ := alternatingQuotientHom_surjective quotientEquiv a
    change MulAut.conjNormal (HEquiv h)
        (quotientAction ((alternatingQuotientHom quotientEquiv) k)) =
      quotientAction
        (MulAut.conjNormal (HEquiv h) ((alternatingQuotientHom quotientEquiv) k))
    calc
      MulAut.conjNormal (HEquiv h)
          (quotientAction ((alternatingQuotientHom quotientEquiv) k)) =
          MulAut.conjNormal (HEquiv h)
            ((alternatingQuotientHom quotientEquiv) (x k)) :=
        congrArg _ (quotientAction_compat k).symm
      _ = (alternatingQuotientHom quotientEquiv) (h.1 (x k)) :=
        (H_action_compat h (x k)).symm
      _ = (alternatingQuotientHom quotientEquiv) (x (h.1 k)) :=
        congrArg (alternatingQuotientHom quotientEquiv) (DFunLike.congr_fun hcomm.eq k)
      _ = quotientAction ((alternatingQuotientHom quotientEquiv) (h.1 k)) :=
        quotientAction_compat (h.1 k)
      _ = quotientAction
          (MulAut.conjNormal (HEquiv h) ((alternatingQuotientHom quotientEquiv) k)) :=
        congrArg quotientAction (H_action_compat h k)
  · intro hcomm
    have hhom : (h.1 * x).toMonoidHom =
        (x * h.1).toMonoidHom := by
      apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
        (alternatingQuotientHom quotientEquiv)
        (by rw [alternatingQuotientHom_ker quotientEquiv])
      apply MonoidHom.ext
      intro k
      change (alternatingQuotientHom quotientEquiv) ((h.1 * x) k) =
        (alternatingQuotientHom quotientEquiv) ((x * h.1) k)
      change (alternatingQuotientHom quotientEquiv) (h.1 (x k)) =
        (alternatingQuotientHom quotientEquiv) (x (h.1 k))
      calc
        (alternatingQuotientHom quotientEquiv) (h.1 (x k)) =
            MulAut.conjNormal (HEquiv h)
              ((alternatingQuotientHom quotientEquiv) (x k)) :=
          H_action_compat h (x k)
        _ = MulAut.conjNormal (HEquiv h)
            (quotientAction ((alternatingQuotientHom quotientEquiv) k)) :=
          congrArg _ (quotientAction_compat k)
        _ = quotientAction
            (MulAut.conjNormal (HEquiv h) ((alternatingQuotientHom quotientEquiv) k)) :=
          DFunLike.congr_fun hcomm.eq ((alternatingQuotientHom quotientEquiv) k)
        _ = quotientAction ((alternatingQuotientHom quotientEquiv) (h.1 k)) :=
          congrArg quotientAction (H_action_compat h k).symm
        _ = (alternatingQuotientHom quotientEquiv) (x (h.1 k)) :=
          (quotientAction_compat (h.1 k)).symm
    apply MulEquiv.ext
    intro k
    exact DFunLike.congr_fun hhom k

private theorem __ch5_proposition_5_2_6_sign_eq_of_mul_eq_one {u v : ℤˣ}
    (huv : u * v = 1) : u = v := by
  rcases Int.units_eq_one_or u with hu | hu <;>
    rcases Int.units_eq_one_or v with hv | hv
  · exact hu.trans hv.symm
  · rw [hu, hv] at huv
    norm_num at huv
  · rw [hu, hv] at huv
    norm_num at huv
  · exact hu.trans hv.symm

private theorem __ch5_proposition_5_2_6_signKernel_decomp_no_odd_pair
    {C : Type*} [Group C] (χ : C →* ℤˣ)
    (R L I : Subgroup C)
    (hRχ : R ≤ χ.ker)
    (hLnorm : L ≤ Subgroup.normalizer R)
    (hIcomm : I ≤ Subgroup.centralizer
      ((R ⊔ L : Subgroup C) : Set C))
    (hsup : I ⊔ (R ⊔ L) = ⊤)
    (hno : ¬ ((∃ l ∈ L, χ l = -1) ∧ (∃ i ∈ I, χ i = -1))) :
    let Z := χ.ker
    let RZ := R.comap Z.subtype
    let LZ := L.comap Z.subtype
    let IZ := I.comap Z.subtype
    (RZ ⊔ LZ) ⊔ IZ = ⊤ := by
  dsimp only
  apply top_unique
  intro z _
  have hz : z.1 ∈ I ⊔ (R ⊔ L) := by rw [hsup]; trivial
  have hRLnormI : R ⊔ L ≤ Subgroup.normalizer I :=
    (Subgroup.le_centralizer_iff.mp hIcomm).trans
      (Subgroup.centralizer_le_normalizer (I : Set C))
  change z.1 ∈ (↑(I ⊔ (R ⊔ L)) : Set C) at hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left I (R ⊔ L) hRLnormI] at hz
  rcases hz with ⟨i, hi, w, hw, hiw⟩
  change w ∈ (↑(R ⊔ L) : Set C) at hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R L hLnorm] at hw
  rcases hw with ⟨r, hr, l, hl, hrl⟩
  have hzval : z.1 = i * (r * l) :=
    hiw.symm.trans (congrArg (i * ·) hrl.symm)
  have hrχ : χ r = 1 := MonoidHom.mem_ker.mp (hRχ hr)
  have hzχ : χ z.1 = 1 := MonoidHom.mem_ker.mp z.2
  rw [hzval, map_mul, map_mul, hrχ, one_mul] at hzχ
  have hil : χ i = χ l := __ch5_proposition_5_2_6_sign_eq_of_mul_eq_one hzχ
  have hiχ : χ i = 1 := by
    rcases Int.units_eq_one_or (χ i) with h1 | hm1
    · exact h1
    · exfalso
      apply hno
      exact ⟨⟨l, hl, hil.symm.trans hm1⟩, ⟨i, hi, hm1⟩⟩
  have hlχ : χ l = 1 := hil.symm.trans hiχ
  let iz : χ.ker := ⟨i, MonoidHom.mem_ker.mpr hiχ⟩
  let rz : χ.ker := ⟨r, hRχ hr⟩
  let lz : χ.ker := ⟨l, MonoidHom.mem_ker.mpr hlχ⟩
  have hiz : iz ∈ I.comap (χ.ker).subtype := hi
  have hrz : rz ∈ R.comap (χ.ker).subtype := hr
  have hlz : lz ∈ L.comap (χ.ker).subtype := hl
  have hprod : iz * (rz * lz) ∈
      (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
        I.comap (χ.ker).subtype := by
    apply Subgroup.mul_mem
    · exact ((le_sup_right : I.comap (χ.ker).subtype ≤
        (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
          I.comap (χ.ker).subtype) hiz)
    · exact ((le_sup_left :
        R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype ≤
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype)
        ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype).mul_mem
          ((le_sup_left : R.comap (χ.ker).subtype ≤
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hrz)
          ((le_sup_right : L.comap (χ.ker).subtype ≤
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hlz)))
  have heq : z = iz * (rz * lz) := by
    apply Subtype.ext
    exact hzval
  rwa [heq]

private theorem __ch5_proposition_5_2_6_signKernel_decomp_with_odd_pair
    {C : Type*} [Group C] (χ : C →* ℤˣ)
    (R L I : Subgroup C)
    (hRχ : R ≤ χ.ker)
    (hLnorm : L ≤ Subgroup.normalizer R)
    (hIcomm : I ≤ Subgroup.centralizer
      ((R ⊔ L : Subgroup C) : Set C))
    (hsup : I ⊔ (R ⊔ L) = ⊤)
    (l0 i0 : C) (hl0 : l0 ∈ L) (hi0 : i0 ∈ I)
    (hl0χ : χ l0 = -1) (hi0χ : χ i0 = -1)
    (hl02 : l0 ^ 2 = 1) (hi02 : i0 ^ 2 = 1) :
    let Z := χ.ker
    let RZ := R.comap Z.subtype
    let LZ := L.comap Z.subtype
    let IZ := I.comap Z.subtype
    let t : Z := ⟨i0 * l0, by
      rw [MonoidHom.mem_ker, map_mul, hi0χ, hl0χ]
      norm_num⟩
    ((RZ ⊔ LZ) ⊔ IZ) ⊔ Subgroup.zpowers t = ⊤ ∧ t ^ 2 = 1 := by
  dsimp only
  let t : χ.ker := ⟨i0 * l0, by
    rw [MonoidHom.mem_ker, map_mul, hi0χ, hl0χ]
    norm_num⟩
  have hi0RL : Commute i0 l0 := by
    have himem := hIcomm hi0
    rw [Subgroup.mem_centralizer_iff] at himem
    exact (Commute.symm (himem l0
      ((le_sup_right : L ≤ R ⊔ L) hl0)))
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    change (i0 * l0) ^ 2 = 1
    rw [pow_two]
    calc
      i0 * l0 * (i0 * l0) = i0 * (l0 * i0) * l0 := by group
      _ = i0 * (i0 * l0) * l0 := by rw [hi0RL.eq.symm]
      _ = (i0 ^ 2) * (l0 ^ 2) := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hi02, hl02, one_mul]
  constructor
  · apply top_unique
    intro z _
    have hz : z.1 ∈ I ⊔ (R ⊔ L) := by rw [hsup]; trivial
    have hRLnormI : R ⊔ L ≤ Subgroup.normalizer I :=
      (Subgroup.le_centralizer_iff.mp hIcomm).trans
        (Subgroup.centralizer_le_normalizer (I : Set C))
    change z.1 ∈ (↑(I ⊔ (R ⊔ L)) : Set C) at hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left I (R ⊔ L) hRLnormI] at hz
    rcases hz with ⟨i, hi, w, hw, hiw⟩
    change w ∈ (↑(R ⊔ L) : Set C) at hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R L hLnorm] at hw
    rcases hw with ⟨r, hr, l, hl, hrl⟩
    have hzval : z.1 = i * (r * l) :=
      hiw.symm.trans (congrArg (i * ·) hrl.symm)
    have hrχ : χ r = 1 := MonoidHom.mem_ker.mp (hRχ hr)
    have hzχ : χ z.1 = 1 := MonoidHom.mem_ker.mp z.2
    rw [hzval, map_mul, map_mul, hrχ, one_mul] at hzχ
    have hil : χ i = χ l := __ch5_proposition_5_2_6_sign_eq_of_mul_eq_one hzχ
    rcases Int.units_eq_one_or (χ i) with hiχ | hiχ
    · have hlχ : χ l = 1 := hil.symm.trans hiχ
      let iz : χ.ker := ⟨i, MonoidHom.mem_ker.mpr hiχ⟩
      let rz : χ.ker := ⟨r, hRχ hr⟩
      let lz : χ.ker := ⟨l, MonoidHom.mem_ker.mpr hlχ⟩
      have hbase : iz * (rz * lz) ∈
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype := by
        apply Subgroup.mul_mem
        · exact ((le_sup_right : I.comap (χ.ker).subtype ≤
            (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
              I.comap (χ.ker).subtype) hi)
        · exact ((le_sup_left :
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype ≤
              (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
                I.comap (χ.ker).subtype)
            ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype).mul_mem
              ((le_sup_left : R.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hr)
              ((le_sup_right : L.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hl)))
      have heq : z = iz * (rz * lz) := Subtype.ext hzval
      rw [heq]
      exact ((le_sup_left :
        (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
          I.comap (χ.ker).subtype ≤
        ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
          I.comap (χ.ker).subtype) ⊔ Subgroup.zpowers t) hbase)
    · have hlχ : χ l = -1 := hil.symm.trans hiχ
      have hii0χ : χ (i * i0) = 1 := by simp [hiχ, hi0χ]
      have hll0χ : χ (l * l0) = 1 := by simp [hlχ, hl0χ]
      let iz : χ.ker := ⟨i * i0, MonoidHom.mem_ker.mpr hii0χ⟩
      let rz : χ.ker := ⟨r, hRχ hr⟩
      let lz : χ.ker := ⟨l * l0, MonoidHom.mem_ker.mpr hll0χ⟩
      have hi0w : Commute i0 (r * (l * l0)) := by
        have himem := hIcomm hi0
        rw [Subgroup.mem_centralizer_iff] at himem
        exact Commute.symm (himem _ ((R ⊔ L).mul_mem
          ((le_sup_left : R ≤ R ⊔ L) hr)
          ((R ⊔ L).mul_mem ((le_sup_right : L ≤ R ⊔ L) hl)
            ((le_sup_right : L ≤ R ⊔ L) hl0))))
      have hbase : iz * (rz * lz) ∈
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype := by
        apply Subgroup.mul_mem
        · exact ((le_sup_right : I.comap (χ.ker).subtype ≤
            (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
              I.comap (χ.ker).subtype) (I.mul_mem hi hi0))
        · exact ((le_sup_left :
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype ≤
              (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
                I.comap (χ.ker).subtype)
            ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype).mul_mem
              ((le_sup_left : R.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hr)
              ((le_sup_right : L.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype)
                (L.mul_mem hl hl0))))
      have htmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      have heq : z = (iz * (rz * lz)) * t := by
        apply Subtype.ext
        change z.1 = ((i * i0) * (r * (l * l0))) * (i0 * l0)
        refine hzval.trans ?_
        symm
        calc
          ((i * i0) * (r * (l * l0))) * (i0 * l0) =
              i * (i0 * (r * (l * l0))) * i0 * l0 := by group
          _ = i * ((r * (l * l0)) * i0) * i0 * l0 := by rw [hi0w.eq]
          _ = i * (r * (l * l0)) * (i0 ^ 2) * l0 := by simp [pow_two, mul_assoc]
          _ = i * (r * (l * l0)) * l0 := by rw [hi02]; simp
          _ = i * (r * l) * (l0 ^ 2) := by simp [pow_two, mul_assoc]
          _ = i * (r * l) := by rw [hl02]; simp
      rw [heq]
      exact Subgroup.mul_mem _
        ((le_sup_left :
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype ≤
          ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype) ⊔ Subgroup.zpowers t) hbase)
        ((le_sup_right : Subgroup.zpowers t ≤
          ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype) ⊔ Subgroup.zpowers t) htmem)
  · exact ht2

private theorem __ch5_proposition_5_2_6_index_adjoin_involution_eq_two
    {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (ht2 : t ^ 2 = 1) (htnot : t ∉ H)
    (htnorm : t ∈ Subgroup.normalizer H) :
    (H.subgroupOf (H ⊔ Subgroup.zpowers t)).index = 2 := by
  have htord : orderOf t = 2 := by
    have hdvd : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ht2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · have ht1 : t = 1 := orderOf_eq_one_iff.mp h1
      exact False.elim (htnot (ht1.symm ▸ H.one_mem))
    · exact h2
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  let K := H ⊔ Subgroup.zpowers t
  let tt : K := ⟨t, (le_sup_right : Subgroup.zpowers t ≤
    H ⊔ Subgroup.zpowers t) (Subgroup.mem_zpowers t)⟩
  refine ⟨tt, ?_, ?_⟩
  · exact htnot
  · intro b
    have hpowNorm : Subgroup.zpowers t ≤ Subgroup.normalizer H :=
      Subgroup.zpowers_le.mpr htnorm
    have hb : b.1 ∈ (↑(H ⊔ Subgroup.zpowers t) : Set G) := b.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H (Subgroup.zpowers t)
      hpowNorm] at hb
    rcases hb with ⟨h, hh, k, hk, hhk⟩
    rcases hk with ⟨z, rfl⟩
    have hzpow : t ^ z = t ^ (z % (orderOf t : ℤ)) :=
      (zpow_mod_orderOf t z).symm
    rw [htord] at hzpow
    norm_num at hzpow
    rcases Int.emod_two_eq_zero_or_one z with hz | hz
    · right
      change b.1 ∈ H
      rw [← hhk]
      change h * t ^ z ∈ H
      rw [hzpow, hz]
      simpa using hh
    · left
      change b.1 * t ∈ H
      rw [← hhk]
      change (h * t ^ z) * t ∈ H
      rw [hzpow, hz]
      simpa [zpow_one, mul_assoc, ← pow_two, ht2] using hh

private noncomputable def centralizerSignKernelEquivFixed
    {n : Nat} (a : alternatingGroup (Fin n)) :
    (Equiv.Perm.sign.comp
        (Subgroup.subtype (Subgroup.centralizer
          ({(a : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))))).ker ≃*
      automorphismFixedSubgroup (MulAut.conj a) where
  toFun z := ⟨⟨z.1.1, by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact MonoidHom.mem_ker.mp z.2⟩, by
      change (MulAut.conj a) ⟨z.1.1, _⟩ = ⟨z.1.1, _⟩
      apply Subtype.ext
      change a.1 * z.1.1 * a.1⁻¹ = z.1.1
      have hcomm : Commute z.1.1 a.1 :=
        Subgroup.mem_centralizer_singleton_iff.mp z.1.2
      rw [hcomm.eq.symm, mul_inv_cancel_right]⟩
  invFun g := ⟨⟨g.1.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix := g.2
    have h := congrArg (fun q : alternatingGroup (Fin n) ↦ q * a) hfix
    change a * g.1 * a⁻¹ = g.1 at hfix
    have hA : g.1 * a = a * g.1 := by simpa [mul_assoc] using h.symm
    exact congrArg Subtype.val hA⟩, by
      rw [MonoidHom.mem_ker]
      exact g.1.2⟩
  left_inv z := by ext; rfl
  right_inv g := by ext; rfl
  map_mul' _ _ := rfl


private theorem __ch5_proposition_5_2_6_rotation_even
    {n : Nat} (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = p) :
    cycleRotationSubgroup (a : Equiv.Perm (Fin n)) ≤
      (Equiv.Perm.sign.comp
        (Subgroup.subtype (Subgroup.centralizer
          ({(a : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))))).ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  let zR : cycleRotationSubgroup (a : Equiv.Perm (Fin n)) := ⟨z, hz⟩
  have haPerm : orderOf (a : Equiv.Perm (Fin n)) = p :=
    (Subgroup.orderOf_coe a).trans ha
  have hzpow := theorem_5_2_2_d_2_b
    (a : Equiv.Perm (Fin n)) (by simpa [haPerm] using hp) zR
  rw [haPerm] at hzpow
  have hsignpow := congrArg (fun q : cycleRotationSubgroup
      (a : Equiv.Perm (Fin n)) ↦ Equiv.Perm.sign q.1.1) hzpow
  change Equiv.Perm.sign (z.1 ^ p) = Equiv.Perm.sign 1 at hsignpow
  rcases Int.units_eq_one_or (Equiv.Perm.sign z.1) with h | h
  · exact h
  · have hpodd : Odd p := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact (hp2 h2).elim
      · exact Nat.odd_iff.mpr hodd
    rw [map_pow, h, hpodd.neg_one_pow, map_one] at hsignpow
    norm_num at hsignpow


private theorem __ch5_proposition_5_2_6_cyclePermutation_swap_sign
    {n : Nat} (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = p)
    (c d : (a : Equiv.Perm (Fin n)).cycleFactorsFinset) (hcd : c ≠ d) :
    Equiv.Perm.sign
      ((theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
        (by simpa [(Subgroup.orderOf_coe a).trans ha] using hp)).symm
          (Equiv.swap c d)).1.1 = -1 := by
  let e := theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
    (by simpa [(Subgroup.orderOf_coe a).trans ha] using hp)
  have haPerm : orderOf (a : Equiv.Perm (Fin n)) = p :=
    (Subgroup.orderOf_coe a).trans ha
  let l := e.symm (Equiv.swap c d)
  have hl2 : l ^ 2 = 1 := by
    apply e.injective
    simp [l, pow_two]
  have hlPerm2 : l.1.1 ^ 2 = 1 := by
    exact congrArg (fun z : cyclePermutationSubgroup
      (a : Equiv.Perm (Fin n)) ↦ z.1.1) hl2
  have hlsupport : l.1.1.support.card = 2 * p := by
    rcases l.2 with ⟨q, hq⟩
    rw [← hq]
    change (Equiv.Perm.Basis.ofPermHom
      (Classical.choice (Equiv.Perm.Basis.nonempty (a : Equiv.Perm (Fin n))))
      (cycleActionRangeToExplicitRange (a : Equiv.Perm (Fin n)) q)).support.card = 2 * p
    rw [Equiv.Perm.Basis.card_ofPermHom_support]
    have hqval : (q : Equiv.Perm
        (a : Equiv.Perm (Fin n)).cycleFactorsFinset) = Equiv.swap c d := by
      have hel := e.apply_symm_apply (Equiv.swap c d)
      let e1 := cycleActionRangeMulEquivCyclePermutationSubgroup
        (a : Equiv.Perm (Fin n))
      let e2 := cycleActionRangeMulEquivPermOfPrimeOrder
        (a : Equiv.Perm (Fin n)) (by simpa [haPerm] using hp)
      have he1 : e1 q = l := by
        apply Subtype.ext
        exact hq
      have hqinv : e1.symm l = q := by
        rw [← he1]
        exact e1.symm_apply_apply q
      calc
        (q : Equiv.Perm (a : Equiv.Perm (Fin n)).cycleFactorsFinset) =
            e2 q := rfl
        _ = e2 (e1.symm l) := congrArg e2 hqinv.symm
        _ = e l := rfl
        _ = Equiv.swap c d := hel
    change ∑ c ∈ (q : Equiv.Perm
      (a : Equiv.Perm (Fin n)).cycleFactorsFinset).support,
        c.1.support.card = 2 * p
    rw [hqval, Equiv.Perm.support_swap hcd]
    simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_singleton,
      hcd, not_false_eq_true]
    rw [cycleFactor_support_card_eq_orderOf_of_primeOrder _
        (by simpa [haPerm] using hp),
      cycleFactor_support_card_eq_orderOf_of_primeOrder _
        (by simpa [haPerm] using hp), haPerm]
    omega
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact (hp2 h2).elim
    · exact Nat.odd_iff.mpr hodd
  rw [Equiv.Perm.sign_of_pow_two_eq_one hlPerm2]
  have hdiff : Fintype.card (Fin n) -
      Fintype.card (Function.fixedPoints l.1.1) = 2 * p := by
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, hlsupport]
    have hle := l.1.1.support.card_le_univ
    simp only [Fintype.card_fin] at hle ⊢
    omega
  rw [hdiff]
  simpa [Nat.mul_comm] using hpodd.neg_one_pow

private theorem __ch5_proposition_5_2_6_cyclePermutation_sign
    {n : Nat} (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = p)
    (l : cyclePermutationSubgroup (a : Equiv.Perm (Fin n))) :
    Equiv.Perm.sign l.1.1 = Equiv.Perm.sign
      ((theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
        (by simpa [(Subgroup.orderOf_coe a).trans ha] using hp)) l) := by
  let e := theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
    (by simpa [(Subgroup.orderOf_coe a).trans ha] using hp)
  have hqsign : ∀ q : Equiv.Perm
      (a : Equiv.Perm (Fin n)).cycleFactorsFinset,
      Equiv.Perm.sign (e.symm q).1.1 = Equiv.Perm.sign q := by
    intro q
    induction q using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul q c d hcd ih =>
        rw [map_mul]
        change Equiv.Perm.sign
            ((e.symm (Equiv.swap c d)).1.1 * (e.symm q).1.1) =
          Equiv.Perm.sign (Equiv.swap c d * q)
        rw [map_mul, map_mul, Equiv.Perm.sign_swap hcd, ih,
          __ch5_proposition_5_2_6_cyclePermutation_swap_sign p hp hp2 a ha c d hcd]
  simpa using hqsign (e l)


private theorem __ch5_proposition_5_2_6_fixedPointPermutation_sign
    {n : Nat} (a : alternatingGroup (Fin n))
    (i : fixedPointPermutationSubgroup (a : Equiv.Perm (Fin n))) :
    Equiv.Perm.sign i.1.1 = Equiv.Perm.sign
      ((theorem_5_2_2_d_4 (a : Equiv.Perm (Fin n))) i) := by
  let e := theorem_5_2_2_d_4 (a : Equiv.Perm (Fin n))
  let u := e i
  have hi : i = e.symm u := by simp [u]
  rw [hi]
  rw [e.apply_symm_apply]
  dsimp [e, theorem_5_2_2_d_4, fixedPointPermMulEquivSubgroup]
  change Equiv.Perm.sign
      ((fixedPointPermToCentralizer (a : Equiv.Perm (Fin n))) u).1 =
    Equiv.Perm.sign u
  rw [fixedPointPermToCentralizer_coe, Equiv.Perm.sign_ofSubtype]


private noncomputable def cycleRotationGroupMulEquivZModPi
    {n : Nat} (a : alternatingGroup (Fin n))
    (hp : (orderOf (a : Equiv.Perm (Fin n))).Prime) :
    CycleRotationGroup (a : Equiv.Perm (Fin n)) ≃*
      Multiplicative
        (Fin (Fintype.card (a : Equiv.Perm (Fin n)).cycleFactorsFinset) →
          ZMod (orderOf (a : Equiv.Perm (Fin n)))) := by
  let coord : CycleRotationGroup (a : Equiv.Perm (Fin n)) ≃*
      ((c : (a : Equiv.Perm (Fin n)).cycleFactorsFinset) →
        Multiplicative (ZMod (orderOf (a : Equiv.Perm (Fin n))))) :=
    MulEquiv.piCongrRight (fun c ↦
      (zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
        (cycleFactorZPowers_card_of_primeOrder
          (a : Equiv.Perm (Fin n)) hp c)).symm)
  let idx := Fintype.equivFin
    (a : Equiv.Perm (Fin n)).cycleFactorsFinset
  let reindex :
      ((c : (a : Equiv.Perm (Fin n)).cycleFactorsFinset) →
        Multiplicative (ZMod (orderOf (a : Equiv.Perm (Fin n))))) ≃*
      Multiplicative
        (Fin (Fintype.card (a : Equiv.Perm (Fin n)).cycleFactorsFinset) →
          ZMod (orderOf (a : Equiv.Perm (Fin n)))) := {
    toFun f := Multiplicative.ofAdd (fun i ↦ Multiplicative.toAdd (f (idx.symm i)))
    invFun f := fun c ↦ Multiplicative.ofAdd (Multiplicative.toAdd f (idx c))
    left_inv f := by funext c; simp
    right_inv f := by apply Multiplicative.toAdd.injective; funext i; simp
    map_mul' _ _ := rfl }
  exact coord.trans reindex


private noncomputable def cyclePermutationEvenMulEquivAlternating
    {n : Nat} (p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = p) :
    let C := Subgroup.centralizer
      ({(a : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))
    let Z := (Equiv.Perm.sign.comp (Subgroup.subtype C)).ker
    ↥((cyclePermutationSubgroup (a : Equiv.Perm (Fin n))).comap Z.subtype) ≃*
      alternatingGroup
        (a : Equiv.Perm (Fin n)).cycleFactorsFinset := by
  dsimp only
  let e := theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
    (by simpa [(Subgroup.orderOf_coe a).trans ha] using hp)
  refine {
    toFun := fun z ↦ ⟨e ⟨z.1.1, z.2⟩, ?_⟩
    invFun := fun u ↦
      ⟨⟨(e.symm u.1).1, ?_⟩, (e.symm u.1).2⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · rw [Equiv.Perm.mem_alternatingGroup]
    rw [← __ch5_proposition_5_2_6_cyclePermutation_sign p hp hp2 a ha]
    exact MonoidHom.mem_ker.mp z.1.2
  · rw [MonoidHom.mem_ker]
    change Equiv.Perm.sign (e.symm u.1).1.1 = 1
    rw [__ch5_proposition_5_2_6_cyclePermutation_sign p hp hp2 a ha]
    rw [e.apply_symm_apply]
    exact Equiv.Perm.mem_alternatingGroup.mp u.2
  · intro z
    have heC : (e.symm (e ⟨z.1.1, z.2⟩)).1 = z.1.1 :=
      congrArg Subtype.val (e.symm_apply_apply ⟨z.1.1, z.2⟩)
    exact Subtype.ext (Subtype.ext heC)
  · intro u
    apply Subtype.ext
    exact e.apply_symm_apply u.1
  · intro x y
    apply Subtype.ext
    exact map_mul e ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩


public noncomputable def fixedPointEvenMulEquivAlternating
    {n : Nat} (a : alternatingGroup (Fin n)) :
    let C := Subgroup.centralizer
      ({(a : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))
    let Z := (Equiv.Perm.sign.comp (Subgroup.subtype C)).ker
    ↥((fixedPointPermutationSubgroup (a : Equiv.Perm (Fin n))).comap Z.subtype) ≃*
      alternatingGroup (Function.fixedPoints (a : Equiv.Perm (Fin n))) := by
  dsimp only
  let e := theorem_5_2_2_d_4 (a : Equiv.Perm (Fin n))
  refine {
    toFun := fun z ↦ ⟨e ⟨z.1.1, z.2⟩, ?_⟩
    invFun := fun u ↦
      ⟨⟨(e.symm u.1).1, ?_⟩, (e.symm u.1).2⟩
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · rw [Equiv.Perm.mem_alternatingGroup]
    rw [← __ch5_proposition_5_2_6_fixedPointPermutation_sign a]
    exact MonoidHom.mem_ker.mp z.1.2
  · rw [MonoidHom.mem_ker]
    change Equiv.Perm.sign (e.symm u.1).1.1 = 1
    rw [__ch5_proposition_5_2_6_fixedPointPermutation_sign a]
    rw [e.apply_symm_apply]
    exact Equiv.Perm.mem_alternatingGroup.mp u.2
  · intro z
    have heC : (e.symm (e ⟨z.1.1, z.2⟩)).1 = z.1.1 :=
      congrArg Subtype.val (e.symm_apply_apply ⟨z.1.1, z.2⟩)
    exact Subtype.ext (Subtype.ext heC)
  · intro u
    apply Subtype.ext
    exact e.apply_symm_apply u.1
  · intro x y
    apply Subtype.ext
    exact map_mul e ⟨x.1.1, x.2⟩ ⟨y.1.1, y.2⟩

public theorem alternatingPrimeCentralizerStructure
    (n p : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (a : alternatingGroup (Fin n)) (ha : orderOf a = p) :
    let r := Fintype.card (a : Equiv.Perm (Fin n)).cycleFactorsFinset
    let s := Fintype.card (Function.fixedPoints (a : Equiv.Perm (Fin n)))
    ∃ (Rbar Lbar H1bar H2bar : Subgroup (alternatingGroup (Fin n)))
      (tbar : alternatingGroup (Fin n)),
      automorphismFixedSubgroup (MulAut.conj a) =
          (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar ∧
        H1bar = Rbar ⊔ Lbar ∧
        (Rbar.subgroupOf H1bar).Normal ∧
        Disjoint H1bar H2bar ∧
        (∀ x : ↥H1bar, ∀ y : ↥H2bar, Commute x.1 y.1) ∧
        Disjoint Lbar
          (Subgroup.centralizer
            (Rbar : Set (alternatingGroup (Fin n)))) ∧
        Nonempty (↥Rbar ≃* Multiplicative (Fin r → ZMod p)) ∧
        Nonempty (↥Lbar ≃* alternatingGroup (Fin r)) ∧
        (∃ eH2 : ↥H2bar ≃* alternatingGroup (Fin s),
          ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card) ∧
        tbar ^ 2 = 1 ∧
        ((s ≤ 1 ∨ r = 1) → tbar = 1) ∧
        ((2 ≤ s ∧ 2 ≤ r) →
          (H1bar.subgroupOf (H1bar ⊔ Subgroup.zpowers tbar)).index = 2 ∧
          (H2bar.subgroupOf (H2bar ⊔ Subgroup.zpowers tbar)).index = 2) := by
  dsimp only
  let x : Equiv.Perm (Fin n) := a
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n)))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  let Z := χ.ker
  let F := automorphismFixedSubgroup (MulAut.conj a)
  let eZ : Z ≃* F := centralizerSignKernelEquivFixed a
  let φ : Z →* alternatingGroup (Fin n) := F.subtype.comp eZ.toMonoidHom
  let R : Subgroup C := cycleRotationSubgroup x
  let L : Subgroup C := cyclePermutationSubgroup x
  let I : Subgroup C := fixedPointPermutationSubgroup x
  let RZ : Subgroup Z := R.comap Z.subtype
  let LZ : Subgroup Z := L.comap Z.subtype
  let IZ : Subgroup Z := I.comap Z.subtype
  let H1Z : Subgroup Z := RZ ⊔ LZ
  let Rbar : Subgroup (alternatingGroup (Fin n)) := RZ.map φ
  let Lbar : Subgroup (alternatingGroup (Fin n)) := LZ.map φ
  let H1bar : Subgroup (alternatingGroup (Fin n)) := H1Z.map φ
  let H2bar : Subgroup (alternatingGroup (Fin n)) := IZ.map φ
  have haPerm : orderOf x = p := (Subgroup.orderOf_coe a).trans ha
  have hxprime : (orderOf x).Prime := by simpa [haPerm] using hp
  have hRχ : R ≤ χ.ker := by
    exact __ch5_proposition_5_2_6_rotation_even p hp hp2 a ha
  have hφinj : Function.Injective φ :=
    F.subtype_injective.comp eZ.injective
  have hφrange : φ.range = F := by
    ext g
    constructor
    · rintro ⟨z, rfl⟩
      exact (eZ z).2
    · intro hg
      let gf : F := ⟨g, hg⟩
      refine ⟨eZ.symm gf, ?_⟩
      rfl
  have hH1eq : H1bar = Rbar ⊔ Lbar := by
    dsimp [H1bar, H1Z, Rbar, Lbar]
    exact Subgroup.map_sup RZ LZ φ
  have hLnorm : L ≤ Subgroup.normalizer R :=
    cyclePermutationSubgroup_le_normalizer_cycleRotationSubgroup x
  have hIcomm : I ≤ Subgroup.centralizer ((R ⊔ L : Subgroup C) : Set C) :=
    (theorem_5_2_2_d_1 x hxprime).2.2.2.2
  have hsup : I ⊔ (R ⊔ L) = ⊤ :=
    (theorem_5_2_2_d_1 x hxprime).2.2.2.1
  have hnormal : (Rbar.subgroupOf H1bar).Normal := by
    have hRZnormal : RZ.Normal :=
      (cycleRotationSubgroup_normal x).comap Z.subtype
    have hRZH : (RZ.subgroupOf H1Z).Normal := hRZnormal.subgroupOf H1Z
    let eH : H1Z ≃* H1bar :=
      Subgroup.equivMapOfInjective H1Z φ hφinj
    have hmapped := hRZH.map eH.toMonoidHom eH.surjective
    convert hmapped using 1
    ext r
    change (r.1 ∈ RZ.map φ) ↔
      ∃ z : H1Z, z ∈ RZ.subgroupOf H1Z ∧ eH z = r
    constructor
    · rintro ⟨q, hq, hqr⟩
      let qH : H1Z :=
        ⟨q, (le_sup_left : RZ ≤ RZ ⊔ LZ) hq⟩
      refine ⟨qH, hq, ?_⟩
      apply Subtype.ext
      exact hqr
    · rintro ⟨z, hz, hzr⟩
      refine ⟨z.1, hz, ?_⟩
      exact congrArg Subtype.val hzr
  have hdisjoint : Disjoint H1bar H2bar := by
    have hH1le : H1Z ≤ (R ⊔ L).comap Z.subtype := by
      apply sup_le
      · intro z hz
        exact (le_sup_left : R ≤ R ⊔ L) hz
      · intro z hz
        exact (le_sup_right : L ≤ R ⊔ L) hz
    have hdisjZ : Disjoint H1Z IZ := by
      rw [Subgroup.disjoint_def]
      intro z hzH1 hzI
      have hzC : z.1 ∈ I ⊓ (R ⊔ L) := ⟨hzI, hH1le hzH1⟩
      have hbot : z.1 ∈ (⊥ : Subgroup C) := by
        rw [← (theorem_5_2_2_d_1 x hxprime).2.2.1]
        exact hzC
      simpa using hbot
    exact Subgroup.disjoint_map hφinj hdisjZ
  have hcommute : ∀ x : ↥H1bar, ∀ y : ↥H2bar, Commute x.1 y.1 := by
    have hH1le : H1Z ≤ (R ⊔ L).comap Z.subtype := by
      apply sup_le
      · intro z hz
        exact (le_sup_left : R ≤ R ⊔ L) hz
      · intro z hz
        exact (le_sup_right : L ≤ R ⊔ L) hz
    intro g h
    obtain ⟨z, hz, hzg⟩ := g.2
    obtain ⟨i, hi, hih⟩ := h.2
    have himem := hIcomm hi
    rw [Subgroup.mem_centralizer_iff] at himem
    have hC : Commute z.1 i.1 := himem z.1 (hH1le hz)
    have hZ : Commute z i := by
      apply Subtype.ext
      exact hC.eq
    rw [← hzg, ← hih]
    exact hZ.map φ
  have hfaithful : Disjoint Lbar
      (Subgroup.centralizer (Rbar : Set (alternatingGroup (Fin n)))) := by
    rw [Subgroup.disjoint_def]
    intro g hgL hgC
    obtain ⟨lz, hlz, hlg⟩ := hgL
    have hlzCentral : lz.1 ∈ Subgroup.centralizer (R : Set C) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      let rz : RZ := ⟨⟨r, hRχ hr⟩, hr⟩
      have hφrz : φ rz ∈ Rbar := ⟨rz, rz.2, rfl⟩
      have hcommMap := Subgroup.mem_centralizer_iff.mp hgC _ hφrz
      rw [← hlg] at hcommMap
      have hzr : rz * lz = lz * rz := hφinj hcommMap
      exact congrArg (fun z : Z => z.1) hzr
    have hlbot : lz.1 ∈ (⊥ : Subgroup C) := by
      rw [← cyclePermutationSubgroup_inf_centralizer_cycleRotation_eq_bot x]
      exact ⟨hlz, hlzCentral⟩
    have hlone : lz = 1 := by
      apply Subtype.ext
      simpa using hlbot
    rw [hlone, map_one] at hlg
    simpa using hlg.symm
  have hRbarEquiv : Nonempty
      (↥Rbar ≃* Multiplicative
        (Fin (Fintype.card x.cycleFactorsFinset) → ZMod p)) := by
    let eMap : RZ ≃* Rbar :=
      Subgroup.equivMapOfInjective RZ φ hφinj
    let eRZ : RZ ≃* R := {
      toFun := fun z ↦ ⟨z.1.1, z.2⟩
      invFun := fun r ↦ ⟨⟨r.1, hRχ r.2⟩, r.2⟩
      left_inv := fun z ↦ by ext; rfl
      right_inv := fun r ↦ by ext; rfl
      map_mul' := fun _ _ ↦ rfl }
    let e0 := eMap.symm.trans (eRZ.trans
      ((cycleRotationGroupMulEquivSubgroup x).symm.trans
        (cycleRotationGroupMulEquivZModPi a
          (by simpa [x] using hxprime))))
    have haPermA : orderOf (a : Equiv.Perm (Fin n)) = p :=
      (Subgroup.orderOf_coe a).trans ha
    exact ⟨by
      rw [← haPermA]
      simpa [x] using e0⟩
  have hLbarEquiv : Nonempty
      (↥Lbar ≃* alternatingGroup
        (Fin (Fintype.card x.cycleFactorsFinset))) := by
    let eMap : LZ ≃* Lbar :=
      Subgroup.equivMapOfInjective LZ φ hφinj
    let eEven := cyclePermutationEvenMulEquivAlternating p hp hp2 a ha
    let eFin := (Fintype.equivFin
      (a : Equiv.Perm (Fin n)).cycleFactorsFinset).altCongrHom
    let e0 := eMap.symm.trans (eEven.trans eFin)
    exact ⟨by simpa [x, C, χ, Z, L, LZ, Lbar] using e0⟩
  have hH2barEquiv : ∃ eH2 : ↥H2bar ≃* alternatingGroup
      (Fin (Fintype.card (Function.fixedPoints x))),
      ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card := by
    let eMap : IZ ≃* H2bar :=
      Subgroup.equivMapOfInjective IZ φ hφinj
    let eEven := fixedPointEvenMulEquivAlternating a
    let eFin := (Fintype.equivFin
      (Function.fixedPoints (a : Equiv.Perm (Fin n)))).altCongrHom
    let eH2 : H2bar ≃* alternatingGroup
        (Fin (Fintype.card (Function.fixedPoints x))) := by
      simpa [x, C, χ, Z, I, IZ, H2bar] using
        eMap.symm.trans (eEven.trans eFin)
    refine ⟨eH2, ?_⟩
    intro u
    change (eFin (eEven (eMap.symm u))).1.support.card = u.1.1.support.card
    calc
      _ = (eEven (eMap.symm u)).1.support.card := by
        simpa [eFin] using card_support_permCongr
          (Fintype.equivFin (Function.fixedPoints x))
          (eEven (eMap.symm u)).1
      _ = (eMap.symm u).1.1.1.support.card := by
        let z := eMap.symm u
        let i : fixedPointPermutationSubgroup x := ⟨z.1.1, z.2⟩
        let v : Equiv.Perm (Function.fixedPoints x) :=
          (theorem_5_2_2_d_4 x) i
        have hi : i = (fixedPointPermMulEquivSubgroup x) v := by
          apply (theorem_5_2_2_d_4 x).injective
          simp [v, theorem_5_2_2_d_4]
        have hcoe : i.1.1 = Equiv.Perm.ofSubtype v := by
          rw [hi]
          exact fixedPointPermToCentralizer_coe x v
        change v.support.card = i.1.1.support.card
        rw [hcoe, Equiv.Perm.support_ofSubtype, Finset.card_map]
      _ = u.1.1.support.card := by
        have hu := congrArg Subtype.val (eMap.apply_symm_apply u)
        change φ (eMap.symm u).1 = u.1 at hu
        have hφcoe : (φ (eMap.symm u).1).1 =
            (eMap.symm u).1.1.1 := rfl
        rw [← hφcoe]
        exact congrArg
          (fun g : alternatingGroup (Fin n) => g.1.support.card) hu
  by_cases hrs : 2 ≤ Fintype.card x.cycleFactorsFinset ∧
      2 ≤ Fintype.card (Function.fixedPoints x)
  · obtain ⟨c, d, hcd⟩ := Fintype.exists_pair_of_one_lt_card
      (show 1 < Fintype.card x.cycleFactorsFinset by omega)
    obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card
      (show 1 < Fintype.card (Function.fixedPoints x) by omega)
    let eL := theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
      (by simpa [x] using hxprime)
    let eI := theorem_5_2_2_d_4 (a : Equiv.Perm (Fin n))
    let l0 : L := eL.symm (Equiv.swap c d)
    let i0 : I := eI.symm (Equiv.swap u v)
    have hl0χ : χ l0.1 = -1 := by
      change Equiv.Perm.sign l0.1.1 = -1
      rw [__ch5_proposition_5_2_6_cyclePermutation_sign p hp hp2 a ha]
      simpa [eL, l0] using Equiv.Perm.sign_swap hcd
    have hi0χ : χ i0.1 = -1 := by
      change Equiv.Perm.sign i0.1.1 = -1
      rw [__ch5_proposition_5_2_6_fixedPointPermutation_sign a]
      simpa [eI, i0] using Equiv.Perm.sign_swap huv
    have hl02 : l0.1 ^ 2 = 1 := by
      have h : l0 ^ 2 = 1 := by
        apply eL.injective
        simp [l0, pow_two]
      exact congrArg Subtype.val h
    have hi02 : i0.1 ^ 2 = 1 := by
      have h : i0 ^ 2 = 1 := by
        apply eI.injective
        simp [i0, pow_two]
      exact congrArg Subtype.val h
    let tZ : Z := ⟨i0.1 * l0.1, by
      rw [MonoidHom.mem_ker, map_mul, hi0χ, hl0χ]
      norm_num⟩
    let tbar : alternatingGroup (Fin n) := φ tZ
    have hdecompZ := __ch5_proposition_5_2_6_signKernel_decomp_with_odd_pair χ R L I hRχ
      hLnorm hIcomm hsup l0.1 i0.1 l0.2 i0.2 hl0χ hi0χ hl02 hi02
    have hdecomp : F = (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar := by
      rw [← hφrange, φ.range_eq_map, ← Subgroup.map_sup,
        ← MonoidHom.map_zpowers, ← Subgroup.map_sup, hdecompZ.1]
    have ht2 : tbar ^ 2 = 1 := by
      exact map_pow φ tZ 2 ▸ congrArg φ hdecompZ.2
    have hindices :
        (H1bar.subgroupOf (H1bar ⊔ Subgroup.zpowers tbar)).index = 2 ∧
        (H2bar.subgroupOf (H2bar ⊔ Subgroup.zpowers tbar)).index = 2 := by
      have ht2Z : tZ ^ 2 = 1 := by
        apply Subtype.ext
        exact congrArg Subtype.val hdecompZ.2
      have htinv : tZ⁻¹ = tZ := by
        apply inv_eq_of_mul_eq_one_right
        simpa [pow_two] using ht2Z
      have hH1le : H1Z ≤ (R ⊔ L).comap Z.subtype := by
        apply sup_le
        · intro z hz
          exact (le_sup_left : R ≤ R ⊔ L) hz
        · intro z hz
          exact (le_sup_right : L ≤ R ⊔ L) hz
      have htNotH1 : tZ ∉ H1Z := by
        intro ht
        have htRL : tZ.1 ∈ R ⊔ L := hH1le ht
        have hlRL : l0.1 ∈ R ⊔ L :=
          (le_sup_right : L ≤ R ⊔ L) l0.2
        have hiRL : i0.1 ∈ R ⊔ L := by
          have heq : i0.1 = tZ.1 * (l0.1)⁻¹ := by
            dsimp [tZ]
            group
          rw [heq]
          exact (R ⊔ L).mul_mem htRL ((R ⊔ L).inv_mem hlRL)
        have hiBot : i0.1 ∈ (⊥ : Subgroup C) := by
          rw [← (theorem_5_2_2_d_1 x hxprime).2.2.1]
          exact ⟨i0.2, hiRL⟩
        have hiOne : i0.1 = 1 := by simpa using hiBot
        rw [hiOne, map_one] at hi0χ
        norm_num at hi0χ
      have htNotI : tZ ∉ IZ := by
        intro ht
        have htI : tZ.1 ∈ I := ht
        have hlI : l0.1 ∈ I := by
          have heq : l0.1 = (i0.1)⁻¹ * tZ.1 := by
            dsimp [tZ]
            group
          rw [heq]
          exact I.mul_mem (I.inv_mem i0.2) htI
        have hlRL : l0.1 ∈ R ⊔ L :=
          (le_sup_right : L ≤ R ⊔ L) l0.2
        have hlBot : l0.1 ∈ (⊥ : Subgroup C) := by
          rw [← (theorem_5_2_2_d_1 x hxprime).2.2.1]
          exact ⟨hlI, hlRL⟩
        have hlOne : l0.1 = 1 := by simpa using hlBot
        rw [hlOne, map_one] at hl0χ
        norm_num at hl0χ
      have hdoubleConj (z : Z) :
          tZ * (tZ * z * tZ⁻¹) * tZ⁻¹ = z := by
        rw [htinv]
        calc
          tZ * (tZ * z * tZ) * tZ =
              (tZ * tZ) * z * (tZ * tZ) := by group
          _ = z := by
            rw [← pow_two, ht2Z]
            simp
      have htNormRZ : tZ ∈ Subgroup.normalizer RZ := by
        have hforward : ∀ z : Z, z ∈ RZ →
            tZ * z * tZ⁻¹ ∈ RZ := by
          intro z hz
          have hlConj : l0.1 * z.1 * (l0.1)⁻¹ ∈ R :=
            ((Subgroup.mem_normalizer_iff.mp (hLnorm l0.2) z.1).mp hz)
          have hiComm : Commute i0.1
              (l0.1 * z.1 * (l0.1)⁻¹) := by
            have hiC := hIcomm i0.2
            rw [Subgroup.mem_centralizer_iff] at hiC
            exact (hiC _ ((le_sup_left : R ≤ R ⊔ L) hlConj)).symm
          change (tZ * z * tZ⁻¹).1 ∈ R
          have heq : (tZ * z * tZ⁻¹).1 =
              l0.1 * z.1 * (l0.1)⁻¹ := by
            dsimp [tZ]
            calc
              (i0.1 * l0.1) * z.1 * (i0.1 * l0.1)⁻¹ =
                  i0.1 * (l0.1 * z.1 * (l0.1)⁻¹) * (i0.1)⁻¹ := by
                group
              _ = l0.1 * z.1 * (l0.1)⁻¹ := by
                rw [hiComm.eq]
                group
          rw [heq]
          exact hlConj
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · exact hforward z
        · intro hz
          have hz' := hforward (tZ * z * tZ⁻¹) hz
          rwa [hdoubleConj z] at hz'
      have htNormLZ : tZ ∈ Subgroup.normalizer LZ := by
        have hforward : ∀ z : Z, z ∈ LZ →
            tZ * z * tZ⁻¹ ∈ LZ := by
          intro z hz
          have hlConj : l0.1 * z.1 * (l0.1)⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem l0.2 hz) (L.inv_mem l0.2)
          have hiComm : Commute i0.1
              (l0.1 * z.1 * (l0.1)⁻¹) := by
            have hiC := hIcomm i0.2
            rw [Subgroup.mem_centralizer_iff] at hiC
            exact (hiC _ ((le_sup_right : L ≤ R ⊔ L) hlConj)).symm
          change (tZ * z * tZ⁻¹).1 ∈ L
          have heq : (tZ * z * tZ⁻¹).1 =
              l0.1 * z.1 * (l0.1)⁻¹ := by
            dsimp [tZ]
            calc
              (i0.1 * l0.1) * z.1 * (i0.1 * l0.1)⁻¹ =
                  i0.1 * (l0.1 * z.1 * (l0.1)⁻¹) * (i0.1)⁻¹ := by
                group
              _ = l0.1 * z.1 * (l0.1)⁻¹ := by
                rw [hiComm.eq]
                group
          rw [heq]
          exact hlConj
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · exact hforward z
        · intro hz
          have hz' := hforward (tZ * z * tZ⁻¹) hz
          rwa [hdoubleConj z] at hz'
      have htNormH1 : tZ ∈ Subgroup.normalizer H1Z :=
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup RZ LZ)
          ⟨htNormRZ, htNormLZ⟩
      have htNormI : tZ ∈ Subgroup.normalizer IZ := by
        have hforward : ∀ z : Z, z ∈ IZ →
            tZ * z * tZ⁻¹ ∈ IZ := by
          intro z hz
          have hlComm : Commute l0.1 z.1 := by
            have hzC := hIcomm hz
            rw [Subgroup.mem_centralizer_iff] at hzC
            exact hzC l0.1 ((le_sup_right : L ≤ R ⊔ L) l0.2)
          have hiConj : i0.1 * z.1 * (i0.1)⁻¹ ∈ I :=
            I.mul_mem (I.mul_mem i0.2 hz) (I.inv_mem i0.2)
          change (tZ * z * tZ⁻¹).1 ∈ I
          have heq : (tZ * z * tZ⁻¹).1 =
              i0.1 * z.1 * (i0.1)⁻¹ := by
            dsimp [tZ]
            calc
              (i0.1 * l0.1) * z.1 * (i0.1 * l0.1)⁻¹ =
                  i0.1 * (l0.1 * z.1 * (l0.1)⁻¹) * (i0.1)⁻¹ := by
                group
              _ = i0.1 * z.1 * (i0.1)⁻¹ := by
                rw [hlComm.eq]
                group
          rw [heq]
          exact hiConj
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · exact hforward z
        · intro hz
          have hz' := hforward (tZ * z * tZ⁻¹) hz
          rwa [hdoubleConj z] at hz'
      have hidxH1 := __ch5_proposition_5_2_6_index_adjoin_involution_eq_two H1Z tZ
        ht2Z htNotH1 htNormH1
      have hidxI := __ch5_proposition_5_2_6_index_adjoin_involution_eq_two IZ tZ
        ht2Z htNotI htNormI
      constructor
      · change H1bar.relIndex
          (H1bar ⊔ Subgroup.zpowers tbar) = 2
        rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup,
          Subgroup.relIndex_map_map_of_injective H1Z
            (H1Z ⊔ Subgroup.zpowers tZ) hφinj]
        exact hidxH1
      · change H2bar.relIndex
          (H2bar ⊔ Subgroup.zpowers tbar) = 2
        rw [← MonoidHom.map_zpowers, ← Subgroup.map_sup,
          Subgroup.relIndex_map_map_of_injective IZ
            (IZ ⊔ Subgroup.zpowers tZ) hφinj]
        exact hidxI
    refine ⟨Rbar, Lbar, H1bar, H2bar, tbar, hdecomp, hH1eq,
      hnormal, hdisjoint, hcommute, hfaithful, hRbarEquiv, hLbarEquiv,
      hH2barEquiv, ht2, ?_, ?_⟩
    · intro hsmall
      exfalso
      rcases hsmall with hs | hr
      · have hs' : Fintype.card (Function.fixedPoints x) ≤ 1 := by
          simpa [x] using hs
        omega
      · have hr' : Fintype.card x.cycleFactorsFinset = 1 := by
          simpa [x] using hr
        omega
    · intro _
      exact hindices
  · have hno : ¬ ((∃ l ∈ L, χ l = -1) ∧ (∃ i ∈ I, χ i = -1)) := by
      rintro ⟨⟨l, hl, hlχ⟩, ⟨i, hi, hiχ⟩⟩
      apply hrs
      constructor
      · by_contra hcard
        have hle : Fintype.card x.cycleFactorsFinset ≤ 1 := by omega
        let lL : L := ⟨l, hl⟩
        let eL := theorem_5_2_2_d_3_a (a : Equiv.Perm (Fin n))
          (by simpa [x] using hxprime)
        have : Subsingleton x.cycleFactorsFinset :=
          Fintype.card_le_one_iff_subsingleton.mp hle
        have hperm : eL lL = 1 := Subsingleton.elim _ _
        have hsign : χ l = 1 := by
          change Equiv.Perm.sign l.1 = 1
          rw [show Equiv.Perm.sign l.1 = Equiv.Perm.sign (eL lL) by
            simpa [x, lL, eL] using __ch5_proposition_5_2_6_cyclePermutation_sign p hp hp2 a ha lL]
          rw [hperm]
          simp
        rw [hsign] at hlχ
        norm_num at hlχ
      · by_contra hcard
        have hle : Fintype.card (Function.fixedPoints x) ≤ 1 := by omega
        let iI : I := ⟨i, hi⟩
        let eI := theorem_5_2_2_d_4 (a : Equiv.Perm (Fin n))
        have : Subsingleton (Function.fixedPoints x) :=
          Fintype.card_le_one_iff_subsingleton.mp hle
        have hperm : eI iI = 1 := by
          apply Subsingleton.elim
        have hsign : χ i = 1 := by
          change Equiv.Perm.sign i.1 = 1
          rw [show Equiv.Perm.sign i.1 = Equiv.Perm.sign (eI iI) by
            simpa [x, iI, eI] using __ch5_proposition_5_2_6_fixedPointPermutation_sign a iI]
          rw [hperm]
          simp
        rw [hsign] at hiχ
        norm_num at hiχ
    have hdecompZ := __ch5_proposition_5_2_6_signKernel_decomp_no_odd_pair χ R L I hRχ
      hLnorm hIcomm hsup hno
    have hdecomp : F = (H1bar ⊔ H2bar) ⊔
        Subgroup.zpowers (1 : alternatingGroup (Fin n)) := by
      rw [Subgroup.zpowers_one_eq_bot, sup_bot_eq, ← hφrange, φ.range_eq_map,
        ← Subgroup.map_sup, hdecompZ]
    refine ⟨Rbar, Lbar, H1bar, H2bar, 1, hdecomp, hH1eq,
      hnormal, hdisjoint, hcommute, hfaithful, hRbarEquiv, hLbarEquiv,
      hH2barEquiv, by simp, by simp, ?_⟩
    intro hlarge
    exact False.elim (hrs ⟨hlarge.2, hlarge.1⟩)

/-- Proposition 5.2.6(a): an odd-prime-order automorphism of an alternating
quasisimple covering group is inner, represented by an element of the same
order. -/
public theorem proposition_5_2_6_a
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hp2 : p ≠ 2) :
    ∃ y : K, orderOf y = p ∧ x = MulAut.conj y := by
  let a : alternatingGroup (Fin n) :=
    Classical.choose (__ch5_proposition_5_2_6_oddPrimeOrder_alternatingAut_is_inner
      n p hn hp hp2 quotientAction
        (quotientAction_order hp quotientEquiv x hx quotientAction
          quotientAction_compat))
  have haction : quotientAction =
      MulAut.conjNormal (a : Equiv.Perm (Fin n)) :=
    Classical.choose_spec (__ch5_proposition_5_2_6_oddPrimeOrder_alternatingAut_is_inner
      n p hn hp hp2 quotientAction
        (quotientAction_order hp quotientEquiv x hx quotientAction
          quotientAction_compat))
  have hconjInj :=
    GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup
      n ((by omega : 4 ≤ 5).trans hn)
  have ha : orderOf a = p := by
    calc
      orderOf a = orderOf (a : Equiv.Perm (Fin n)) :=
        (Subgroup.orderOf_coe a).symm
      _ = orderOf (MulAut.conjNormal
            (H := alternatingGroup (Fin n))
            (a : Equiv.Perm (Fin n))) :=
        (orderOf_injective _ hconjInj
          (a : Equiv.Perm (Fin n))).symm
      _ = orderOf quotientAction := congrArg orderOf haction.symm
      _ = p := quotientAction_order hp quotientEquiv x hx quotientAction
        quotientAction_compat
  obtain ⟨y, hy, hyOrder⟩ : ∃ y : K,
      (alternatingQuotientHom quotientEquiv) y = a ∧ orderOf y = p := by
    by_cases hp3 : p = 3
    · obtain ⟨y, hy, hy3⟩ := __ch5_proposition_5_2_6_exists_order_three_lift_central_alternating
        n hn (alternatingQuotientHom quotientEquiv)
        (alternatingQuotientHom_surjective quotientEquiv)
        (by rw [alternatingQuotientHom_ker quotientEquiv])
        a (by simpa [hp3] using ha)
      exact ⟨y, hy, by simpa [hp3] using hy3⟩
    · have hnotdiv :=
        __ch5_proposition_5_2_6_prime_ne_three_not_dvd_center n p hn hp quotientEquiv hp2 hp3
      have hcop : Nat.Coprime
          (Nat.card (alternatingQuotientHom quotientEquiv).ker) p := by
        rw [alternatingQuotientHom_ker quotientEquiv]
        exact Nat.coprime_comm.mp
          (hp.coprime_iff_not_dvd.mpr hnotdiv)
      exact __ch5_proposition_5_2_6_exists_order_prime_lift_of_coprime_kernel
        p hp (alternatingQuotientHom quotientEquiv)
          (alternatingQuotientHom_surjective quotientEquiv) hcop a ha
  have hhom : x.toMonoidHom = (MulAut.conj y).toMonoidHom := by
    apply SchurPresentation.monoidHom_eq_of_isPerfect_of_comp_eq
      (alternatingQuotientHom quotientEquiv)
      (by rw [alternatingQuotientHom_ker quotientEquiv])
    apply MonoidHom.ext
    intro k
    change (alternatingQuotientHom quotientEquiv) (x k) =
      (alternatingQuotientHom quotientEquiv) (y * k * y⁻¹)
    calc
      (alternatingQuotientHom quotientEquiv) (x k) =
          quotientAction ((alternatingQuotientHom quotientEquiv) k) :=
        quotientAction_compat k
      _ = a * (alternatingQuotientHom quotientEquiv) k * a⁻¹ := by rw [haction]; rfl
      _ = (alternatingQuotientHom quotientEquiv) (y * k * y⁻¹) := by
        rw [map_mul, map_mul, map_inv, hy]
  have hx : x = MulAut.conj y := by
    apply MulEquiv.ext
    intro k
    exact DFunLike.congr_fun hhom k
  exact ⟨y, hyOrder, hx⟩

-- Preserve the named source hypotheses in this public interface.
set_option linter.unusedVariables false in
/-- Proposition 5.2.6(b): the centralizer in `Aₙ` of an odd-prime-order
element has the cycle-rotation, cycle-permutation, fixed-point, and parity
extension structure described in the printed proposition. -/
public theorem proposition_5_2_6_b
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hxOrder : orderOf x = p)
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hp2 : p ≠ 2)
    (y : K) (hy : orderOf y = p) (hx : x = MulAut.conj y) :
    let ybar := quotientEquiv
      (QuotientGroup.mk' (Subgroup.center K) y)
    let r := Fintype.card ybar.1.cycleFactorsFinset
    let s := Fintype.card (Function.fixedPoints ybar.1)
    ∃ (Rbar Lbar H1bar H2bar : Subgroup
        (alternatingGroup (Fin n)))
      (tbar : alternatingGroup (Fin n)),
      automorphismFixedSubgroup (MulAut.conj ybar) =
          (H1bar ⊔ H2bar) ⊔ Subgroup.zpowers tbar ∧
        H1bar = Rbar ⊔ Lbar ∧
        (Rbar.subgroupOf H1bar).Normal ∧
        Disjoint H1bar H2bar ∧
        (∀ a : ↥H1bar, ∀ b : ↥H2bar, Commute a.1 b.1) ∧
        Disjoint Lbar
          (Subgroup.centralizer
            (Rbar : Set (alternatingGroup (Fin n)))) ∧
        Nonempty (↥Rbar ≃* Multiplicative (Fin r → ZMod p)) ∧
        Nonempty (↥Lbar ≃* alternatingGroup (Fin r)) ∧
        (∃ eH2 : ↥H2bar ≃* alternatingGroup (Fin s),
          ∀ u : H2bar, (eH2 u).1.support.card = u.1.1.support.card) ∧
        tbar ^ 2 = 1 ∧
        ((s ≤ 1 ∨ r = 1) → tbar = 1) ∧
         ((2 ≤ s ∧ 2 ≤ r) →
          (H1bar.subgroupOf (H1bar ⊔ Subgroup.zpowers tbar)).index = 2 ∧
          (H2bar.subgroupOf (H2bar ⊔ Subgroup.zpowers tbar)).index = 2) := by
  dsimp only
  let ybar : alternatingGroup (Fin n) := quotientEquiv
    (QuotientGroup.mk' (Subgroup.center K) y)
  have haction : quotientAction = MulAut.conj ybar := by
    apply MulEquiv.ext
    intro a
    obtain ⟨k, rfl⟩ := alternatingQuotientHom_surjective quotientEquiv a
    calc
      quotientAction ((alternatingQuotientHom quotientEquiv) k) =
          (alternatingQuotientHom quotientEquiv) (x k) :=
        (quotientAction_compat k).symm
      _ = (alternatingQuotientHom quotientEquiv) (y * k * y⁻¹) := by
        exact congrArg (alternatingQuotientHom quotientEquiv)
          (DFunLike.congr_fun hx k)
      _ = ybar * (alternatingQuotientHom quotientEquiv) k * ybar⁻¹ := by
        rw [map_mul, map_mul, map_inv]
        rfl
      _ = MulAut.conj ybar ((alternatingQuotientHom quotientEquiv) k) := rfl
  have hconjInj :=
    GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup
      n ((by omega : 4 ≤ 5).trans hn)
  have hybarOrder : orderOf ybar = p := by
    calc
      orderOf ybar = orderOf (ybar : Equiv.Perm (Fin n)) :=
        (Subgroup.orderOf_coe ybar).symm
      _ = orderOf (MulAut.conjNormal
            (H := alternatingGroup (Fin n))
            (ybar : Equiv.Perm (Fin n))) :=
        (orderOf_injective _ hconjInj
          (ybar : Equiv.Perm (Fin n))).symm
      _ = orderOf quotientAction := congrArg orderOf haction.symm
      _ = p := quotientAction_order hp quotientEquiv x hxOrder quotientAction
        quotientAction_compat
  simpa [ybar] using alternatingPrimeCentralizerStructure
    n p hp hp2 ybar hybarOrder

/-- Proposition 5.2.6(c): an odd-prime-order element of `Aₙ` centralizes an
odd permutation precisely when `n > p + 1`. -/
public theorem proposition_5_2_6_c
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime)
    (quotientEquiv : K ⧸ Subgroup.center K ≃*
      alternatingGroup (Fin n))
    (x : MulAut K) (hx : orderOf x = p)
    (H : Subgroup (MulAut K))
    (HEquiv : H ≃* Equiv.Perm (Fin n))
    (quotientAction : MulAut (alternatingGroup (Fin n)))
    (quotientAction_compat : ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (x k)) =
        quotientAction
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (H_action_compat : ∀ h : H, ∀ k : K,
      quotientEquiv (QuotientGroup.mk' (Subgroup.center K) (h.1 k)) =
        MulAut.conjNormal (HEquiv h)
          (quotientEquiv (QuotientGroup.mk' (Subgroup.center K) k)))
    (hp2 : p ≠ 2) :
    (∃ h : H, Equiv.Perm.sign (HEquiv h) = -1 ∧
      Commute h.1 x) ↔ p + 1 < n := by
  let a : alternatingGroup (Fin n) :=
    Classical.choose (__ch5_proposition_5_2_6_oddPrimeOrder_alternatingAut_is_inner
      n p hn hp hp2 quotientAction
        (quotientAction_order hp quotientEquiv x hx quotientAction
          quotientAction_compat))
  have haction : quotientAction =
      MulAut.conjNormal (a : Equiv.Perm (Fin n)) :=
    Classical.choose_spec (__ch5_proposition_5_2_6_oddPrimeOrder_alternatingAut_is_inner
      n p hn hp hp2 quotientAction
        (quotientAction_order hp quotientEquiv x hx quotientAction
          quotientAction_compat))
  have hconjInj :=
    GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup
      n ((by omega : 4 ≤ 5).trans hn)
  have ha : orderOf a = p := by
    calc
      orderOf a = orderOf (a : Equiv.Perm (Fin n)) :=
        (Subgroup.orderOf_coe a).symm
      _ = orderOf (MulAut.conjNormal
            (H := alternatingGroup (Fin n))
            (a : Equiv.Perm (Fin n))) :=
        (orderOf_injective _ hconjInj
          (a : Equiv.Perm (Fin n))).symm
      _ = orderOf quotientAction := congrArg orderOf haction.symm
      _ = p := quotientAction_order hp quotientEquiv x hx quotientAction
        quotientAction_compat
  constructor
  · rintro ⟨h, hsign, hcomm⟩
    apply (__ch5_proposition_5_2_6_exists_odd_centralizer_iff
      n p hp hp2 a ha).mp
    refine ⟨HEquiv h, hsign, ?_⟩
    apply hconjInj
    have hquot := (__ch5_proposition_5_2_6_commute_iff_quotient_commute quotientEquiv x H HEquiv
      quotientAction quotientAction_compat H_action_compat h).mp hcomm
    simpa [map_mul, ← haction] using hquot.eq
  · intro hbound
    obtain ⟨σ, hsign, hcomm⟩ := (__ch5_proposition_5_2_6_exists_odd_centralizer_iff
      n p hp hp2 a ha).mpr hbound
    let h : H := HEquiv.symm σ
    refine ⟨h, ?_, ?_⟩
    · simpa [h] using hsign
    · apply (__ch5_proposition_5_2_6_commute_iff_quotient_commute quotientEquiv x H HEquiv
        quotientAction quotientAction_compat H_action_compat h).mpr
      simpa [h, ← haction] using hcomm.map
        (MulAut.conjNormal (H := alternatingGroup (Fin n)))

private theorem __ch5_proposition_5_2_6_alternatingHom_eq_one_of_sq_eq_one
    {α C : Type*} [Fintype α] [DecidableEq α] [Group C]
    (ψ : alternatingGroup α →* C) (h2 : ∀ c : C, c ^ 2 = 1) :
    ψ = 1 := by
  apply MonoidHom.ext
  intro a
  have ha : a ∈ Subgroup.closure
      {g : alternatingGroup α |
        Equiv.Perm.IsThreeCycle (g : Equiv.Perm α)} := by
    rw [alternatingGroup.closure_isThreeCycles_eq_top]
    trivial
  refine Subgroup.closure_induction (p := fun x _ ↦ ψ x = 1) ?_ ?_ ?_ ?_ ha
  · intro x hx
    have hxpow : (x : Equiv.Perm α) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (x : Equiv.Perm α)
      rw [hx.orderOf] at h
      exact h
    have hxpow' : x ^ 3 = 1 := Subtype.ext hxpow
    have hψ3 : ψ x ^ 3 = 1 := by rw [← map_pow, hxpow', map_one]
    calc
      ψ x = ψ x ^ 3 := by
        rw [show (3 : Nat) = 2 + 1 by omega, pow_add, h2]
        simp
      _ = 1 := hψ3
  · simp
  · intro x y _ _ hx hy
    simp [map_mul, hx, hy]
  · intro x _ hx
    simp [map_inv, hx]

private theorem __ch5_proposition_5_2_6_odd_sq_pow_eq_one
    {C : Type*} [Group C] {p : Nat} (hpodd : Odd p)
    {c : C} (hc2 : c ^ 2 = 1) (hcp : c ^ p = 1) : c = 1 := by
  rcases hpodd with ⟨k, hk⟩
  rw [hk, pow_add, pow_mul, hc2] at hcp
  simpa using hcp

private theorem __ch5_proposition_5_2_6_hom_eq_one_of_surjective_of_quotient_hom_eq_one
    {P M C : Type*} [Group P] [Group M] [Group C]
    (q : P →* M) (hq : Function.Surjective q)
    (φ : P →* C) (hker : q.ker ≤ φ.ker)
    (htrivial : ∀ ψ : M →* C, ψ = 1) : φ = 1 := by
  let ψQ : P ⧸ q.ker →* C := QuotientGroup.lift q.ker φ hker
  let eQ : P ⧸ q.ker ≃* M :=
    QuotientGroup.quotientKerEquivOfSurjective q hq
  let ψM : M →* C := ψQ.comp eQ.symm.toMonoidHom
  have hψM : ψM = 1 := htrivial ψM
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hψM (q x)
  have he : eQ.symm (q x) = QuotientGroup.mk' q.ker x := by
    rw [MulEquiv.symm_apply_eq]
    change q x = QuotientGroup.kerLift q (QuotientGroup.mk' q.ker x)
    exact (QuotientGroup.kerLift_mk q x).symm
  change ψQ (eQ.symm (q x)) = 1 at hx
  rw [he] at hx
  dsimp [ψQ] at hx
  simpa using hx

private theorem __ch5_proposition_5_2_6_zmodPi_multiplicative_pow_prime
    (p r : Nat) [Fact p.Prime]
    (v : Multiplicative (Fin r → ZMod p)) : v ^ p = 1 := by
  apply (Multiplicative.toAdd : Multiplicative (Fin r → ZMod p) ≃
    (Fin r → ZMod p)).injective
  ext i
  change p • Multiplicative.toAdd v i = 0
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod p),
    CharP.cast_eq_zero (ZMod p) p]
  simp

private theorem __ch5_proposition_5_2_6_oddAlternatingSupHom_eq_one
    {G C : Type*} [Group G] [Group C]
    (p r : Nat) [Fact p.Prime] (hpodd : Odd p)
    (R L A : Subgroup G) (hA : A = R ⊔ L)
    (eR : R ≃* Multiplicative (Fin r → ZMod p))
    (eL : L ≃* alternatingGroup (Fin r))
    (ψ : A →* C) (h2 : ∀ c : C, c ^ 2 = 1) : ψ = 1 := by
  have hRle : R ≤ A := by rw [hA]; exact le_sup_left
  have hLle : L ≤ A := by rw [hA]; exact le_sup_right
  let iR : R →* A := R.subtype.codRestrict A (fun x => hRle x.2)
  let iL : L →* A := L.subtype.codRestrict A (fun x => hLle x.2)
  let ψR : R →* C := ψ.comp iR
  let ψL : L →* C := ψ.comp iL
  have hψR : ψR = 1 := by
    apply __ch5_proposition_5_2_6_hom_eq_one_of_surjective_of_quotient_hom_eq_one
      eR.toMonoidHom eR.surjective ψR
    · intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      have hx1 : x = 1 := by
        apply eR.injective
        simpa using hx
      simp [hx1]
    · intro ψM
      apply MonoidHom.ext
      intro m
      apply __ch5_proposition_5_2_6_odd_sq_pow_eq_one hpodd (h2 (ψM m))
      rw [← map_pow, __ch5_proposition_5_2_6_zmodPi_multiplicative_pow_prime p r, map_one]
  have hψL : ψL = 1 := by
    apply __ch5_proposition_5_2_6_hom_eq_one_of_surjective_of_quotient_hom_eq_one
      eL.toMonoidHom eL.surjective ψL
    · intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      have hx1 : x = 1 := by
        apply eL.injective
        simpa using hx
      simp [hx1]
    · intro ψA
      exact __ch5_proposition_5_2_6_alternatingHom_eq_one_of_sq_eq_one ψA h2
  have hRker : R ≤ ψ.ker.map A.subtype := by
    intro x hx
    let xR : R := ⟨x, hx⟩
    let xA : A := ⟨x, hRle hx⟩
    refine ⟨xA, ?_, rfl⟩
    change ψ xA = 1
    have h := DFunLike.congr_fun hψR xR
    simpa [ψR, iR, xR, xA] using h
  have hLker : L ≤ ψ.ker.map A.subtype := by
    intro x hx
    let xL : L := ⟨x, hx⟩
    let xA : A := ⟨x, hLle hx⟩
    refine ⟨xA, ?_, rfl⟩
    change ψ xA = 1
    have h := DFunLike.congr_fun hψL xL
    simpa [ψL, iL, xL, xA] using h
  apply MonoidHom.ext
  intro x
  have hx : x.1 ∈ ψ.ker.map A.subtype := by
    apply (sup_le hRker hLker)
    rw [← hA]
    exact x.2
  rcases hx with ⟨z, hz, hzx⟩
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact MonoidHom.mem_ker.mp hz

private def __ch5_proposition_5_2_6_centralCommutatorHom
    {P K : Type*} [Group P] [Group K]
    (s : P →* K) (b : K)
    (hc : ∀ a : P, ⁅s a, b⁆ ∈ Subgroup.center K) :
    P →* Subgroup.center K where
  toFun a := ⟨⁅s a, b⁆, hc a⟩
  map_one' := by ext; simp
  map_mul' a₁ a₂ := by
    apply Subtype.ext
    change ⁅s (a₁ * a₂), b⁆ = ⁅s a₁, b⁆ * ⁅s a₂, b⁆
    rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
    have hc₂ := hc a₂
    have hconj : s a₁ * ⁅s a₂, b⁆ * (s a₁)⁻¹ = ⁅s a₂, b⁆ := by
      have hcomm := Subgroup.mem_center_iff.mp hc₂ (s a₁)
      rw [hcomm]
      simp
    rw [hconj]
    exact (Subgroup.mem_center_iff.mp hc₂ ⁅s a₁, b⁆).symm

/-- Proposition 5.2.6(d)(1): the full preimages of the moving-cycle factor
and the fixed-point factor commute.  The proof factors the lift commutator
through `R ⋊ Aᵣ`; odd exponent and three-cycle generation force it to vanish. -/
public theorem proposition_5_2_6_d_1
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hp : p.Prime)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (hp2 : p ≠ 2)
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (r : Nat)
    (Rbar Lbar H1bar H2bar : Subgroup (alternatingGroup (Fin n)))
    (hH1 : H1bar = Rbar ⊔ Lbar)
    (hcomm : ∀ a : H1bar, ∀ b : H2bar, Commute a.1 b.1)
    (eR : Nonempty (Rbar ≃* Multiplicative (Fin r → ZMod p)))
    (eL : Nonempty (Lbar ≃* alternatingGroup (Fin r))) :
    ∀ a : ↥(H1bar.comap f.toMonoidHom),
      ∀ b : ↥(H2bar.comap f.toMonoidHom), Commute a.1 b.1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact (hp2 h2).elim
    · exact Nat.odd_iff.mpr hodd
  obtain ⟨eR⟩ := eR
  obtain ⟨eL⟩ := eL
  intro a b
  let P := H1bar.comap f.toMonoidHom
  let q : P →* H1bar :=
    (f.toMonoidHom.comp P.subtype).codRestrict H1bar (fun x => x.2)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨k, hk⟩ := f.surjective x.1
    have hkP : k ∈ P := by
      have hxmem := x.2
      change (x.1 : alternatingGroup (Fin n)) ∈ H1bar at hxmem
      rw [← hk] at hxmem
      exact hxmem
    refine ⟨⟨k, hkP⟩, ?_⟩
    apply Subtype.ext
    change f k = x.1
    exact hk
  have hcKer : ∀ x : P, ⁅x.1, b.1⁆ ∈ f.toMonoidHom.ker := by
    intro x
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    exact hcomm ⟨f x.1, x.2⟩ ⟨f b.1, b.2⟩
  have hcCenter : ∀ x : P, ⁅x.1, b.1⁆ ∈ Subgroup.center K :=
    fun x => f.ker_le_center (hcKer x)
  let φZ : P →* Subgroup.center K :=
    __ch5_proposition_5_2_6_centralCommutatorHom P.subtype b.1 hcCenter
  let φ : P →* f.toMonoidHom.ker := {
    toFun := fun x => ⟨(φZ x).1, hcKer x⟩
    map_one' := by
      apply Subtype.ext
      change (φZ 1).1 = 1
      exact congrArg Subtype.val (map_one φZ)
    map_mul' := by
      intro x y
      apply Subtype.ext
      change (φZ (x * y)).1 = (φZ x).1 * (φZ y).1
      exact congrArg Subtype.val (map_mul φZ x y) }
  have hqker : q.ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    apply Subtype.ext
    change ⁅x.1, b.1⁆ = 1
    apply commutatorElement_eq_one_iff_commute.mpr
    have hfx : f x.1 = 1 := by
      have h := congrArg Subtype.val hx
      change f x.1 = 1 at h
      exact h
    have hxker : x.1 ∈ f.toMonoidHom.ker := MonoidHom.mem_ker.mpr hfx
    exact (show Commute b.1 x.1 from
      Subgroup.mem_center_iff.mp (f.ker_le_center hxker) b.1).symm
  have hpow2 : ∀ z : f.toMonoidHom.ker, z ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    exact SchurPresentation.DoubleCoverUniqueness.ker_pow_two_eq_one
      f.toMonoidHom hker z.2
  let ψQ : P ⧸ q.ker →* f.toMonoidHom.ker :=
    QuotientGroup.lift q.ker φ hqker
  let eQ : P ⧸ q.ker ≃* H1bar :=
    QuotientGroup.quotientKerEquivOfSurjective q hq
  let ψ : H1bar →* f.toMonoidHom.ker := ψQ.comp eQ.symm.toMonoidHom
  have hψ : ψ = 1 :=
    __ch5_proposition_5_2_6_oddAlternatingSupHom_eq_one p r hpodd Rbar Lbar H1bar hH1 eR eL ψ hpow2
  have hφ : φ = 1 := by
    apply MonoidHom.ext
    intro x
    have hx := DFunLike.congr_fun hψ (q x)
    have he : eQ.symm (q x) = QuotientGroup.mk' q.ker x := by
      rw [MulEquiv.symm_apply_eq]
      change q x = QuotientGroup.kerLift q (QuotientGroup.mk' q.ker x)
      exact (QuotientGroup.kerLift_mk q x).symm
    change ψQ (eQ.symm (q x)) = 1 at hx
    rw [he] at hx
    dsimp [ψQ] at hx
    simpa using hx
  apply commutatorElement_eq_one_iff_commute.mp
  have ha := DFunLike.congr_fun hφ a
  have haval := congrArg Subtype.val ha
  change ⁅a.1, b.1⁆ = 1 at haval
  exact haval

private def __ch5_proposition_5_2_6_rootFourPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

private theorem __ch5_proposition_5_2_6_rootFourPerm_sign : Equiv.Perm.sign __ch5_proposition_5_2_6_rootFourPerm = 1 := by
  all_goals decide
private theorem __ch5_proposition_5_2_6_rootFourPerm_order : orderOf __ch5_proposition_5_2_6_rootFourPerm = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

private theorem __ch5_proposition_5_2_6_rootFourPerm_support : __ch5_proposition_5_2_6_rootFourPerm.support.card = 4 := by
  all_goals decide
private def __ch5_proposition_5_2_6_firstFourEmbedding (m : Nat) (hm : 4 ≤ m) : Fin 4 ↪ Fin m where
  toFun i := ⟨i, by omega⟩
  inj' i j h := by
    apply Fin.eq_of_val_eq
    simpa using congrArg Fin.val h

private noncomputable def alternatingRootInvolution (m : Nat) (hm : 4 ≤ m) :
    alternatingGroup (Fin m) :=
  ⟨__ch5_proposition_5_2_6_rootFourPerm.viaEmbedding (__ch5_proposition_5_2_6_firstFourEmbedding m hm), by
    rw [Equiv.Perm.mem_alternatingGroup]
    dsimp [Equiv.Perm.viaEmbedding]
    rw [Equiv.Perm.sign_extendDomain]
    exact __ch5_proposition_5_2_6_rootFourPerm_sign⟩

private theorem __ch5_proposition_5_2_6_alternatingRootInvolution_order (m : Nat) (hm : 4 ≤ m) :
    orderOf (alternatingRootInvolution m hm) = 2 := by
  calc
    orderOf (alternatingRootInvolution m hm) =
        orderOf ((alternatingRootInvolution m hm : alternatingGroup (Fin m)) :
          Equiv.Perm (Fin m)) := (Subgroup.orderOf_coe _).symm
    _ = orderOf __ch5_proposition_5_2_6_rootFourPerm := by
      change orderOf ((Equiv.Perm.viaEmbeddingHom (__ch5_proposition_5_2_6_firstFourEmbedding m hm))
        __ch5_proposition_5_2_6_rootFourPerm) = orderOf __ch5_proposition_5_2_6_rootFourPerm
      exact orderOf_injective _
        (Equiv.Perm.viaEmbeddingHom_injective (__ch5_proposition_5_2_6_firstFourEmbedding m hm)) __ch5_proposition_5_2_6_rootFourPerm
    _ = 2 := __ch5_proposition_5_2_6_rootFourPerm_order

private theorem __ch5_proposition_5_2_6_alternatingRootInvolution_support (m : Nat) (hm : 4 ≤ m) :
    (alternatingRootInvolution m hm).1.support.card = 4 := by
  let emb := __ch5_proposition_5_2_6_firstFourEmbedding m hm
  have hsupport : (__ch5_proposition_5_2_6_rootFourPerm.viaEmbedding emb).support =
      __ch5_proposition_5_2_6_rootFourPerm.support.map emb := by
    ext y
    by_cases hy : y ∈ Set.range emb
    · obtain ⟨x, rfl⟩ := hy
      rw [Equiv.Perm.mem_support, Equiv.Perm.viaEmbedding_apply, Finset.mem_map]
      constructor
      · intro hx
        have hx' : __ch5_proposition_5_2_6_rootFourPerm x ≠ x := fun h => hx (congrArg emb h)
        exact ⟨x, by simpa [Equiv.Perm.mem_support] using hx', rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hzx' : z = x := emb.injective hzx
        subst z
        have hz' : __ch5_proposition_5_2_6_rootFourPerm x ≠ x := by
          simpa [Equiv.Perm.mem_support] using hz
        exact fun h => hz' (emb.injective h)
    · rw [Equiv.Perm.mem_support,
        Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hy, Finset.mem_map]
      constructor
      · intro h
        exact (h rfl).elim
      · rintro ⟨x, _, hxy⟩
        exact (hy ⟨x, hxy⟩).elim
  change (__ch5_proposition_5_2_6_rootFourPerm.viaEmbedding emb).support.card = 4
  rw [hsupport, Finset.card_map, __ch5_proposition_5_2_6_rootFourPerm_support]

private theorem __ch5_proposition_5_2_6_orderOf_eq_four_of_odd_quarter_support
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (x : K) (hxOrder : orderOf (f x) = 2)
    (m : Nat) (hmodd : Odd m)
    (hsupport : (f x).1.support.card = 4 * m) : orderOf x = 4 := by
  let qn := n - 5
  have hqn : qn + 5 = n := Nat.sub_add_cancel hn
  let : IsQuasisimple (alternatingGroup (Fin (qn + 5))) :=
    SchurPresentation.alternatingGroup_isQuasisimple qn
  let relabel : Fin n ≃ Fin (qn + 5) := finCongr hqn.symm
  let baseEquiv : alternatingGroup (Fin n) ≃*
      alternatingGroup (Fin (qn + 5)) := relabel.altCongrHom
  let fK : Covering K (alternatingGroup (Fin (qn + 5))) :=
    (Covering.ofMulEquiv baseEquiv).comp f
  have hfKkerEq : fK.toMonoidHom.ker = f.toMonoidHom.ker := by
    ext z
    simp [fK, baseEquiv]
  have hfKker : Nat.card fK.toMonoidHom.ker = 2 := by
    rw [hfKkerEq, hker]
  obtain ⟨e, he, _⟩ :=
    SchurPresentation.theorem_5_2_3_a_2 qn fK
      (SchurPresentation.schurAlternatingCovering qn) hfKker
      (SchurPresentation.natCard_ker_schurAlternatingCovering qn)
  let xS : SchurPresentation.SchurAlternatingGroup qn := e x
  have hxSproj : SchurPresentation.schurAlternatingProjection qn xS = fK x := by
    have h := DFunLike.congr_fun (congrArg Covering.toMonoidHom he) x
    change SchurPresentation.schurAlternatingProjection qn (e x) = fK x at h
    exact h
  have hxKOrder : orderOf (fK x) = 2 := by
    calc
      orderOf (fK x) = orderOf (baseEquiv (f x)) := rfl
      _ = orderOf (f x) := orderOf_injective baseEquiv.toMonoidHom
        baseEquiv.injective (f x)
      _ = 2 := hxOrder
  have hsupportK : (fK x).1.support.card = 4 * m := by
    calc
      (fK x).1.support.card =
          (relabel.permCongr (f x).1).support.card := by
            rw [show (fK x).1 = relabel.permCongr (f x).1 by rfl]
      _ = (f x).1.support.card := card_support_permCongr relabel (f x).1
      _ = 4 * m := hsupport
  have hmpos : 1 ≤ m := by rcases hmodd with ⟨k, rfl⟩; omega
  have hsuppLe : (fK x).1.support.card ≤ qn + 5 := by
    simpa using Finset.card_le_univ (fK x).1.support
  have h4m : 4 * m ≤ qn + 5 := by
    rw [← hsupportK]
    exact hsuppLe
  let y := SchurPresentation.canonicalLift qn m h4m
  let ybar := SchurPresentation.schurAlternatingProjection qn y
  have hxbarSq : (fK x).1 ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one (fK x)
    rw [hxKOrder] at hpow
    exact congrArg Subtype.val hpow
  have hybarSq : ybar.1 ^ 2 = 1 := by
    have hyOrder := SchurPresentation.canonicalLift_proj_order_two
      qn m h4m hmpos
    have hpow := pow_orderOf_eq_one ybar
    rw [hyOrder] at hpow
    exact congrArg Subtype.val hpow
  have hxbarNe : fK x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxKOrder
    norm_num at hxKOrder
  have hsupportEq : (fK x).1.support.card = ybar.1.support.card := by
    rw [show ybar.1 = SchurPresentation.canonicalPerm qn m h4m by
      exact SchurPresentation.canonicalLift_proj qn m h4m]
    rw [SchurPresentation.canonicalPerm_support_card qn m h4m]
    exact hsupportK
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (SchurPresentation.alternating_involution_isConj_of_card_support_eq
      hxbarSq hybarSq (by exact hxbarNe) hsupportEq)
  have hxSsq : xS ^ 2 = y ^ 2 := by
    apply SchurPresentation.DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
      (SchurPresentation.schurAlternatingCovering qn)
      (SchurPresentation.natCard_ker_schurAlternatingCovering qn)
      (x := xS) (y := y) (c := c)
    · change (SchurPresentation.schurAlternatingProjection qn xS) ^ 2 = 1
      rw [hxSproj]
      exact Subtype.ext hxbarSq
    · change c * SchurPresentation.schurAlternatingProjection qn xS * c⁻¹ =
        SchurPresentation.schurAlternatingProjection qn y
      simpa [hxSproj, ybar] using hc
  have hysq : y ^ 2 = SchurPresentation.schurAlternatingCentral qn := by
    rw [SchurPresentation.canonicalLift_sq]
    exact SchurPresentation.central_pow_of_odd qn hmodd
  have hxSsqNe : xS ^ 2 ≠ 1 := by
    rw [hxSsq, hysq]
    exact SchurPresentation.schurAlternatingCentral_ne_one qn
  have hxsqNe : x ^ 2 ≠ 1 := by
    intro hx
    apply hxSsqNe
    change e x ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have hxsqKer : x ^ 2 ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    have hpow := pow_orderOf_eq_one (f x)
    simpa [hxOrder] using hpow
  have hxfour : x ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 by norm_num, pow_mul]
    exact SchurPresentation.DoubleCoverUniqueness.ker_pow_two_eq_one
      f.toMonoidHom hker hxsqKer
  exact SchurPresentation.orderOf_eq_four_of_sq_ne_one_of_pow_four_eq_one
    x hxfour hxsqNe

private theorem __ch5_proposition_5_2_6_nonsplitDoubleExtension_alternating
    {E : Type*} [Group E] [Finite E]
    (m : Nat) (hm : 5 ≤ m)
    (q : E →* alternatingGroup (Fin m))
    (hq : Function.Surjective q)
    (hcenter : q.ker ≤ Subgroup.center E)
    (hcard : Nat.card q.ker = 2)
    (u : E) (huq : orderOf (q u) = 2) (hu : orderOf u = 4) :
    IsQuasisimple E ∧
      Nat.card (Subgroup.center E) = 2 ∧
      Nonempty (E ⧸ Subgroup.center E ≃* alternatingGroup (Fin m)) := by
  let : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by simpa using hm)
  have hmcard : 5 ≤ Nat.card (Fin m) := by simpa using hm
  let : Group.IsPerfect (alternatingGroup (Fin m)) :=
    ⟨commutator_alternatingGroup_eq_top hmcard⟩
  let D : Subgroup E := commutator E
  let qD : D →* alternatingGroup (Fin m) := q.comp D.subtype
  have hqD : Function.Surjective qD := by
    have hqrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hq
    have hmap : D.map q = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, hqrange]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map q := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hqDkerDvd : Nat.card qD.ker ∣ Nat.card q.ker := by
    change Nat.card (q.ker.comap D.subtype) ∣ Nat.card q.ker
    exact Subgroup.card_comap_dvd_of_injective q.ker D.subtype D.subtype_injective
  rw [hcard] at hqDkerDvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hqDkerDvd with hqDkerCard | hqDkerCard
  · have hqDkerBot : qD.ker = ⊥ := Subgroup.card_eq_one.mp hqDkerCard
    obtain ⟨d, hd⟩ := hqD (q u)
    have hd2 : (d : E) ^ 2 = 1 := by
      have hdker : d ^ 2 ∈ qD.ker := by
        rw [MonoidHom.mem_ker, map_pow, hd]
        have hpow := pow_orderOf_eq_one (q u)
        simpa [huq] using hpow
      rw [hqDkerBot, Subgroup.mem_bot] at hdker
      exact congrArg Subtype.val hdker
    let k := u * (d : E)⁻¹
    have hk : k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change q u * (qD d)⁻¹ = 1
      rw [hd]
      simp
    have hk2 : k ^ 2 = 1 :=
      SchurPresentation.DoubleCoverUniqueness.ker_pow_two_eq_one q hcard hk
    have hkcenter : k ∈ Subgroup.center E := hcenter hk
    have hcomm : Commute k (d : E) :=
      (Subgroup.mem_center_iff.mp hkcenter d).symm
    have hud : u = k * (d : E) := by simp [k]
    have hu2 : u ^ 2 = 1 := by
      rw [hud, hcomm.mul_pow, hk2, hd2]
      simp
    have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hu2
    rw [hu] at hdvd
    norm_num at hdvd
  · have hDcard : Nat.card D =
        Nat.card (alternatingGroup (Fin m)) * 2 := by
      have h := SchurPresentation.card_comap_mul qD hqD
        (⊤ : Subgroup (alternatingGroup (Fin m)))
      simpa only [Subgroup.comap_top, Subgroup.card_top, hqDkerCard] using h
    have hEcard : Nat.card E =
        Nat.card (alternatingGroup (Fin m)) * 2 := by
      have h := SchurPresentation.card_comap_mul q hq
        (⊤ : Subgroup (alternatingGroup (Fin m)))
      simpa only [Subgroup.comap_top, Subgroup.card_top, hcard] using h
    have hDtop : D = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      exact hDcard.trans hEcard.symm
    let perfectE : Group.IsPerfect E := ⟨by simpa [D] using hDtop⟩
    have hkerEqCenter : q.ker = Subgroup.center E := by
      apply SchurPresentation.ker_eq_center_of_surjective_of_center_eq_bot q hq hcenter
      exact alternatingGroup.center_eq_bot (by
        have : 4 ≤ Nat.card (Fin m) := by omega
        exact this)
    let e : E ⧸ Subgroup.center E ≃* alternatingGroup (Fin m) :=
      (QuotientGroup.quotientMulEquivOfEq hkerEqCenter.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq)
    let qs : IsQuasisimple E := {
      toIsPerfect := perfectE
      simple := e.isSimpleGroup }
    exact ⟨qs, by rw [← hkerEqCenter, hcard], ⟨e⟩⟩

private def __ch5_proposition_5_2_6_d4Rho1Perm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

private def __ch5_proposition_5_2_6_d4Rho2Perm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

private def __ch5_proposition_5_2_6_d4TauPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

private def __ch5_proposition_5_2_6_d4Rho1 : alternatingGroup (Fin 4) :=
  ⟨__ch5_proposition_5_2_6_d4Rho1Perm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private def __ch5_proposition_5_2_6_d4Rho2 : alternatingGroup (Fin 4) :=
  ⟨__ch5_proposition_5_2_6_d4Rho2Perm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private def __ch5_proposition_5_2_6_d4Tau : alternatingGroup (Fin 4) :=
  ⟨__ch5_proposition_5_2_6_d4TauPerm, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private def __ch5_proposition_5_2_6_d4V : Subgroup (alternatingGroup (Fin 4)) :=
  { carrier := {1, __ch5_proposition_5_2_6_d4Rho1, __ch5_proposition_5_2_6_d4Rho2, __ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Rho2}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
      rcases ha with rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl <;>
        simp [__ch5_proposition_5_2_6_d4Rho1, __ch5_proposition_5_2_6_d4Rho2, __ch5_proposition_5_2_6_d4Rho1Perm, __ch5_proposition_5_2_6_d4Rho2Perm] <;> decide
    inv_mem' := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl | rfl <;>
        simp [__ch5_proposition_5_2_6_d4Rho1, __ch5_proposition_5_2_6_d4Rho2, __ch5_proposition_5_2_6_d4Rho1Perm, __ch5_proposition_5_2_6_d4Rho2Perm] <;> decide }

private theorem __ch5_proposition_5_2_6_d4Rho1_order : orderOf __ch5_proposition_5_2_6_d4Rho1 = 2 := by
  apply orderOf_eq_prime <;> decide
private theorem __ch5_proposition_5_2_6_d4Rho2_order : orderOf __ch5_proposition_5_2_6_d4Rho2 = 2 := by
  apply orderOf_eq_prime <;> decide
private theorem __ch5_proposition_5_2_6_d4Rho12_order : orderOf (__ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Rho2) = 2 := by
  apply orderOf_eq_prime <;> decide
private theorem __ch5_proposition_5_2_6_d4_order_of_support_four
    (x : alternatingGroup (Fin 4)) (hx : x.1.support.card = 4) :
    orderOf x = 2 := by
  fin_cases x
  all_goals
    first
    | exfalso; revert hx; decide
    | apply orderOf_eq_prime <;> decide
private theorem __ch5_proposition_5_2_6_d4Rho1_support : __ch5_proposition_5_2_6_d4Rho1.1.support.card = 4 := by decide
private theorem __ch5_proposition_5_2_6_d4Rho2_support : __ch5_proposition_5_2_6_d4Rho2.1.support.card = 4 := by decide
private theorem __ch5_proposition_5_2_6_d4Rho12_support : (__ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Rho2).1.support.card = 4 := by decide
private theorem __ch5_proposition_5_2_6_d4Tau_order : orderOf __ch5_proposition_5_2_6_d4Tau = 3 := by
  apply orderOf_eq_prime <;> decide
private theorem __ch5_proposition_5_2_6_d4V_card : Nat.card __ch5_proposition_5_2_6_d4V = 4 := by
  change Nat.card (__ch5_proposition_5_2_6_d4V : Set (alternatingGroup (Fin 4))) = 4
  rw [Nat.card_coe_set_eq]
  have hset : (__ch5_proposition_5_2_6_d4V : Set (alternatingGroup (Fin 4))) =
      (↑({1, __ch5_proposition_5_2_6_d4Rho1, __ch5_proposition_5_2_6_d4Rho2, __ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Rho2} :
        Finset (alternatingGroup (Fin 4))) : Set (alternatingGroup (Fin 4))) := by
    ext x
    simp [__ch5_proposition_5_2_6_d4V]
  rw [hset, Set.ncard_coe_finset]
  all_goals decide
private instance : __ch5_proposition_5_2_6_d4V.Normal := by
  constructor
  intro n hn g
  simp only [__ch5_proposition_5_2_6_d4V] at hn ⊢
  rcases hn with rfl | rfl | rfl | rfl <;>
    fin_cases g <;>
    simp [__ch5_proposition_5_2_6_d4Rho1, __ch5_proposition_5_2_6_d4Rho2, __ch5_proposition_5_2_6_d4Rho1Perm, __ch5_proposition_5_2_6_d4Rho2Perm] <;> decide

private theorem __ch5_proposition_5_2_6_d4Tau_conj_rho1 :
    __ch5_proposition_5_2_6_d4Tau * __ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Tau⁻¹ = __ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Rho2 := by decide

private theorem __ch5_proposition_5_2_6_d4Tau_conj_rho2 :
    __ch5_proposition_5_2_6_d4Tau * __ch5_proposition_5_2_6_d4Rho2 * __ch5_proposition_5_2_6_d4Tau⁻¹ = __ch5_proposition_5_2_6_d4Rho1 := by decide

private theorem __ch5_proposition_5_2_6_d4Tau_not_mem_V : __ch5_proposition_5_2_6_d4Tau ∉ __ch5_proposition_5_2_6_d4V := by
  simp [__ch5_proposition_5_2_6_d4V, __ch5_proposition_5_2_6_d4Tau, __ch5_proposition_5_2_6_d4Rho1, __ch5_proposition_5_2_6_d4Rho2, __ch5_proposition_5_2_6_d4TauPerm,
    __ch5_proposition_5_2_6_d4Rho1Perm, __ch5_proposition_5_2_6_d4Rho2Perm]
  all_goals decide
private theorem __ch5_proposition_5_2_6_d4V_sup_tau : __ch5_proposition_5_2_6_d4V ⊔ Subgroup.zpowers __ch5_proposition_5_2_6_d4Tau = ⊤ := by
  let T : Subgroup (alternatingGroup (Fin 4)) := Subgroup.zpowers __ch5_proposition_5_2_6_d4Tau
  have hTcard : Nat.card T = 3 := by
    simpa [T] using (Nat.card_zpowers __ch5_proposition_5_2_6_d4Tau).trans __ch5_proposition_5_2_6_d4Tau_order
  have hinter : __ch5_proposition_5_2_6_d4V ⊓ T = ⊥ := by
    apply Disjoint.eq_bot
    apply Subgroup.disjoint_of_coprime_natCard
    rw [__ch5_proposition_5_2_6_d4V_card, hTcard]
    all_goals decide
  have hrel : __ch5_proposition_5_2_6_d4V.relIndex T = 3 := by
    rw [← Subgroup.inf_relIndex_right, hinter,
      Subgroup.relIndex_bot_left, hTcard]
  have hcard : Nat.card ↥(__ch5_proposition_5_2_6_d4V ⊔ T) = 12 := by
    have hmul := Subgroup.relIndex_mul_relIndex
      (⊥ : Subgroup (alternatingGroup (Fin 4))) __ch5_proposition_5_2_6_d4V (__ch5_proposition_5_2_6_d4V ⊔ T)
      bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, __ch5_proposition_5_2_6_d4V_card,
      Subgroup.relIndex_sup_left, hrel,
      Subgroup.relIndex_bot_left] at hmul
    omega
  apply Subgroup.eq_top_of_card_eq
  rw [hcard]
  exact (alternatingGroup.card_of_card_eq_four (by simp)).symm

private theorem __ch5_proposition_5_2_6_exists_order_three_lift_two_kernel
    {E G : Type*} [Group E] [Finite E] [Group G]
    (q : E →* G) (hq : Function.Surjective q)
    (hcenter : q.ker ≤ Subgroup.center E)
    (hcard : Nat.card q.ker = 2)
    (g : G) (hg : orderOf g = 3) :
    ∃ t : E, q t = g ∧ orderOf t = 3 := by
  obtain ⟨x, hx⟩ := hq g
  have hx3ker : x ^ 3 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, hx]
    simpa [hg] using pow_orderOf_eq_one g
  rcases SchurPresentation.DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution
      q hcard hx3ker with hx3 | hx3
  · refine ⟨x, hx, ?_⟩
    have hdiv : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · have hx1 : x = 1 := orderOf_eq_one_iff.mp h1
      have : g = 1 := by simpa [hx1] using hx.symm
      simp [this] at hg
    · exact h3
  · let z : E :=
      SchurPresentation.DoubleCoverUniqueness.kernelInvolution q hcard
    let t := z * x
    have hzker : z ∈ q.ker :=
      (SchurPresentation.DoubleCoverUniqueness.kernelInvolution q hcard).property
    have hzq : q z = 1 := MonoidHom.mem_ker.mp hzker
    have hzt : q t = g := by simp [t, hzq, hx]
    have hz2 : z ^ 2 = 1 :=
      SchurPresentation.DoubleCoverUniqueness.kernelInvolution_sq q hcard
    have hzx : Commute z x :=
      (Subgroup.mem_center_iff.mp (hcenter hzker) x).symm
    have ht3 : t ^ 3 = 1 := by
      change (z * x) ^ 3 = 1
      rw [hzx.mul_pow, hx3]
      calc
        z ^ 3 * z = (z ^ 2) ^ 2 := by group
        _ = 1 := by rw [hz2, one_pow]
    refine ⟨t, hzt, ?_⟩
    have hdiv : orderOf t ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr ht3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · have ht1 : t = 1 := orderOf_eq_one_iff.mp h1
      have : g = 1 := by simpa [ht1] using hzt.symm
      simp [this] at hg
    · exact h3

private theorem __ch5_proposition_5_2_6_sq_ne_one_of_orderOf_eq_four
    {G : Type*} [Group G] (x : G) (hx : orderOf x = 4) : x ^ 2 ≠ 1 := by
  intro hsq
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  rw [hx] at hdvd
  norm_num at hdvd

private noncomputable def cyclicFourHom {E : Type*} [Group E]
    (a : E) (ha : orderOf a = 4) : Multiplicative (ZMod 4) →* E :=
  (Subgroup.subtype (Subgroup.zpowers a)).comp
    (zmodMulEquivOfGenerator
      (g := (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a))
      (by
        intro x
        rcases x with ⟨x, i, rfl⟩
        exact ⟨i, by ext; simp⟩)
      ((Nat.card_zpowers a).trans ha)).toMonoidHom

private noncomputable def cyclicThreeHom {E : Type*} [Group E]
    (t : E) (ht : orderOf t = 3) : Multiplicative (ZMod 3) →* E :=
  (Subgroup.subtype (Subgroup.zpowers t)).comp
    (zmodMulEquivOfGenerator
      (g := (⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t))
      (by
        intro x
        rcases x with ⟨x, i, rfl⟩
        exact ⟨i, by ext; simp⟩)
      ((Nat.card_zpowers t).trans ht)).toMonoidHom

private theorem __ch5_proposition_5_2_6_cyclicThreeHom_one_generator {E : Type*} [Group E]
    (t : E) (ht : orderOf t = 3) :
    cyclicThreeHom t ht (Multiplicative.ofAdd 1) = t := by
  exact congrArg Subtype.val
    (zmodMulEquivOfGenerator_apply_ofAdd_one
      (G := Subgroup.zpowers t)
      (g := (⟨t, Subgroup.mem_zpowers t⟩ : Subgroup.zpowers t))
      (by
        intro x
        rcases x with ⟨x, i, rfl⟩
        exact ⟨i, by ext; simp⟩)
      ((Nat.card_zpowers t).trans ht))

private theorem __ch5_proposition_5_2_6_cyclicThreeHom_two {E : Type*} [Group E]
    (t : E) (ht : orderOf t = 3) :
    cyclicThreeHom t ht (Multiplicative.ofAdd 2) = t ^ 2 := by
  rw [show (Multiplicative.ofAdd 2 : Multiplicative (ZMod 3)) =
    Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 by rfl]
  rw [map_mul, __ch5_proposition_5_2_6_cyclicThreeHom_one_generator, pow_two]

private theorem __ch5_proposition_5_2_6_cyclicFourHom_one_generator {E : Type*} [Group E]
    (a : E) (ha : orderOf a = 4) :
    cyclicFourHom a ha (Multiplicative.ofAdd 1) = a := by
  exact congrArg Subtype.val
    (zmodMulEquivOfGenerator_apply_ofAdd_one
      (G := Subgroup.zpowers a)
      (g := (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a))
      (by
        intro x
        rcases x with ⟨x, i, rfl⟩
        exact ⟨i, by ext; simp⟩)
      ((Nat.card_zpowers a).trans ha))

private theorem __ch5_proposition_5_2_6_cyclicFourHom_two {E : Type*} [Group E]
    (a : E) (ha : orderOf a = 4) :
    cyclicFourHom a ha (Multiplicative.ofAdd 2) = a ^ 2 := by
  rw [show (Multiplicative.ofAdd 2 : Multiplicative (ZMod 4)) =
    Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 by rfl]
  rw [map_mul, __ch5_proposition_5_2_6_cyclicFourHom_one_generator, pow_two]

private theorem __ch5_proposition_5_2_6_cyclicFourHom_mem_zpowers {E : Type*} [Group E]
    (a : E) (ha : orderOf a = 4) (c : Multiplicative (ZMod 4)) :
    cyclicFourHom a ha c ∈ Subgroup.zpowers a := by
  change ((zmodMulEquivOfGenerator
    (g := (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a))
    (by
      intro x
      rcases x with ⟨x, i, rfl⟩
      exact ⟨i, by ext; simp⟩)
    ((Nat.card_zpowers a).trans ha)) c : Subgroup.zpowers a).1 ∈
      Subgroup.zpowers a
  exact Subtype.property _

private theorem __ch5_proposition_5_2_6_cyclicFourHom_b_mul {E : Type*} [Group E]
    (a b : E) (ha : orderOf a = 4) (hba : b * a = a⁻¹ * b)
    (i : ZMod 4) :
    b * cyclicFourHom a ha (Multiplicative.ofAdd i) =
      cyclicFourHom a ha (Multiplicative.ofAdd (-i)) * b := by
  obtain ⟨z, hz⟩ := __ch5_proposition_5_2_6_cyclicFourHom_mem_zpowers a ha (Multiplicative.ofAdd i)
  calc
    b * cyclicFourHom a ha (Multiplicative.ofAdd i) = b * a ^ z := by rw [← hz]
    _ = (a⁻¹) ^ z * b :=
      (show SemiconjBy b a a⁻¹ from hba).zpow_right z
    _ = (a ^ z)⁻¹ * b := by rw [inv_zpow]
    _ = (cyclicFourHom a ha (Multiplicative.ofAdd i))⁻¹ * b := by rw [← hz]
    _ = cyclicFourHom a ha (Multiplicative.ofAdd (-i)) * b := by
      rw [← map_inv]
      rfl

private theorem __ch5_proposition_5_2_6_cyclicFourHom_mul_b {E : Type*} [Group E]
    (a b : E) (ha : orderOf a = 4) (hba : b * a = a⁻¹ * b)
    (i : ZMod 4) :
    cyclicFourHom a ha (Multiplicative.ofAdd i) * b =
      b * cyclicFourHom a ha (Multiplicative.ofAdd (-i)) := by
  have h := __ch5_proposition_5_2_6_cyclicFourHom_b_mul a b ha hba (-i)
  simpa using h.symm

private noncomputable def abstractQ8Map {E : Type*} [Group E]
    (a b : E) (ha : orderOf a = 4) : QuaternionGroup 2 → E
  | .a i => cyclicFourHom a ha (Multiplicative.ofAdd i)
  | .xa i => b * cyclicFourHom a ha (Multiplicative.ofAdd i)

private theorem __ch5_proposition_5_2_6_abstractQ8Map_one
    {E : Type*} [Group E] (a b : E) (ha : orderOf a = 4) :
    abstractQ8Map a b ha 1 = 1 := by
  change cyclicFourHom a ha (Multiplicative.ofAdd 0) = 1
  exact map_one _

private theorem __ch5_proposition_5_2_6_abstractQ8Map_mul
    {E : Type*} [Group E] (a b : E)
    (ha : orderOf a = 4) (hb2 : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b)
    (x y : QuaternionGroup 2) :
    abstractQ8Map a b ha (x * y) =
      abstractQ8Map a b ha x * abstractQ8Map a b ha y := by
  rcases x with i | i <;> rcases y with j | j
  · change cyclicFourHom a ha (Multiplicative.ofAdd (i + j)) =
      cyclicFourHom a ha (Multiplicative.ofAdd i) *
        cyclicFourHom a ha (Multiplicative.ofAdd j)
    exact map_mul _ _ _
  · change b * cyclicFourHom a ha (Multiplicative.ofAdd (j - i)) =
      cyclicFourHom a ha (Multiplicative.ofAdd i) *
        (b * cyclicFourHom a ha (Multiplicative.ofAdd j))
    rw [← mul_assoc, __ch5_proposition_5_2_6_cyclicFourHom_mul_b a b ha hba i, mul_assoc, ← map_mul]
    congr 2
    apply Multiplicative.toAdd.injective
    change j - i = -i + j
    ring
  · change b * cyclicFourHom a ha (Multiplicative.ofAdd (i + j)) =
      (b * cyclicFourHom a ha (Multiplicative.ofAdd i)) *
        cyclicFourHom a ha (Multiplicative.ofAdd j)
    rw [mul_assoc, ← map_mul]
    congr 2
  · change cyclicFourHom a ha (Multiplicative.ofAdd (2 + j - i)) =
      (b * cyclicFourHom a ha (Multiplicative.ofAdd i)) *
        (b * cyclicFourHom a ha (Multiplicative.ofAdd j))
    symm
    calc
      (b * cyclicFourHom a ha (Multiplicative.ofAdd i)) *
          (b * cyclicFourHom a ha (Multiplicative.ofAdd j)) =
          b * (cyclicFourHom a ha (Multiplicative.ofAdd i) * b) *
            cyclicFourHom a ha (Multiplicative.ofAdd j) := by group
      _ = b * (b * cyclicFourHom a ha (Multiplicative.ofAdd (-i))) *
            cyclicFourHom a ha (Multiplicative.ofAdd j) := by
              rw [__ch5_proposition_5_2_6_cyclicFourHom_mul_b a b ha hba i]
      _ = b ^ 2 * cyclicFourHom a ha (Multiplicative.ofAdd (-i)) *
            cyclicFourHom a ha (Multiplicative.ofAdd j) := by
              rw [pow_two]
              group
      _ = cyclicFourHom a ha (Multiplicative.ofAdd 2) *
            cyclicFourHom a ha (Multiplicative.ofAdd (-i)) *
            cyclicFourHom a ha (Multiplicative.ofAdd j) := by
              rw [hb2, __ch5_proposition_5_2_6_cyclicFourHom_two]
      _ = cyclicFourHom a ha (Multiplicative.ofAdd (2 + j - i)) := by
        rw [← map_mul, ← map_mul]
        congr 1
        apply Multiplicative.toAdd.injective
        simp
        ring

private noncomputable def abstractQ8Hom {E : Type*} [Group E]
    (a b : E) (ha : orderOf a = 4) (hb2 : b ^ 2 = a ^ 2)
    (hba : b * a = a⁻¹ * b) : QuaternionGroup 2 →* E where
  toFun := abstractQ8Map a b ha
  map_one' := __ch5_proposition_5_2_6_abstractQ8Map_one a b ha
  map_mul' := __ch5_proposition_5_2_6_abstractQ8Map_mul a b ha hb2 hba

private theorem __ch5_proposition_5_2_6_kleinFourPreimage_hom
    {E : Type*} [Group E] [Finite E]
    (q : E →* alternatingGroup (Fin 4))
    (hq : Function.Surjective q)
    (hcard : Nat.card q.ker = 2)
    (hfour : ∀ x : E, (q x).1.support.card = 4 → orderOf x = 4)
    (a b : E) (ha : q a = __ch5_proposition_5_2_6_d4Rho1) (hb : q b = __ch5_proposition_5_2_6_d4Rho2) :
    ∃ phi : QuaternionGroup 2 →* E,
      phi.range = __ch5_proposition_5_2_6_d4V.comap q ∧
        phi (QuaternionGroup.a 1) = a ∧
        phi (QuaternionGroup.xa 0) = b := by
  let N : Subgroup E := __ch5_proposition_5_2_6_d4V.comap q
  let : N.Normal := inferInstance
  have hNcard : Nat.card N = 8 := by
    have h := SchurPresentation.card_comap_mul q hq __ch5_proposition_5_2_6_d4V
    rw [__ch5_proposition_5_2_6_d4V_card, hcard] at h
    simpa [N] using h
  have haN : a ∈ N := by
    change q a ∈ __ch5_proposition_5_2_6_d4V
    rw [ha]
    simp [__ch5_proposition_5_2_6_d4V]
  have hbN : b ∈ N := by
    change q b ∈ __ch5_proposition_5_2_6_d4V
    rw [hb]
    simp [__ch5_proposition_5_2_6_d4V]
  have ha4 : orderOf a = 4 := hfour a (by rw [ha]; exact __ch5_proposition_5_2_6_d4Rho1_support)
  have hb4 : orderOf b = 4 := hfour b (by rw [hb]; exact __ch5_proposition_5_2_6_d4Rho2_support)
  have hab4 : orderOf (a * b) = 4 := hfour (a * b) (by
    rw [map_mul, ha, hb]
    exact __ch5_proposition_5_2_6_d4Rho12_support)
  have ha2ker : a ^ 2 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, ha]
    simpa [__ch5_proposition_5_2_6_d4Rho1_order] using pow_orderOf_eq_one __ch5_proposition_5_2_6_d4Rho1
  have hb2ker : b ^ 2 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, hb]
    simpa [__ch5_proposition_5_2_6_d4Rho2_order] using pow_orderOf_eq_one __ch5_proposition_5_2_6_d4Rho2
  have hab2ker : (a * b) ^ 2 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, ha, hb]
    simpa [__ch5_proposition_5_2_6_d4Rho12_order] using pow_orderOf_eq_one (__ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Rho2)
  have ha2ne : a ^ 2 ≠ 1 := __ch5_proposition_5_2_6_sq_ne_one_of_orderOf_eq_four a ha4
  have hb2ne : b ^ 2 ≠ 1 := __ch5_proposition_5_2_6_sq_ne_one_of_orderOf_eq_four b hb4
  have hab2ne : (a * b) ^ 2 ≠ 1 :=
    __ch5_proposition_5_2_6_sq_ne_one_of_orderOf_eq_four (a * b) hab4
  have ha2 : a ^ 2 = b ^ 2 := by
    have ha' := SchurPresentation.DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
      q hcard (⟨a ^ 2, ha2ker⟩ : q.ker) (by
        intro h
        exact ha2ne (congrArg Subtype.val h))
    have hb' := SchurPresentation.DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
      q hcard (⟨b ^ 2, hb2ker⟩ : q.ker) (by
        intro h
        exact hb2ne (congrArg Subtype.val h))
    exact congrArg Subtype.val (ha'.trans hb'.symm)
  have hab2 : (a * b) ^ 2 = a ^ 2 := by
    have hab' := SchurPresentation.DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
      q hcard (⟨(a * b) ^ 2, hab2ker⟩ : q.ker) (by
        intro h
        exact hab2ne (congrArg Subtype.val h))
    have ha' := SchurPresentation.DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
      q hcard (⟨a ^ 2, ha2ker⟩ : q.ker) (by
        intro h
        exact ha2ne (congrArg Subtype.val h))
    exact congrArg Subtype.val (hab'.trans ha'.symm)
  have hba : b * a = a⁻¹ * b := by
    have habb : (a * b) ^ 2 = b ^ 2 := hab2.trans ha2
    calc
      b * a = a⁻¹ * (a * b) ^ 2 * b⁻¹ := by
        simp [pow_two, mul_assoc]
      _ = a⁻¹ * b ^ 2 * b⁻¹ := by rw [habb]
      _ = a⁻¹ * b := by group
  let phiE : QuaternionGroup 2 →* E := abstractQ8Hom a b ha4 ha2.symm hba
  have hphiMem : ∀ x, phiE x ∈ N := by
    intro x
    rcases x with i | i
    · change cyclicFourHom a ha4 (Multiplicative.ofAdd i) ∈ N
      exact N.zpow_mem haN (Multiplicative.toAdd (Multiplicative.ofAdd i)).val
    · change b * cyclicFourHom a ha4 (Multiplicative.ofAdd i) ∈ N
      exact N.mul_mem hbN
        (N.zpow_mem haN (Multiplicative.toAdd (Multiplicative.ofAdd i)).val)
  let phiN : QuaternionGroup 2 →* N := phiE.codRestrict N hphiMem
  let R : Subgroup N := phiN.range
  have haR : (⟨a, haN⟩ : N) ∈ R := by
    refine ⟨QuaternionGroup.a 1, ?_⟩
    apply Subtype.ext
    exact __ch5_proposition_5_2_6_cyclicFourHom_one_generator a ha4
  have hbR : (⟨b, hbN⟩ : N) ∈ R := by
    refine ⟨QuaternionGroup.xa 0, ?_⟩
    apply Subtype.ext
    change b * cyclicFourHom a ha4 (Multiplicative.ofAdd 0) = b
    rw [show (Multiplicative.ofAdd 0 : Multiplicative (ZMod 4)) = 1 by rfl,
      map_one, mul_one]
  have ha2R : (⟨a ^ 2, N.pow_mem haN 2⟩ : N) ∈ R := by
    simpa [pow_two] using R.mul_mem haR haR
  have hkernelInv :
      (SchurPresentation.DoubleCoverUniqueness.kernelInvolution q hcard : E) = a ^ 2 := by
    let a2ker : q.ker := ⟨a ^ 2, ha2ker⟩
    have ha2ne' : a2ker ≠ 1 := by
      intro h
      exact ha2ne (congrArg Subtype.val h)
    exact congrArg Subtype.val
      (SchurPresentation.DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
        q hcard a2ker ha2ne').symm
  have hphiNsurj : Function.Surjective phiN := by
    intro x
    have hxV : q x.1 ∈ __ch5_proposition_5_2_6_d4V := x.2
    simp only [__ch5_proposition_5_2_6_d4V] at hxV
    obtain ⟨r, hrR, hrq⟩ : ∃ r : N, r ∈ R ∧ q r.1 = q x.1 := by
      rcases hxV with hx | hx | hx | hx
      · refine ⟨1, R.one_mem, ?_⟩
        simpa using hx.symm
      · refine ⟨⟨a, haN⟩, haR, ?_⟩
        simpa [ha] using hx.symm
      · refine ⟨⟨b, hbN⟩, hbR, ?_⟩
        simpa [hb] using hx.symm
      · refine ⟨⟨a * b, N.mul_mem haN hbN⟩, R.mul_mem haR hbR, ?_⟩
        simpa [map_mul, ha, hb] using hx.symm
    let k : E := x.1 * r.1⁻¹
    have hkN : k ∈ N := N.mul_mem x.2 (N.inv_mem r.2)
    have hkker : k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrq]
      simp
    have hkR : (⟨k, hkN⟩ : N) ∈ R := by
      rcases SchurPresentation.DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution
          q hcard hkker with hk | hk
      · have hk1 : (⟨k, hkN⟩ : N) = 1 := by
          apply Subtype.ext
          exact hk
        rw [hk1]
        exact R.one_mem
      · have hk2 : k = a ^ 2 := hk.trans hkernelInv
        simpa [k, hk2] using ha2R
    have hxR : x ∈ R := by
      have hxkr : x = (⟨k, hkN⟩ : N) * r := by
        apply Subtype.ext
        simp [k]
      rw [hxkr]
      exact R.mul_mem hkR hrR
    exact hxR
  have hphiNbij : Function.Bijective phiN := by
    let : Fintype N := Fintype.ofFinite _
    exact (Fintype.bijective_iff_surjective_and_card phiN).2
      ⟨hphiNsurj, by
        rw [QuaternionGroup.card]
        rw [← Nat.card_eq_fintype_card, hNcard]⟩
  have hphiRange : phiE.range = N := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact hphiMem y
    · intro x hx
      obtain ⟨y, hy⟩ := hphiNsurj (⟨x, hx⟩ : N)
      exact ⟨y, congrArg Subtype.val hy⟩
  refine ⟨phiE, hphiRange, ?_, ?_⟩
  · exact __ch5_proposition_5_2_6_cyclicFourHom_one_generator a ha4
  · change b * cyclicFourHom a ha4 (Multiplicative.ofAdd 0) = b
    rw [show (Multiplicative.ofAdd 0 : Multiplicative (ZMod 4)) = 1 by rfl,
      map_one, mul_one]

private theorem __ch5_proposition_5_2_6_binaryTetrahedralEquiv_of_data
    {E : Type*} [Group E] [Finite E]
    (q : E →* alternatingGroup (Fin 4))
    (hq : Function.Surjective q)
    (hcard : Nat.card q.ker = 2)
    (phi : QuaternionGroup 2 →* E)
    (hphiRange : phi.range = __ch5_proposition_5_2_6_d4V.comap q)
    (a b t : E)
    (hphiA : phi (QuaternionGroup.a 1) = a)
    (hphiB : phi (QuaternionGroup.xa 0) = b)
    (ht : orderOf t = 3)
    (hqt : q t = __ch5_proposition_5_2_6_d4Tau)
    (hconjA : t * a * t⁻¹ = b * a)
    (hconjB : t * b * t⁻¹ = a⁻¹) :
    Nonempty (E ≃* SL23) := by
  let psi : Multiplicative (ZMod 3) →* E := cyclicThreeHom t ht
  have hactionOne (x : QuaternionGroup 2) :
      phi (q8Cycle x) = t * phi x * t⁻¹ := by
    let f : QuaternionGroup 2 →* E := phi.comp q8Cycle.toMonoidHom
    let g : QuaternionGroup 2 →* E :=
      (MulAut.conj t).toMonoidHom.comp phi
    have hA : f (QuaternionGroup.a 1) = g (QuaternionGroup.a 1) := by
      change phi (q8Cycle (QuaternionGroup.a 1)) =
        t * phi (QuaternionGroup.a 1) * t⁻¹
      rw [q8Cycle_a_one,
        show QuaternionGroup.xa 1 =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide,
        map_mul, hphiA, hphiB, hconjA]
    have hB : f (QuaternionGroup.xa 0) = g (QuaternionGroup.xa 0) := by
      change phi (q8Cycle (QuaternionGroup.xa 0)) =
        t * phi (QuaternionGroup.xa 0) * t⁻¹
      rw [q8Cycle_xa_zero,
        show QuaternionGroup.a 3 = (QuaternionGroup.a 1)⁻¹ by decide,
        map_inv, hphiA, hphiB, hconjB]
    have hfg : f = g := by
      apply DFunLike.ext _ _
      intro y
      rcases y with i | i
      · rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
        rw [map_pow, map_pow, hA]
      · have hxa : QuaternionGroup.xa i =
            QuaternionGroup.xa 0 * QuaternionGroup.a i := by
          rw [QuaternionGroup.xa_mul_a]
          simp
        rw [hxa, map_mul, map_mul, hB]
        rw [← ZMod.natCast_zmod_val i, ← QuaternionGroup.a_one_pow]
        rw [map_pow, map_pow, hA]
    exact DFunLike.congr_fun hfg x
  have haction (k : Multiplicative (ZMod 3)) (x : QuaternionGroup 2) :
      phi (q8C3Action k x) = psi k * phi x * (psi k)⁻¹ := by
    change ZMod 3 at k
    fin_cases k
    all_goals simp only
    · change phi ((q8Cycle ^ 0) x) =
        psi (Multiplicative.ofAdd 0) * phi x *
          (psi (Multiplicative.ofAdd 0))⁻¹
      simp
    · change phi ((q8Cycle ^ 1) x) =
        psi (Multiplicative.ofAdd 1) * phi x *
          (psi (Multiplicative.ofAdd 1))⁻¹
      simpa [psi, __ch5_proposition_5_2_6_cyclicThreeHom_one_generator] using hactionOne x
    · change phi (q8Cycle (q8Cycle x)) =
        psi (Multiplicative.ofAdd 2) * phi x *
          (psi (Multiplicative.ofAdd 2))⁻¹
      rw [show psi (Multiplicative.ofAdd 2) = t ^ 2 by
        exact __ch5_proposition_5_2_6_cyclicThreeHom_two t ht]
      calc
        phi (q8Cycle (q8Cycle x)) =
            t * phi (q8Cycle x) * t⁻¹ := hactionOne (q8Cycle x)
        _ = t * (t * phi x * t⁻¹) * t⁻¹ := by rw [hactionOne]
        _ = t ^ 2 * phi x * (t ^ 2)⁻¹ := by
          rw [pow_two]
          group
  let F : (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) →* E :=
    SemidirectProduct.lift phi psi (by
      intro k
      apply MonoidHom.ext
      intro x
      exact haction k x)
  let R : Subgroup E := F.range
  have hphiR : phi.range ≤ R := by
    rintro x ⟨y, rfl⟩
    exact ⟨SemidirectProduct.inl y, by simp [F]⟩
  have hNle : __ch5_proposition_5_2_6_d4V.comap q ≤ R := by
    rw [← hphiRange]
    exact hphiR
  have htR : t ∈ R := by
    refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩
    simp [F, psi, __ch5_proposition_5_2_6_cyclicThreeHom_one_generator]
  have hVle : __ch5_proposition_5_2_6_d4V ≤ R.map q := by
    intro v hv
    obtain ⟨x, hx⟩ := hq v
    have hxN : x ∈ __ch5_proposition_5_2_6_d4V.comap q := by
      change q x ∈ __ch5_proposition_5_2_6_d4V
      rwa [hx]
    exact ⟨x, hNle hxN, hx⟩
  have hTauLe : Subgroup.zpowers __ch5_proposition_5_2_6_d4Tau ≤ R.map q := by
    apply Subgroup.zpowers_le.mpr
    exact ⟨t, htR, hqt⟩
  have hmapTop : R.map q = ⊤ := by
    apply top_unique
    rw [← __ch5_proposition_5_2_6_d4V_sup_tau]
    exact sup_le hVle hTauLe
  have hkerR : q.ker ≤ R := by
    intro x hx
    apply hNle
    change q x ∈ __ch5_proposition_5_2_6_d4V
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact __ch5_proposition_5_2_6_d4V.one_mem
  have hFsurj : Function.Surjective F := by
    intro x
    have hxmap : q x ∈ R.map q := by rw [hmapTop]; trivial
    obtain ⟨r, hrR, hrq⟩ := hxmap
    let k := x * r⁻¹
    have hkker : k ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrq]
      simp
    have hkR : k ∈ R := hkerR hkker
    have hxR : x ∈ R := by
      have hxkr : x = k * r := by simp [k]
      rw [hxkr]
      exact R.mul_mem hkR hrR
    exact hxR
  have hEcard : Nat.card E = 24 := by
    have h := SchurPresentation.card_comap_mul q hq
      (⊤ : Subgroup (alternatingGroup (Fin 4)))
    have htop : Nat.card ↥(⊤ : Subgroup (alternatingGroup (Fin 4))) =
        Nat.card (alternatingGroup (Fin 4)) := Subgroup.card_top
    rw [Subgroup.comap_top, htop, hcard,
      alternatingGroup.card_of_card_eq_four (by simp)] at h
    norm_num at h
    exact h
  let : Fintype (QuaternionGroup 2 ⋊[q8C3Action] Multiplicative (ZMod 3)) :=
    Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
      SemidirectProduct.equivProd.symm
  have : Fintype E := Fintype.ofFinite _
  have hFbij : Function.Bijective F := by
    apply (Fintype.bijective_iff_surjective_and_card F).2
    refine ⟨hFsurj, ?_⟩
    have hQ : Nat.card (QuaternionGroup 2) = 8 := by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hC : Nat.card (Multiplicative (ZMod 3)) = 3 := by simp
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      SemidirectProduct.card, hEcard, hQ, hC]
  exact ⟨(MulEquiv.ofBijective F hFbij).symm.trans binaryTetrahedralEquivSL⟩

private theorem __ch5_proposition_5_2_6_nonsplitDoubleExtension_four
    {E : Type*} [Group E] [Finite E]
    (q : E →* alternatingGroup (Fin 4))
    (hq : Function.Surjective q)
    (hcenter : q.ker ≤ Subgroup.center E)
    (hcard : Nat.card q.ker = 2)
    (hfour : ∀ x : E, (q x).1.support.card = 4 → orderOf x = 4) :
    Nonempty (E ≃* SL23) := by
  obtain ⟨t, hqt, ht⟩ := __ch5_proposition_5_2_6_exists_order_three_lift_two_kernel
    q hq hcenter hcard __ch5_proposition_5_2_6_d4Tau __ch5_proposition_5_2_6_d4Tau_order
  obtain ⟨a, ha⟩ := hq __ch5_proposition_5_2_6_d4Rho1
  let b := t * a * t⁻¹ * a⁻¹
  have hb : q b = __ch5_proposition_5_2_6_d4Rho2 := by
    calc
      q b = __ch5_proposition_5_2_6_d4Tau * __ch5_proposition_5_2_6_d4Rho1 * __ch5_proposition_5_2_6_d4Tau⁻¹ * __ch5_proposition_5_2_6_d4Rho1⁻¹ := by
        simp [b, hqt, ha]
      _ = __ch5_proposition_5_2_6_d4Rho2 := by rw [__ch5_proposition_5_2_6_d4Tau_conj_rho1]; decide
  have hconjA : t * a * t⁻¹ = b * a := by
    simp [b, mul_assoc]
  have ha4 : orderOf a = 4 := hfour a (by rw [ha]; exact __ch5_proposition_5_2_6_d4Rho1_support)
  have ha2ker : a ^ 2 ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow, ha]
    simpa [__ch5_proposition_5_2_6_d4Rho1_order] using pow_orderOf_eq_one __ch5_proposition_5_2_6_d4Rho1
  have ha2ne : a ^ 2 ≠ 1 := __ch5_proposition_5_2_6_sq_ne_one_of_orderOf_eq_four a ha4
  have hkernelInv :
      (SchurPresentation.DoubleCoverUniqueness.kernelInvolution q hcard : E) =
        a ^ 2 := by
    let a2ker : q.ker := ⟨a ^ 2, ha2ker⟩
    have ha2ne' : a2ker ≠ 1 := by
      intro h
      exact ha2ne (congrArg Subtype.val h)
    exact congrArg Subtype.val
      (SchurPresentation.DoubleCoverUniqueness.eq_kernelInvolution_of_ne_one
        q hcard a2ker ha2ne').symm
  let c := t * b * t⁻¹
  have hcq : q c = q a⁻¹ := by
    calc
      q c = __ch5_proposition_5_2_6_d4Tau * __ch5_proposition_5_2_6_d4Rho2 * __ch5_proposition_5_2_6_d4Tau⁻¹ := by simp [c, hqt, hb]
      _ = __ch5_proposition_5_2_6_d4Rho1 := __ch5_proposition_5_2_6_d4Tau_conj_rho2
      _ = q a⁻¹ := by rw [map_inv, ha]; decide
  let k := c * (a⁻¹)⁻¹
  have hkker : k ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcq]
    simp
  have hconjCases : c = a⁻¹ ∨ c = a := by
    rcases SchurPresentation.DoubleCoverUniqueness.eq_one_or_eq_kernelInvolution
        q hcard hkker with hk | hk
    · left
      calc
        c = (c * a) * a⁻¹ := by simp
        _ = a⁻¹ := by
          rw [show c * a = 1 by simpa [k] using hk]
          simp
    · right
      have hka2 : c * a = a ^ 2 := by simpa [k, hkernelInv] using hk
      calc
        c = (c * a) * a⁻¹ := by simp
        _ = a ^ 2 * a⁻¹ := by rw [hka2]
        _ = a := by group
  rcases hconjCases with hc | hc
  · obtain ⟨phi, hphiRange, hphiA, hphiB⟩ :=
      __ch5_proposition_5_2_6_kleinFourPreimage_hom q hq hcard hfour a b ha hb
    exact __ch5_proposition_5_2_6_binaryTetrahedralEquiv_of_data q hq hcard phi hphiRange
      a b t hphiA hphiB ht hqt hconjA (by simpa [c] using hc)
  · have haInv : q a⁻¹ = __ch5_proposition_5_2_6_d4Rho1 := by rw [map_inv, ha]; decide
    obtain ⟨phi, hphiRange, hphiA, hphiB⟩ :=
      __ch5_proposition_5_2_6_kleinFourPreimage_hom q hq hcard hfour a⁻¹ b haInv hb
    have hAB : a⁻¹ * b⁻¹ = b * a⁻¹ := by
      have hq8 :
          (QuaternionGroup.a 1 : QuaternionGroup 2) *
              (QuaternionGroup.xa 0)⁻¹ =
            QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
      have h := congrArg phi hq8
      have hxa : phi (QuaternionGroup.xa 1) = b * a⁻¹ := by
        rw [show (QuaternionGroup.xa 1 : QuaternionGroup 2) =
          QuaternionGroup.xa 0 * QuaternionGroup.a 1 by decide,
          map_mul, hphiA, hphiB]
      simpa [map_mul, map_inv, hphiA, hphiB, hxa] using h
    have hconjA' : t * a⁻¹ * t⁻¹ = b * a⁻¹ := by
      calc
        t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
        _ = (b * a)⁻¹ := by rw [hconjA]
        _ = a⁻¹ * b⁻¹ := by rw [mul_inv_rev]
        _ = b * a⁻¹ := hAB
    exact __ch5_proposition_5_2_6_binaryTetrahedralEquiv_of_data q hq hcard phi hphiRange
      a⁻¹ b t hphiA hphiB ht hqt hconjA' (by simpa [c] using hc)


private theorem __ch5_proposition_5_2_6_doubleCoverPreimage_alternating_of_root_support
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (m k : Nat) (hm : 5 ≤ m) (hkodd : Odd k)
    (Hbar : Subgroup (alternatingGroup (Fin n)))
    (eH : ↥Hbar ≃* alternatingGroup (Fin m))
    (hroot : ∀ u : Hbar,
      (eH u).1.support.card = 4 → u.1.1.support.card = 4 * k) :
    let H := Hbar.comap f.toMonoidHom
    IsQuasisimple ↥H ∧
      Nat.card (Subgroup.center ↥H) = 2 ∧
      Nonempty (↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin m)) := by
  let H := Hbar.comap f.toMonoidHom
  change IsQuasisimple H ∧ Nat.card (Subgroup.center H) = 2 ∧
    Nonempty (H ⧸ Subgroup.center H ≃* alternatingGroup (Fin m))
  let q0 : H →* Hbar :=
    (f.toMonoidHom.comp H.subtype).codRestrict Hbar (fun x => x.2)
  have hq0 : Function.Surjective q0 := by
    intro x
    obtain ⟨k, hk⟩ := f.surjective x.1
    have hkH : k ∈ H := by
      have hxmem := x.2
      change (x.1 : alternatingGroup (Fin n)) ∈ Hbar at hxmem
      rw [← hk] at hxmem
      exact hxmem
    refine ⟨⟨k, hkH⟩, ?_⟩
    apply Subtype.ext
    change f k = x.1
    exact hk
  let q : H →* alternatingGroup (Fin m) := eH.toMonoidHom.comp q0
  have hq : Function.Surjective q := eH.surjective.comp hq0
  have hqcenter : q.ker ≤ Subgroup.center H := by
    intro x hx
    have hq0x : q0 x = 1 := by
      apply eH.injective
      simpa [q] using MonoidHom.mem_ker.mp hx
    have hfx : f x.1 = 1 := by
      change f x.1 = (1 : Hbar).1
      have hval := congrArg Subtype.val hq0x
      dsimp [q0] at hval
      change f x.1 = (1 : Hbar).1 at hval
      exact hval
    have hxker : x.1 ∈ f.toMonoidHom.ker := MonoidHom.mem_ker.mpr hfx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (f.ker_le_center hxker) y.1
  have hHcard : Nat.card H = Nat.card Hbar * Nat.card f.toMonoidHom.ker := by
    simpa [H] using SchurPresentation.card_comap_mul
      f.toMonoidHom f.surjective Hbar
  have hHbarCard : Nat.card Hbar = Nat.card (alternatingGroup (Fin m)) :=
    Nat.card_congr eH.toEquiv
  have hqCardEq : Nat.card H =
      Nat.card (alternatingGroup (Fin m)) * Nat.card q.ker := by
    have h := SchurPresentation.card_comap_mul q hq
      (⊤ : Subgroup (alternatingGroup (Fin m)))
    simpa only [Subgroup.comap_top, Subgroup.card_top] using h
  have hqkerCard : Nat.card q.ker = 2 := by
    rw [hHbarCard, hker] at hHcard
    apply Nat.mul_left_cancel (Nat.card_pos :
      0 < Nat.card (alternatingGroup (Fin m)))
    exact hqCardEq.symm.trans hHcard
  have hm4 : 4 ≤ m := by omega
  let rho := alternatingRootInvolution m hm4
  let ubar : Hbar := eH.symm rho
  obtain ⟨u, hu⟩ := hq rho
  have hfu : f u.1 = ubar.1 := by
    have hq0u : q0 u = ubar := by
      apply eH.injective
      calc
        eH (q0 u) = q u := rfl
        _ = rho := hu
        _ = eH ubar := by simp [ubar]
    exact congrArg Subtype.val hq0u
  have hfuOrder : orderOf (f u.1) = 2 := by
    calc
      orderOf (f u.1) = orderOf (ubar : alternatingGroup (Fin n)) :=
        congrArg orderOf hfu
      _ = orderOf ubar := Subgroup.orderOf_coe ubar
      _ = orderOf (eH ubar) :=
        (orderOf_injective eH.toMonoidHom eH.injective ubar).symm
      _ = orderOf rho := by simp [ubar]
      _ = 2 := __ch5_proposition_5_2_6_alternatingRootInvolution_order m hm4
  have hsupport : (f u.1).1.support.card = 4 * k := by
    rw [hfu]
    apply hroot ubar
    simpa [ubar] using __ch5_proposition_5_2_6_alternatingRootInvolution_support m hm4
  have hu4 : orderOf u = 4 := by
    have hu4ambient := __ch5_proposition_5_2_6_orderOf_eq_four_of_odd_quarter_support n hn f hker u.1
      hfuOrder k hkodd hsupport
    exact (Subgroup.orderOf_coe u).symm.trans hu4ambient
  exact __ch5_proposition_5_2_6_nonsplitDoubleExtension_alternating m hm q hq hqcenter hqkerCard
    u (by simpa [hu] using __ch5_proposition_5_2_6_alternatingRootInvolution_order m hm4) hu4

private theorem __ch5_proposition_5_2_6_doubleCoverPreimage_four_of_root_support
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (k : Nat) (hkodd : Odd k)
    (Hbar : Subgroup (alternatingGroup (Fin n)))
    (eH : ↥Hbar ≃* alternatingGroup (Fin 4))
    (hroot : ∀ u : Hbar,
      (eH u).1.support.card = 4 → u.1.1.support.card = 4 * k) :
    let H := Hbar.comap f.toMonoidHom
    Nonempty (↥H ≃* SL23) := by
  let H := Hbar.comap f.toMonoidHom
  change Nonempty (H ≃* SL23)
  let q0 : H →* Hbar :=
    (f.toMonoidHom.comp H.subtype).codRestrict Hbar (fun x => x.2)
  have hq0 : Function.Surjective q0 := by
    intro x
    obtain ⟨y, hy⟩ := f.surjective x.1
    have hyH : y ∈ H := by
      have hxmem := x.2
      change (x.1 : alternatingGroup (Fin n)) ∈ Hbar at hxmem
      rw [← hy] at hxmem
      exact hxmem
    refine ⟨⟨y, hyH⟩, ?_⟩
    apply Subtype.ext
    change f y = x.1
    exact hy
  let q : H →* alternatingGroup (Fin 4) := eH.toMonoidHom.comp q0
  have hq : Function.Surjective q := eH.surjective.comp hq0
  have hqcenter : q.ker ≤ Subgroup.center H := by
    intro x hx
    have hq0x : q0 x = 1 := by
      apply eH.injective
      simpa [q] using MonoidHom.mem_ker.mp hx
    have hfx : f x.1 = 1 := by
      change f x.1 = (1 : Hbar).1
      have hval := congrArg Subtype.val hq0x
      dsimp [q0] at hval
      change f x.1 = (1 : Hbar).1 at hval
      exact hval
    have hxker : x.1 ∈ f.toMonoidHom.ker := MonoidHom.mem_ker.mpr hfx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (f.ker_le_center hxker) y.1
  have hHcard : Nat.card H = Nat.card Hbar * Nat.card f.toMonoidHom.ker := by
    simpa [H] using SchurPresentation.card_comap_mul
      f.toMonoidHom f.surjective Hbar
  have hHbarCard : Nat.card Hbar = Nat.card (alternatingGroup (Fin 4)) :=
    Nat.card_congr eH.toEquiv
  have hqCardEq : Nat.card H =
      Nat.card (alternatingGroup (Fin 4)) * Nat.card q.ker := by
    have h := SchurPresentation.card_comap_mul q hq
      (⊤ : Subgroup (alternatingGroup (Fin 4)))
    simpa only [Subgroup.comap_top, Subgroup.card_top] using h
  have hqkerCard : Nat.card q.ker = 2 := by
    rw [hHbarCard, hker] at hHcard
    apply Nat.mul_left_cancel (Nat.card_pos :
      0 < Nat.card (alternatingGroup (Fin 4)))
    exact hqCardEq.symm.trans hHcard
  have hfour : ∀ x : H, (q x).1.support.card = 4 → orderOf x = 4 := by
    intro x hx
    have hqOrder : orderOf (q x) = 2 := __ch5_proposition_5_2_6_d4_order_of_support_four (q x) hx
    have hq0Order : orderOf (q0 x) = 2 := by
      calc
        orderOf (q0 x) = orderOf (eH (q0 x)) :=
          (orderOf_injective eH.toMonoidHom eH.injective (q0 x)).symm
        _ = orderOf (q x) := rfl
        _ = 2 := hqOrder
    have hfxOrder : orderOf (f x.1) = 2 := by
      calc
        orderOf (f x.1) = orderOf ((q0 x : Hbar) :
            alternatingGroup (Fin n)) := rfl
        _ = orderOf (q0 x) := Subgroup.orderOf_coe (q0 x)
        _ = 2 := hq0Order
    have hsupport : (f x.1).1.support.card = 4 * k := by
      change (q0 x).1.1.support.card = 4 * k
      apply hroot (q0 x)
      simpa [q] using hx
    have hx4 := __ch5_proposition_5_2_6_orderOf_eq_four_of_odd_quarter_support n hn f hker x.1
      hfxOrder k hkodd hsupport
    exact (Subgroup.orderOf_coe x).symm.trans hx4
  exact __ch5_proposition_5_2_6_nonsplitDoubleExtension_four q hq hqcenter hqkerCard hfour

/-- Proposition 5.2.6(d)(2): the full preimage of the cycle-permuting
alternating factor is `2Aᵣ`.  At degree four this means the binary
tetrahedral group `SL₂(3)`; from degree five onward it is quasisimple. -/
public theorem proposition_5_2_6_d_2
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (r : Nat)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (hp2 : p ≠ 2)
    (hr : 4 ≤ r)
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (Lbar : Subgroup (alternatingGroup (Fin n)))
    (eL : ↥Lbar ≃* alternatingGroup (Fin r))
    (hreplication : ∀ u : Lbar,
      (eL u).1.support.card = 4 →
        u.1.1.support.card = 4 * p) :
    let L := Lbar.comap f.toMonoidHom
    (r = 4 → Nonempty
      (↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) ∧
    (5 ≤ r →
      IsQuasisimple ↥L ∧
        Nat.card (Subgroup.center ↥L) = 2 ∧
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
          alternatingGroup (Fin r))) := by
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact (hp2 h2).elim
    · exact Nat.odd_iff.mpr hodd
  constructor
  · intro hr4
    subst r
    exact __ch5_proposition_5_2_6_doubleCoverPreimage_four_of_root_support n hn f hker
      p hpodd Lbar eL hreplication
  · intro hr5
    exact __ch5_proposition_5_2_6_doubleCoverPreimage_alternating_of_root_support n hn f hker
      r p hr5 hpodd Lbar eL hreplication

/-- Proposition 5.2.6(d)(3): the full preimage of the fixed-point alternating
factor is `2Aₛ`, with the degree-four branch stated as `SL₂(3)`. -/
public theorem proposition_5_2_6_d_3
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n) (s : Nat)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (hs : 4 ≤ s)
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (H2bar : Subgroup (alternatingGroup (Fin n)))
    (eH2 : ↥H2bar ≃* alternatingGroup (Fin s))
    (hroot : ∀ u : H2bar,
      (eH2 u).1.support.card = 4 → u.1.1.support.card = 4) :
    let H2 := H2bar.comap f.toMonoidHom
    (s = 4 → Nonempty
      (↥H2 ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) ∧
    (5 ≤ s →
      IsQuasisimple ↥H2 ∧
        Nat.card (Subgroup.center ↥H2) = 2 ∧
        Nonempty (↥H2 ⧸ Subgroup.center ↥H2 ≃*
          alternatingGroup (Fin s))) := by
  constructor
  · intro hs4
    subst s
    exact __ch5_proposition_5_2_6_doubleCoverPreimage_four_of_root_support n hn f hker
      1 (by norm_num) H2bar eH2 (by simpa using hroot)
  · intro hs5
    exact __ch5_proposition_5_2_6_doubleCoverPreimage_alternating_of_root_support n hn f hker
      s 1 hs5 (by norm_num) H2bar eH2 (by simpa using hroot)

private theorem __ch5_proposition_5_2_6_fixedSubgroup_map_eq_of_not_dvd_kernel
    {G H : Type*} [Group G] [Finite G] [Group H]
    (p : Nat) (hp : p.Prime)
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (y : G) (hy : orderOf y = p)
    (hcop : ¬ p ∣ Nat.card f.ker) :
    (automorphismFixedSubgroup (MulAut.conj y)).map f =
      automorphismFixedSubgroup (MulAut.conj (f y)) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := ha
    change y * a * y⁻¹ = a at ha'
    change f y * f a * (f y)⁻¹ = f a
    simpa using congrArg f ha'
  · intro hb
    obtain ⟨a, rfl⟩ := hf b
    have hfa : Commute (f y) (f a) := by
      have hb' := hb
      change f y * f a * (f y)⁻¹ = f a at hb'
      rw [commute_iff_eq]
      have h := congrArg (fun z : H => z * f y) hb'
      simpa [mul_assoc] using h
    let Y : Subgroup G := Subgroup.zpowers y
    have hcKer : ∀ z : Y, ⁅z.1, a⁆ ∈ f.ker := by
      intro z
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply commutatorElement_eq_one_iff_commute.mpr
      obtain ⟨n, hn⟩ := z.2
      rw [← hn, map_zpow]
      exact hfa.zpow_left n
    have hcCenter : ∀ z : Y, ⁅z.1, a⁆ ∈ Subgroup.center G :=
      fun z => hker (hcKer z)
    let phiZ : Y →* Subgroup.center G :=
      __ch5_proposition_5_2_6_centralCommutatorHom Y.subtype a hcCenter
    let phi : Y →* f.ker := {
      toFun := fun z => ⟨(phiZ z).1, hcKer z⟩
      map_one' := by
        apply Subtype.ext
        change (phiZ 1).1 = 1
        exact congrArg Subtype.val (map_one phiZ)
      map_mul' := by
        intro z w
        apply Subtype.ext
        change (phiZ (z * w)).1 = (phiZ z).1 * (phiZ w).1
        exact congrArg Subtype.val (map_mul phiZ z w) }
    let yY : Y := ⟨y, Subgroup.mem_zpowers y⟩
    have hyPow : y ^ p = 1 := by
      rw [← hy]
      exact pow_orderOf_eq_one y
    have hyYPow : yY ^ p = 1 := by
      apply Subtype.ext
      exact hyPow
    have hphiPow : phi yY ^ p = 1 := by
      rw [← map_pow, hyYPow, map_one]
    have hord : orderOf (phi yY) ∣ p :=
      orderOf_dvd_iff_pow_eq_one.mpr hphiPow
    have hphiOne : phi yY = 1 := by
      rcases (Nat.dvd_prime hp).mp hord with h1 | hp'
      · exact orderOf_eq_one_iff.mp h1
      · exfalso
        apply hcop
        rw [← hp']
        exact orderOf_dvd_natCard (phi yY)
    have hcommYA : Commute y a := by
      apply commutatorElement_eq_one_iff_commute.mp
      have h := congrArg Subtype.val hphiOne
      change ⁅y, a⁆ = 1 at h
      exact h
    refine ⟨a, ?_, rfl⟩
    change y * a * y⁻¹ = a
    rw [hcommYA.eq, mul_inv_cancel_right]

private theorem __ch5_proposition_5_2_6_coveringKernel_cyclic_card_three_or_six
    {L K A : Type}
    [Group L] [Finite L] [IsQuasisimple L]
    [Group K] [Finite K] [IsQuasisimple K]
    [Group A] [Finite A] [IsQuasisimple A]
    (f₀ : Covering L A) (hf₀ : Covering.IsUniversal.{0, 0, 0} f₀)
    (hcyc : IsCyclic f₀.toMonoidHom.ker)
    (hcard : Nat.card f₀.toMonoidHom.ker = 6)
    (f : Covering K A) (hthree : 3 ∣ Nat.card f.toMonoidHom.ker) :
    IsCyclic f.toMonoidHom.ker ∧
      (Nat.card f.toMonoidHom.ker = 3 ∨
        Nat.card f.toMonoidHom.ker = 6) := by
  let lift : Covering L K := Covering.IsUniversal.lift hf₀ f
  let phi : f₀.toMonoidHom.ker →* f.toMonoidHom.ker :=
    (lift.toMonoidHom.comp f₀.toMonoidHom.ker.subtype).codRestrict
      f.toMonoidHom.ker (by
        intro x
        rw [MonoidHom.mem_ker]
        change f (lift x.1) = 1
        have hfac (z : L) : f (lift z) = f₀ z := by
          simpa [lift] using
            DFunLike.congr_fun (Covering.IsUniversal.lift_fac hf₀ f) z
        rw [hfac x.1]
        exact MonoidHom.mem_ker.mp x.2)
  have hphi : Function.Surjective phi := by
    intro y
    have hy : y.1 ∈ Subgroup.map lift.toMonoidHom f₀.toMonoidHom.ker := by
      rw [show lift = Covering.IsUniversal.lift hf₀ f by rfl,
        Covering.coveringKernel_image_of_universal f₀ hf₀ f]
      exact y.2
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  have hcycKer : IsCyclic f.toMonoidHom.ker :=
    isCyclic_of_surjective phi hphi
  have hdvd :=
    Covering.coveringKernel_card_dvd_of_universal f₀ hf₀ f
  rw [hcard] at hdvd
  have hle : Nat.card f.toMonoidHom.ker ≤ 6 :=
    Nat.le_of_dvd (by norm_num : 0 < 6) hdvd
  have hpos : 0 < Nat.card f.toMonoidHom.ker := Nat.card_pos
  rcases hthree with ⟨a, ha⟩
  exact ⟨hcycKer, by omega⟩

private theorem __ch5_proposition_5_2_6_center_card_eq_three_of_card_eq_twenty_seven_of_noncommutative
    {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 27) (hncomm : ¬ IsMulCommutative P) :
    Nat.card (Subgroup.center P) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardPow : Nat.card P = 3 ^ 3 := by simpa using hcard
  obtain ⟨k, hkpos, hcenter⟩ :=
    IsPGroup.card_center_eq_prime_pow hcardPow (by norm_num)
  have hk_dvd : 3 ^ k ∣ 3 ^ 3 := by
    rw [← hcenter, ← hcardPow]
    simpa [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le
        (show Subgroup.center P ≤ (⊤ : Subgroup P) from le_top))
  have hkle : k ≤ 3 :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk_dvd
  have hkCases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkCases with hk1 | hk23
  · simpa [hk1] using hcenter
  · rcases hk23 with hk2 | hk3
    · have hindex : (Subgroup.center P).index = 3 := by
        have hmul := (Subgroup.center P).card_mul_index
        rw [hcenter, hk2, hcard] at hmul
        omega
      have hquotCard : Nat.card (P ⧸ Subgroup.center P) = 3 := by
        rw [← Subgroup.index_eq_card]
        exact hindex
      let : IsCyclic (P ⧸ Subgroup.center P) :=
        isCyclic_of_card_dvd_prime (by rw [hquotCard])
      exact (hncomm
        (isMulCommutative_of_isCyclic_quotient_center_self P)).elim
    · have hcenterCard : Nat.card (Subgroup.center P) = Nat.card P := by
        rw [hcenter, hk3, hcardPow]
      have hcenterTop : Subgroup.center P = ⊤ :=
        (Subgroup.card_eq_iff_eq_top _).mp hcenterCard
      exact (hncomm (Subgroup.center_eq_top_iff.mp hcenterTop)).elim

private theorem __ch5_proposition_5_2_6_sylow3_structure_of_mulEquiv
    {K G : Type*} [Group K] [Finite K] [Group G] [Finite G]
    (e : K ≃* G)
    (hG : ∀ Q : Sylow 3 G,
      Nat.card (Q : Subgroup G) = 27 ∧
        Nat.card (Subgroup.center (Q : Subgroup G)) = 3) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  intro P
  let Q : Sylow 3 G :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ := hG Q
  let eP : P ≃* Q := by
    change P ≃* P.map e.toMonoidHom
    exact e.subgroupMap P
  exact ⟨(Nat.card_congr eP.toEquiv).trans hQ.1,
    (Nat.card_congr (Subgroup.centerCongr eP).toEquiv).trans hQ.2⟩

private theorem __ch5_proposition_5_2_6_tripleCoverA7_sylow3
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, hcyc, hcard⟩ :=
    theorem_5_2_3_c_multiplier_a7
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, hgker, hgSylow⟩ :=
    theorem_5_2_3_d_sylow3_3A7
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  obtain ⟨e, _, _⟩ :=
    coveringIso_of_cyclic_kernel_card_six_of_kernel_card_three
      f₀ hf₀ hcyc hcard f g hker hgker
  exact __ch5_proposition_5_2_6_sylow3_structure_of_mulEquiv e hgSylow

private theorem __ch5_proposition_5_2_6_nonempty_mulEquiv_of_universal_kernel_card_eq
    {L K A : Type}
    [Group L] [Finite L] [IsQuasisimple L]
    [Group K] [Finite K] [IsQuasisimple K]
    [Group A] [Finite A] [IsQuasisimple A]
    (f₀ : Covering L A) (hf₀ : Covering.IsUniversal.{0, 0, 0} f₀)
    (f : Covering K A)
    (hcard : Nat.card f₀.toMonoidHom.ker =
      Nat.card f.toMonoidHom.ker) : Nonempty (L ≃* K) := by
  let lift : Covering L K := Covering.IsUniversal.lift hf₀ f
  have hLcard : Nat.card L =
      Nat.card A * Nat.card f₀.toMonoidHom.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul f₀.toMonoidHom f₀.surjective
        (⊤ : Subgroup A)
  have hKcard : Nat.card K =
      Nat.card A * Nat.card f.toMonoidHom.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
        (⊤ : Subgroup A)
  have hLKcard : Nat.card L = Nat.card K := by
    rw [hLcard, hKcard, hcard]
  have hbij : Function.Bijective lift := by
    have : Fintype L := Fintype.ofFinite L
    have : Fintype K := Fintype.ofFinite K
    apply (Fintype.bijective_iff_surjective_and_card lift).2
    refine ⟨lift.surjective, ?_⟩
    simpa [Nat.card_eq_fintype_card] using hLKcard
  exact ⟨MulEquiv.ofBijective lift.toMonoidHom hbij⟩

private theorem __ch5_proposition_5_2_6_sylow3_structure_of_surjection_to_model
    {K G : Type} [Group K] [Finite K] [IsQuasisimple K]
    [Group G] [Finite G] [IsQuasisimple G]
    (psi : Covering K G)
    (hKcard : ∀ P : Sylow 3 K, Nat.card (P : Subgroup K) = 27)
    (hG : ∀ Q : Sylow 3 G,
      Nat.card (Q : Subgroup G) = 27 ∧
        Nat.card (Subgroup.center (Q : Subgroup G)) = 3) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  intro P
  let Q : Sylow 3 G := P.mapSurjective psi.surjective
  have hQ := hG Q
  have hPnoncomm : ¬ IsMulCommutative P := by
    intro hPcomm
    let : IsMulCommutative P := hPcomm
    have hQcomm : IsMulCommutative Q := by
      rw [show (Q : Subgroup G) = (P : Subgroup K).map psi.toMonoidHom by
        simp [Q]]
      exact Subgroup.map_isMulCommutative (P : Subgroup K) psi.toMonoidHom
    let : IsMulCommutative Q := hQcomm
    have hcenterTop : Subgroup.center Q = ⊤ := Subgroup.center_eq_top
    have hcenterCard : Nat.card (Subgroup.center Q) = 27 := by
      rw [hcenterTop, Subgroup.card_top, hQ.1]
    omega
  exact ⟨hKcard P,
    __ch5_proposition_5_2_6_center_card_eq_three_of_card_eq_twenty_seven_of_noncommutative
      (hKcard P) hPnoncomm⟩

private theorem __ch5_proposition_5_2_6_sixCoverA6_sylow3
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 6) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, _, hcard₀⟩ :=
    theorem_5_2_3_c_multiplier_a6
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, _, hgSylow⟩ :=
    theorem_5_2_3_d_sylow3_3A6
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  obtain ⟨e⟩ := __ch5_proposition_5_2_6_nonempty_mulEquiv_of_universal_kernel_card_eq
    f₀ hf₀ f (hcard₀.trans hker.symm)
  let psi₀ : Covering L₀ G := Covering.IsUniversal.lift hf₀ g
  let psi : Covering K G := psi₀.comp (Covering.ofMulEquiv e.symm)
  have hKcard : Nat.card K = 2160 := by
    have h : Nat.card K = Nat.card (alternatingGroup (Fin 6)) *
        Nat.card f.toMonoidHom.ker := by
      simpa only [Subgroup.comap_top, Subgroup.card_top] using
        SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
          (⊤ : Subgroup (alternatingGroup (Fin 6)))
    have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hker, hA] at h
    omega
  have hPcard : ∀ P : Sylow 3 K, Nat.card (P : Subgroup K) = 27 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    intro P
    have hfac : (2160).factorization 3 = 3 := by
      have hzero : padicValNat 3 80 = 0 :=
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
      rw [Nat.factorization_def 2160 Nat.prime_three,
        show (2160 : Nat) = 3 ^ 3 * 80 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]
    rw [Sylow.card_eq_multiplicity, hKcard, hfac]
    norm_num
  exact __ch5_proposition_5_2_6_sylow3_structure_of_surjection_to_model psi hPcard hgSylow

private theorem __ch5_proposition_5_2_6_sixCoverA7_sylow3
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 6) :
    ∀ P : Sylow 3 K,
      Nat.card (P : Subgroup K) = 27 ∧
        Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
  obtain ⟨L₀, instL₀, finL₀, qsL₀, f₀, hf₀, _, hcard₀⟩ :=
    theorem_5_2_3_c_multiplier_a7
  let : Group L₀ := instL₀
  let : Finite L₀ := finL₀
  let : IsQuasisimple L₀ := qsL₀
  obtain ⟨G, instG, finG, qsG, g, _, hgSylow⟩ :=
    theorem_5_2_3_d_sylow3_3A7
  let : Group G := instG
  let : Finite G := finG
  let : IsQuasisimple G := qsG
  obtain ⟨e⟩ := __ch5_proposition_5_2_6_nonempty_mulEquiv_of_universal_kernel_card_eq
    f₀ hf₀ f (hcard₀.trans hker.symm)
  let psi₀ : Covering L₀ G := Covering.IsUniversal.lift hf₀ g
  let psi : Covering K G := psi₀.comp (Covering.ofMulEquiv e.symm)
  have hKcard : Nat.card K = 15120 := by
    have h : Nat.card K = Nat.card (alternatingGroup (Fin 7)) *
        Nat.card f.toMonoidHom.ker := by
      simpa only [Subgroup.comap_top, Subgroup.card_top] using
        SchurPresentation.card_comap_mul f.toMonoidHom f.surjective
          (⊤ : Subgroup (alternatingGroup (Fin 7)))
    have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hker, hA] at h
    omega
  have hPcard : ∀ P : Sylow 3 K, Nat.card (P : Subgroup K) = 27 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    intro P
    have hfac : (15120).factorization 3 = 3 := by
      have hzero : padicValNat 3 560 = 0 :=
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
      rw [Nat.factorization_def 15120 Nat.prime_three,
        show (15120 : Nat) = 3 ^ 3 * 560 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 3, hzero]
    rw [Sylow.card_eq_multiplicity, hKcard, hfac]
    norm_num
  exact __ch5_proposition_5_2_6_sylow3_structure_of_surjection_to_model psi hPcard hgSylow

private theorem __ch5_proposition_5_2_6_fixedSubgroup_image_index_eq_three_of_failure
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (hkerCard : Nat.card f.ker = 3 ∨ Nat.card f.ker = 6)
    (y : G) (hy : orderOf y = 3)
    (hneq :
      (automorphismFixedSubgroup (MulAut.conj y)).map f ≠
        automorphismFixedSubgroup (MulAut.conj (f y))) :
    ∃ _hle :
        (automorphismFixedSubgroup (MulAut.conj y)).map f ≤
          automorphismFixedSubgroup (MulAut.conj (f y)),
      (((automorphismFixedSubgroup (MulAut.conj y)).map f).subgroupOf
          (automorphismFixedSubgroup (MulAut.conj (f y)))).index = 3 := by
  let C := automorphismFixedSubgroup (MulAut.conj y)
  let Cbar := automorphismFixedSubgroup (MulAut.conj (f y))
  have hle : C.map f ≤ Cbar := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' := ha
    change y * a * y⁻¹ = a at ha'
    change f y * f a * (f y)⁻¹ = f a
    simpa using congrArg f ha'
  let E := Cbar.comap f
  have hCE : C ≤ E := by
    intro a ha
    exact hle ⟨a, ha, rfl⟩
  let q : E →* Cbar :=
    (f.comp E.subtype).codRestrict Cbar (fun a => a.2)
  have hq : Function.Surjective q := by
    intro b
    obtain ⟨a, ha⟩ := hf b.1
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact b.2
    refine ⟨⟨a, haE⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hcKer : ∀ a : E, ⁅a.1, y⁆ ∈ f.ker := by
    intro a
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply commutatorElement_eq_one_iff_commute.mpr
    have ha := a.2
    change f y * f a.1 * (f y)⁻¹ = f a.1 at ha
    have hcomm : Commute (f y) (f a.1) := by
      rw [commute_iff_eq]
      have h := congrArg (fun z : H => z * f y) ha
      simpa [mul_assoc] using h
    exact hcomm.symm
  have hcCenter : ∀ a : E, ⁅a.1, y⁆ ∈ Subgroup.center G :=
    fun a => hker (hcKer a)
  let deltaCenter : E →* Subgroup.center G :=
    __ch5_proposition_5_2_6_centralCommutatorHom E.subtype y hcCenter
  let delta : E →* f.ker := {
    toFun := fun a => ⟨(deltaCenter a).1, hcKer a⟩
    map_one' := by
      apply Subtype.ext
      change (deltaCenter 1).1 = 1
      exact congrArg Subtype.val (map_one deltaCenter)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change (deltaCenter (a * b)).1 =
        (deltaCenter a).1 * (deltaCenter b).1
      exact congrArg Subtype.val (map_mul deltaCenter a b) }
  have hdeltaKer : delta.ker = C.subgroupOf E := by
    ext a
    constructor
    · intro ha
      have haOne : ⁅a.1, y⁆ = 1 := by
        have h := MonoidHom.mem_ker.mp ha
        exact congrArg Subtype.val h
      have hcomm : Commute a.1 y :=
        commutatorElement_eq_one_iff_commute.mp haOne
      change y * a.1 * y⁻¹ = a.1
      rw [← hcomm.eq, mul_inv_cancel_right]
    · intro ha
      have haC : a.1 ∈ C := ha
      have haFixed := haC
      change y * a.1 * y⁻¹ = a.1 at haFixed
      have hcomm : Commute y a.1 := by
        rw [commute_iff_eq]
        have h := congrArg (fun z : G => z * y) haFixed
        simpa [mul_assoc] using h
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      change ⁅a.1, y⁆ = 1
      exact commutatorElement_eq_one_iff_commute.mpr hcomm.symm
  have hdeltaPow : ∀ a : E, delta a ^ 3 = 1 := by
    intro a
    let Y : Subgroup G := Subgroup.zpowers y
    have hcKerY : ∀ z : Y, ⁅z.1, a.1⁆ ∈ f.ker := by
      intro z
      rw [MonoidHom.mem_ker, map_commutatorElement]
      apply commutatorElement_eq_one_iff_commute.mpr
      obtain ⟨m, hm⟩ := z.2
      rw [← hm, map_zpow]
      have ha := a.2
      change f y * f a.1 * (f y)⁻¹ = f a.1 at ha
      have hcomm : Commute (f y) (f a.1) := by
        rw [commute_iff_eq]
        have h := congrArg (fun w : H => w * f y) ha
        simpa [mul_assoc] using h
      exact hcomm.zpow_left m
    have hcCenterY : ∀ z : Y, ⁅z.1, a.1⁆ ∈ Subgroup.center G :=
      fun z => hker (hcKerY z)
    let phiCenter : Y →* Subgroup.center G :=
      __ch5_proposition_5_2_6_centralCommutatorHom Y.subtype a.1 hcCenterY
    let phi : Y →* f.ker := {
      toFun := fun z => ⟨(phiCenter z).1, hcKerY z⟩
      map_one' := by
        apply Subtype.ext
        change (phiCenter 1).1 = 1
        exact congrArg Subtype.val (map_one phiCenter)
      map_mul' := by
        intro z w
        apply Subtype.ext
        change (phiCenter (z * w)).1 =
          (phiCenter z).1 * (phiCenter w).1
        exact congrArg Subtype.val (map_mul phiCenter z w) }
    let yY : Y := ⟨y, Subgroup.mem_zpowers y⟩
    have hyPow : y ^ 3 = 1 := by
      rw [← hy]
      exact pow_orderOf_eq_one y
    have hyYPow : yY ^ 3 = 1 := by
      apply Subtype.ext
      exact hyPow
    have hphiPow : phi yY ^ 3 = 1 := by
      rw [← map_pow, hyYPow, map_one]
    apply Subtype.ext
    have hcommPow : ⁅y, a.1⁆ ^ 3 = 1 := by
      exact congrArg Subtype.val hphiPow
    change ⁅a.1, y⁆ ^ 3 = 1
    rw [← commutatorElement_inv]
    simpa only [inv_pow, inv_eq_one] using hcommPow
  have hdeltaP : IsPGroup 3 delta.range := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [IsPGroup.iff_orderOf]
    intro z
    have hzPow : z ^ 3 = 1 := by
      obtain ⟨a, ha⟩ := z.2
      apply Subtype.ext
      simpa [ha] using hdeltaPow a
    have hord : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hzPow
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h3⟩
  have hdeltaRangeNe : delta.range ≠ ⊥ := by
    intro hrange
    apply hneq
    apply le_antisymm hle
    intro b hb
    obtain ⟨a, ha⟩ := hf b
    have haE : a ∈ E := by
      change f a ∈ Cbar
      rw [ha]
      exact hb
    let aE : E := ⟨a, haE⟩
    have hdeltaOne : delta aE = 1 := by
      have hmem : delta aE ∈ delta.range := ⟨aE, rfl⟩
      rw [hrange] at hmem
      exact Subgroup.mem_bot.mp hmem
    have haComm : Commute a y := by
      apply commutatorElement_eq_one_iff_commute.mp
      exact congrArg Subtype.val hdeltaOne
    have haC : a ∈ C := by
      change y * a * y⁻¹ = a
      rw [← haComm.eq, mul_inv_cancel_right]
    exact ⟨a, haC, ha⟩
  have hthreeDvdRange : 3 ∣ Nat.card delta.range := by
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hdeltaRangeNe
    have hord : orderOf z = 3 := by
      have hzPow : z ^ 3 = 1 := by
        obtain ⟨a, ha⟩ := z.2
        apply Subtype.ext
        simpa [ha] using hdeltaPow a
      let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hzPow hz
    rw [← hord]
    exact orderOf_dvd_natCard z
  have hRangeDvdKer : Nat.card delta.range ∣ Nat.card f.ker := by
    simpa [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le
        (show delta.range ≤ (⊤ : Subgroup f.ker) from le_top))
  have hdeltaRangeCard : Nat.card delta.range = 3 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hdeltaP)
    rcases hkerCard with h3 | h6
    · rw [h3] at hRangeDvdKer
      exact Nat.dvd_antisymm hRangeDvdKer hthreeDvdRange
    · rw [h6] at hRangeDvdKer
      have hle6 : Nat.card delta.range ≤ 6 :=
        Nat.le_of_dvd (by norm_num) hRangeDvdKer
      have hmod : Nat.card delta.range % 3 = 0 :=
        Nat.mod_eq_zero_of_dvd hthreeDvdRange
      have hcases : Nat.card delta.range = 3 ∨ Nat.card delta.range = 6 := by
        let m := Nat.card delta.range
        have hmpos : 0 < m := Nat.card_pos
        have hmle : m ≤ 6 := hle6
        have hmmod : m % 3 = 0 := hmod
        change m = 3 ∨ m = 6
        omega
      rcases hcases with h3 | h6'
      · exact h3
      · exfalso
        have hodd : Odd (Nat.card delta.range) := by
          rw [hk]
          have hthreeOdd : Odd 3 := ⟨1, by norm_num⟩
          exact hthreeOdd.pow
        rw [h6'] at hodd
        rcases hodd with ⟨m, hm⟩
        omega
  have hCindexE : (C.subgroupOf E).index = 3 := by
    calc
      (C.subgroupOf E).index = delta.ker.index :=
        congrArg Subgroup.index hdeltaKer.symm
      _ = Nat.card delta.range := Subgroup.index_ker delta
      _ = 3 := hdeltaRangeCard
  have hqker : q.ker ≤ C.subgroupOf E := by
    intro a ha
    have hfa : f a.1 = 1 := by
      have h := MonoidHom.mem_ker.mp ha
      exact congrArg Subtype.val h
    have haCenter : a.1 ∈ Subgroup.center G := by
      apply hker
      exact MonoidHom.mem_ker.mpr hfa
    change y * a.1 * y⁻¹ = a.1
    have hcomm : Commute y a.1 :=
      Subgroup.mem_center_iff.mp haCenter y
    rw [hcomm.eq, mul_inv_cancel_right]
  have hmap : (C.subgroupOf E).map q = (C.map f).subgroupOf Cbar := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      change f a.1 ∈ C.map f
      exact ⟨a.1, ha, rfl⟩
    · intro hb
      change b.1 ∈ C.map f at hb
      obtain ⟨a, haC, ha⟩ := hb
      have haE : a ∈ E := hCE haC
      let aE : E := ⟨a, haE⟩
      refine ⟨aE, ?_, ?_⟩
      · exact haC
      · apply Subtype.ext
        exact ha
  refine ⟨hle, ?_⟩
  rw [← hmap]
  exact (Subgroup.index_map_eq (C.subgroupOf E) hq hqker).trans hCindexE

private theorem __ch5_proposition_5_2_6_three_dvd_coveringKernel_implies_degree_six_or_seven
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) (hn : 5 ≤ n)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (f : Covering K (alternatingGroup (Fin n)))
    (hthree : 3 ∣ Nat.card f.toMonoidHom.ker) :
    n = 6 ∨ n = 7 := by
  by_contra h
  have h6 : n ≠ 6 := fun hn6 => h (Or.inl hn6)
  have h7 : n ≠ 7 := fun hn7 => h (Or.inr hn7)
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  have hq6 : q + 5 ≠ 6 := by simpa [hq] using h6
  have hq7 : q + 5 ≠ 7 := by simpa [hq] using h7
  let e : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := e.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f.toMonoidHom
  have hf'ker : f'.ker = f.toMonoidHom.ker := by
    rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
      MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom eA.injective]
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp f.surjective
  }
  have hdiv : Nat.card f'.ker ∣ 2 := by
    have hkernel := Covering.coveringKernel_card_dvd_of_universal
      (SchurPresentation.schurAlternatingCovering q)
      (SchurPresentation.theorem_5_2_3_b_universality q hq6 hq7) c
    rw [SchurPresentation.theorem_5_2_3_a q] at hkernel
    simpa [c] using hkernel
  have : 3 ∣ 2 := by
    apply hthree.trans
    rwa [← hf'ker]
  norm_num at this

private theorem __ch5_proposition_5_2_6_odd_prime_dvd_coveringKernel_eq_three
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (f : Covering K (alternatingGroup (Fin n)))
    (hpker : p ∣ Nat.card f.toMonoidHom.ker) : p = 3 := by
  by_contra hp3
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  let q := n - 5
  have hq : q + 5 = n := Nat.sub_add_cancel hn
  let e : Fin (q + 5) ≃ Fin n := finCongr hq
  let eA := e.symm.altCongrHom
  let f' : K →* alternatingGroup (Fin (q + 5)) :=
    eA.toMonoidHom.comp f.toMonoidHom
  have hf'ker : f'.ker = f.toMonoidHom.ker := by
    rw [show f' = eA.toMonoidHom.comp f.toMonoidHom by rfl,
      MonoidHom.ker_comp_of_injective f.toMonoidHom eA.toMonoidHom eA.injective]
  let c : Covering K (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f'
    surjective := eA.surjective.comp f.surjective
  }
  have hdiv : Nat.card f'.ker ∣
      Nat.card (SchurPresentation.alternatingFreeCentralCovering q).toMonoidHom.ker := by
    simpa [c] using Covering.coveringKernel_card_dvd_of_universal
      (SchurPresentation.alternatingFreeCentralCovering q)
      (SchurPresentation.alternatingFreeCentralCovering_isUniversal q) c
  apply SchurPresentation.not_dvd_natCard_ker_alternatingFreeCentralCovering_of_five_le_prime
    p q hp hp5
  have hpker' : p ∣ Nat.card f'.ker := by
    rwa [hf'ker]
  exact hpker'.trans hdiv

private theorem __ch5_proposition_5_2_6_exceptional_alternating_fixed_sylow3_card
    (n : Nat) (hn : n = 6 ∨ n = 7)
    (y : alternatingGroup (Fin n)) (hy : orderOf y = 3) :
    ∀ Q : Sylow 3 (automorphismFixedSubgroup (MulAut.conj y)),
      Nat.card (Q : Subgroup
        (automorphismFixedSubgroup (MulAut.conj y))) = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Cbar := automorphismFixedSubgroup (MulAut.conj y)
  have hAfactor :
      (Nat.card (alternatingGroup (Fin n))).factorization 3 = 2 := by
    rcases hn with hn6 | hn7
    · subst n
      have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      rw [hcard, Nat.factorization_def 360 Nat.prime_three,
        show (360 : Nat) = 3 ^ 2 * 40 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 2,
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]
    · subst n
      have hcard : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      rw [hcard, Nat.factorization_def 2520 Nat.prime_three,
        show (2520 : Nat) = 3 ^ 2 * 280 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 2,
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]
  have hAmbientSylow : ∀ P : Sylow 3 (alternatingGroup (Fin n)),
      Nat.card (P : Subgroup (alternatingGroup (Fin n))) = 9 := by
    intro P
    rw [Sylow.card_eq_multiplicity, hAfactor]
    norm_num
  let Y : Subgroup (alternatingGroup (Fin n)) := Subgroup.zpowers y
  have hYp : IsPGroup 3 Y := by
    apply IsPGroup.of_card (p := 3) (n := 1)
    rw [Nat.card_zpowers, hy]
    norm_num
  obtain ⟨P, hYP⟩ := hYp.exists_le_sylow
  have hPcomm : IsMulCommutative P := by
    apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    simpa using hAmbientSylow P
  have hPCbar : (P : Subgroup (alternatingGroup (Fin n))) ≤ Cbar := by
    intro a ha
    let aP : P := ⟨a, ha⟩
    let yP : P := ⟨y, hYP (Subgroup.mem_zpowers y)⟩
    have hcomm : Commute y a := by
      rw [commute_iff_eq]
      exact congrArg Subtype.val (hPcomm.is_comm.comm yP aP)
    change y * a * y⁻¹ = a
    rw [hcomm.eq, mul_inv_cancel_right]
  let PC : Subgroup Cbar :=
    (P : Subgroup (alternatingGroup (Fin n))).subgroupOf Cbar
  have hPCcard : Nat.card PC = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPCbar).toEquiv,
      hAmbientSylow P]
  have hPCp : IsPGroup 3 PC := by
    apply IsPGroup.of_card (p := 3) (n := 2)
    rw [hPCcard]
    norm_num
  obtain ⟨Q0, hPCQ0⟩ := hPCp.exists_le_sylow
  have hQ0lower : 9 ≤ Nat.card (Q0 : Subgroup Cbar) := by
    rw [← hPCcard]
    exact Subgroup.card_le_of_le hPCQ0
  let Q0A : Subgroup (alternatingGroup (Fin n)) :=
    (Q0 : Subgroup Cbar).map Cbar.subtype
  have hQ0Ap : IsPGroup 3 Q0A := Q0.isPGroup'.map Cbar.subtype
  obtain ⟨R, hQ0AR⟩ := hQ0Ap.exists_le_sylow
  have hQ0mapCard : Nat.card Q0A = Nat.card (Q0 : Subgroup Cbar) := by
    dsimp [Q0A]
    exact Subgroup.card_map_of_injective Cbar.subtype_injective
  have hQ0upper : Nat.card (Q0 : Subgroup Cbar) ≤ 9 := by
    rw [← hQ0mapCard, ← hAmbientSylow R]
    exact Subgroup.card_le_of_le hQ0AR
  have hQ0card : Nat.card (Q0 : Subgroup Cbar) = 9 := by omega
  intro Q
  have hcardCongr : Nat.card (Q : Subgroup Cbar) =
      Nat.card (Q0 : Subgroup Cbar) :=
    Nat.card_congr (Sylow.equiv Q Q0).toEquiv
  exact hcardCongr.trans hQ0card

set_option linter.unusedVariables false in
private theorem __ch5_proposition_5_2_6_fixedSubgroup_sylow3_card_nine_of_exceptional
    {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G)
    (hkerCard : Nat.card f.ker = 3 ∨ Nat.card f.ker = 6)
    (y : G) (hy : orderOf y = 3)
    (hindex : ∃ _hle :
      (automorphismFixedSubgroup (MulAut.conj y)).map f ≤
        automorphismFixedSubgroup (MulAut.conj (f y)),
      (((automorphismFixedSubgroup (MulAut.conj y)).map f).subgroupOf
        (automorphismFixedSubgroup (MulAut.conj (f y)))).index = 3)
    (hCbarSylow : ∀ S : Sylow 3
      (automorphismFixedSubgroup (MulAut.conj (f y))),
      Nat.card (S : Subgroup
        (automorphismFixedSubgroup (MulAut.conj (f y)))) = 9) :
    ∀ Q : Sylow 3 (automorphismFixedSubgroup (MulAut.conj y)),
      Nat.card (Q : Subgroup
        (automorphismFixedSubgroup (MulAut.conj y))) = 9 ∧
        IsMulCommutative (Q : Subgroup
          (automorphismFixedSubgroup (MulAut.conj y))) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C := automorphismFixedSubgroup (MulAut.conj y)
  let Cbar := automorphismFixedSubgroup (MulAut.conj (f y))
  let I := C.map f
  obtain ⟨hle, hIindex⟩ := hindex
  have hCbarFactor : (Nat.card Cbar).factorization 3 = 2 := by
    let S : Sylow 3 Cbar := default
    have hpow : 3 ^ (Nat.card Cbar).factorization 3 = 3 ^ 2 := by
      calc
        3 ^ (Nat.card Cbar).factorization 3 =
            Nat.card (S : Subgroup Cbar) :=
          (Sylow.card_eq_multiplicity S).symm
        _ = 9 := hCbarSylow S
        _ = 3 ^ 2 := by norm_num
    exact Nat.pow_right_injective (by norm_num) hpow
  have hIcard : Nat.card I * 3 = Nat.card Cbar := by
    have h := (I.subgroupOf Cbar).card_mul_index
    rw [hIindex] at h
    have hsubCard : Nat.card (I.subgroupOf Cbar) = Nat.card I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rwa [hsubCard] at h
  have hthreeFactor : (3 : Nat).factorization 3 = 1 :=
    Nat.prime_three.factorization_self
  have hIFactor : (Nat.card I).factorization 3 = 1 := by
    have h := congrArg (fun m : Nat => m.factorization 3) hIcard
    rw [Nat.factorization_mul Nat.card_pos.ne' (by norm_num)] at h
    change (Nat.card I).factorization 3 + (3 : Nat).factorization 3 =
      (Nat.card Cbar).factorization 3 at h
    rw [hthreeFactor, hCbarFactor] at h
    omega
  have hkerC : f.ker ≤ C := by
    intro z hz
    have hzCenter : z ∈ Subgroup.center G := hker hz
    have hcomm : Commute y z := Subgroup.mem_center_iff.mp hzCenter y
    change y * z * y⁻¹ = z
    rw [hcomm.eq, mul_inv_cancel_right]
  let r : C →* I :=
    (f.comp C.subtype).codRestrict I (fun c => ⟨c.1, c.2, rfl⟩)
  have hr : Function.Surjective r := by
    intro b
    obtain ⟨a, haC, ha⟩ := b.2
    refine ⟨⟨a, haC⟩, ?_⟩
    apply Subtype.ext
    exact ha
  have hrker : r.ker = f.ker.subgroupOf C := by
    ext a
    change r a = 1 ↔ f a.1 = 1
    constructor
    · intro ha
      exact congrArg Subtype.val ha
    · intro ha
      apply Subtype.ext
      exact ha
  have hrkerCard : Nat.card r.ker = Nat.card f.ker := by
    rw [hrker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerC).toEquiv
  have hrkerFactor : (Nat.card r.ker).factorization 3 = 1 := by
    rw [hrkerCard]
    rcases hkerCard with h3 | h6
    · rw [h3]
      exact hthreeFactor
    · rw [h6, Nat.factorization_def 6 Nat.prime_three,
        show (6 : Nat) = 3 ^ 1 * 2 by norm_num,
        padicValNat_base_pow_mul (by norm_num) (by norm_num) 1,
        padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))]
  have hCcard : Nat.card C = Nat.card I * Nat.card r.ker := by
    simpa only [Subgroup.comap_top, Subgroup.card_top] using
      SchurPresentation.card_comap_mul r hr (⊤ : Subgroup I)
  have hCFactor : (Nat.card C).factorization 3 = 2 := by
    have h := congrArg (fun m : Nat => m.factorization 3) hCcard
    rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at h
    change (Nat.card C).factorization 3 =
      (Nat.card I).factorization 3 +
        (Nat.card r.ker).factorization 3 at h
    rw [hIFactor, hrkerFactor] at h
    simpa using h
  intro Q
  have hQcard : Nat.card (Q : Subgroup C) = 9 := by
    rw [Sylow.card_eq_multiplicity, hCFactor]
    norm_num
  refine ⟨hQcard, ?_⟩
  apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
  simpa using hQcard

/-- Proposition 5.2.6(e): the fixed subgroup covers the fixed subgroup in
the alternating quotient, except in the exceptional triple-cover cases; in
those cases the image has index three and the Sylow `3`-subgroups have the
stated `3^{1+2}` and `E₉` structures. -/
public theorem proposition_5_2_6_e
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (n p : Nat) (hn : 5 ≤ n) (hp : p.Prime)
    (x : MulAut K) (hxOrder : orderOf x = p)
    [IsQuasisimple (alternatingGroup (Fin n))]
    (hp2 : p ≠ 2)
    (f : Covering K (alternatingGroup (Fin n)))
    (y : K) (hy : orderOf y = p)
    (hx : x = MulAut.conj y) :
    let x := MulAut.conj y
    let C := automorphismFixedSubgroup x
    let Cbar := automorphismFixedSubgroup (MulAut.conj (f y))
    C.map f.toMonoidHom = Cbar ∨
      (p = 3 ∧ (n = 6 ∨ n = 7) ∧
        3 ∣ Nat.card (Subgroup.center K) ∧
        (∃ _hle : C.map f.toMonoidHom ≤ Cbar,
          ((C.map f.toMonoidHom).subgroupOf Cbar).index = 3) ∧
        (∀ P : Sylow 3 K,
          Nat.card (P : Subgroup K) = 27 ∧
            Nat.card (Subgroup.center ↥(P : Subgroup K)) = 3) ∧
        (∀ Q : Sylow 3 C,
          Nat.card (Q : Subgroup C) = 9 ∧ IsMulCommutative ↥(Q : Subgroup C))) := by
  let C := automorphismFixedSubgroup (MulAut.conj y)
  let Cbar := automorphismFixedSubgroup (MulAut.conj (f y))
  by_cases heq : C.map f.toMonoidHom = Cbar
  · exact Or.inl heq
  · right
    let : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa using hn)
    have hfker : f.toMonoidHom.ker = Subgroup.center K :=
      f.ker_eq_center_of_isSimple
    have hpcenter : p ∣ Nat.card (Subgroup.center K) := by
      by_contra hpc
      apply heq
      apply __ch5_proposition_5_2_6_fixedSubgroup_map_eq_of_not_dvd_kernel
        p hp f.toMonoidHom f.surjective f.ker_le_center y hy
      rwa [hfker]
    have hpker : p ∣ Nat.card f.toMonoidHom.ker := by
      rwa [hfker]
    have hp3 : p = 3 :=
      __ch5_proposition_5_2_6_odd_prime_dvd_coveringKernel_eq_three n p hn hp hp2 f hpker
    have hpker3 : 3 ∣ Nat.card f.toMonoidHom.ker := by
      rwa [← hp3]
    have hpcenter3 : 3 ∣ Nat.card (Subgroup.center K) := by
      rwa [← hp3]
    have hy3 : orderOf y = 3 := hy.trans hp3
    have hn67 : n = 6 ∨ n = 7 :=
      __ch5_proposition_5_2_6_three_dvd_coveringKernel_implies_degree_six_or_seven n hn f hpker3
    have hkerCard : Nat.card f.toMonoidHom.ker = 3 ∨
        Nat.card f.toMonoidHom.ker = 6 := by
      rcases hn67 with hn6 | hn7
      · subst n
        obtain ⟨L, instL, finL, qsL, f0, hf0, hcyc, hcard⟩ :=
          theorem_5_2_3_c_multiplier_a6
        let : Group L := instL
        let : Finite L := finL
        let : IsQuasisimple L := qsL
        exact (__ch5_proposition_5_2_6_coveringKernel_cyclic_card_three_or_six
          f0 hf0 hcyc hcard f hpker3).2
      · subst n
        obtain ⟨L, instL, finL, qsL, f0, hf0, hcyc, hcard⟩ :=
          theorem_5_2_3_c_multiplier_a7
        let : Group L := instL
        let : Finite L := finL
        let : IsQuasisimple L := qsL
        exact (__ch5_proposition_5_2_6_coveringKernel_cyclic_card_three_or_six
          f0 hf0 hcyc hcard f hpker3).2
    have hindex : ∃ hle : C.map f.toMonoidHom ≤ Cbar,
        ((C.map f.toMonoidHom).subgroupOf Cbar).index = 3 :=
      __ch5_proposition_5_2_6_fixedSubgroup_image_index_eq_three_of_failure
        f.toMonoidHom f.surjective f.ker_le_center hkerCard y hy3 heq
    have hKSylow : ∀ P : Sylow 3 K,
        Nat.card (P : Subgroup K) = 27 ∧
          Nat.card (Subgroup.center (P : Subgroup K)) = 3 := by
      rcases hn67 with hn6 | hn7
      · subst n
        rcases hkerCard with h3 | h6
        · exact tripleCoverA6_sylow3 f h3
        · exact __ch5_proposition_5_2_6_sixCoverA6_sylow3 f h6
      · subst n
        rcases hkerCard with h3 | h6
        · exact __ch5_proposition_5_2_6_tripleCoverA7_sylow3 f h3
        · exact __ch5_proposition_5_2_6_sixCoverA7_sylow3 f h6
    have hfy : orderOf (f y) = 3 := by
      have hfyPow : (f y) ^ 3 = 1 := by
        rw [← map_pow, ← hy3]
        rw [pow_orderOf_eq_one, map_one]
      have hfyNe : f y ≠ 1 := by
        intro hfyOne
        have hyCenter : y ∈ Subgroup.center K := by
          rw [← hfker]
          exact MonoidHom.mem_ker.mpr hfyOne
        have hconjOne : MulAut.conj y = 1 := by
          ext z
          change y * z * y⁻¹ = z
          have hcomm : Commute y z :=
            (Subgroup.mem_center_iff.mp hyCenter z).symm
          rw [hcomm.eq, mul_inv_cancel_right]
        have hxOne : x = 1 := hx.trans hconjOne
        have : orderOf x = 1 := by rw [hxOne, orderOf_one]
        omega
      let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime hfyPow hfyNe
    have hCbarSylow : ∀ S : Sylow 3 Cbar,
        Nat.card (S : Subgroup Cbar) = 9 :=
      __ch5_proposition_5_2_6_exceptional_alternating_fixed_sylow3_card n hn67 (f y) hfy
    have hCSylow : ∀ Q : Sylow 3 C,
        Nat.card (Q : Subgroup C) = 9 ∧
          IsMulCommutative (Q : Subgroup C) :=
      __ch5_proposition_5_2_6_fixedSubgroup_sylow3_card_nine_of_exceptional
        f.toMonoidHom f.surjective f.ker_le_center hkerCard y hy3
        hindex hCbarSylow
    exact ⟨hp3, hn67, hpcenter3, hindex, hKSylow, hCSylow⟩

end GLS3.Chapter5
/- END KGroup.GLS3.Chapter5.proposition_5_2_6 -/

/- BEGIN Theory.CenterCoreLeDerivedAlternatingPreimage -/
namespace GLS3.Chapter5
open SchurPresentation

/-- In a double cover, the center of the covering group is contained in the
commutator of the full preimage of an alternating factor. -/
public theorem center_le_derived_alternating_preimage_of_double_cover
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (n : Nat) [IsQuasisimple (alternatingGroup (Fin n))]
    (hn : 5 ≤ n) (s : Nat) (hs : 5 ≤ s)
    (f : Covering K (alternatingGroup (Fin n)))
    (hker : Nat.card f.toMonoidHom.ker = 2)
    (H2bar : Subgroup (alternatingGroup (Fin n)))
    (eH2 : H2bar ≃* alternatingGroup (Fin s))
    (hroot : ∀ u : H2bar,
      (eH2 u).1.support.card = 4 → u.1.1.support.card = 4) :
    Subgroup.center K ≤
      (_root_.commutator (H2bar.comap f.toMonoidHom)).map
        (H2bar.comap f.toMonoidHom).subtype := by
  let E := H2bar.comap f.toMonoidHom
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  obtain ⟨hEqs, _hEcard, _⟩ :=
    (proposition_5_2_6_d_3 n hn s (by omega) f hker H2bar eH2 hroot).2 hs
  have hEperfect : _root_.commutator E = ⊤ :=
    (isQuasisimple_def E).mp hEqs |>.1
  have hkerCenter : f.toMonoidHom.ker = Subgroup.center K :=
    f.ker_eq_center_of_isSimple
  have hcenterKleE : Subgroup.center K ≤ E := by
    intro z hz
    change f.toMonoidHom z ∈ H2bar
    have hzker : z ∈ f.toMonoidHom.ker := by
      rw [hkerCenter]
      exact hz
    rw [MonoidHom.mem_ker] at hzker
    rw [hzker]
    exact H2bar.one_mem
  intro z hz
  have hzE : z ∈ E := hcenterKleE hz
  let zE : E := ⟨z, hzE⟩
  change E.subtype zE ∈ (_root_.commutator E).map E.subtype
  apply Subgroup.mem_map_of_mem E.subtype
  rw [hEperfect]
  exact Subgroup.mem_top zE

end GLS3.Chapter5
/- END Theory.CenterCoreLeDerivedAlternatingPreimage -/

/- BEGIN Theory.FixedSubgroupMulEquivTransport -/
namespace GLS3.Chapter5

set_option maxHeartbeats 800000

/-- A group equivalence intertwining two automorphisms identifies their fixed
subgroups as groups. -/
public noncomputable def fixedSubgroupMulEquivOfCompat
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (alpha : MulAut G) (beta : MulAut H)
    (hcompat : ∀ g : G, e (alpha g) = beta (e g)) :
    automorphismFixedSubgroup alpha ≃*
      automorphismFixedSubgroup beta := by
  let F : Subgroup G := automorphismFixedSubgroup alpha
  let F' : Subgroup H := automorphismFixedSubgroup beta
  have hmap : F.map e.toMonoidHom = F' := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      change beta (e g) = e g
      change alpha g = g at hg
      rw [← hcompat g, hg]
    · intro hy
      obtain ⟨g, rfl⟩ := e.surjective y
      change beta (e g) = e g at hy
      refine ⟨g, ?_, rfl⟩
      change alpha g = g
      apply e.injective
      rw [hcompat g, hy]
  exact (e.subgroupMap F).trans (MulEquiv.subgroupCongr hmap)

end GLS3.Chapter5

namespace GLS3.Chapter5

public theorem fixedSubgroupMulEquivOfCompat_apply
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (alpha : MulAut G) (beta : MulAut H)
    (hcompat : ∀ g : G, e (alpha g) = beta (e g))
    (g : automorphismFixedSubgroup alpha) :
    (fixedSubgroupMulEquivOfCompat e alpha beta hcompat g : H) = e g := by
  rfl

end GLS3.Chapter5
/- END Theory.FixedSubgroupMulEquivTransport -/

/- BEGIN Theory.PrimeCentralizerExtensionNormalizer -/
namespace GLS3.Chapter5

/-- The order-two extension element in the alternating prime centralizer
normalizes both product factors. The small case is trivial; in the large case
this follows because each factor has index two after adjoining the element. -/
public theorem primeCentralizer_zpowers_le_normalizer_factors
    {G : Type*} [Group G]
    (r s : Nat) (A B : Subgroup G) (t : G)
    (hrpos : 0 < r)
    (hsmall : (s ≤ 1 ∨ r = 1) → t = 1)
    (hlarge : (2 ≤ s ∧ 2 ≤ r) →
      (A.subgroupOf (A ⊔ Subgroup.zpowers t)).index = 2 ∧
      (B.subgroupOf (B ⊔ Subgroup.zpowers t)).index = 2) :
    Subgroup.zpowers t ≤ Subgroup.normalizer A ∧
      Subgroup.zpowers t ≤ Subgroup.normalizer B := by
  by_cases hs : s ≤ 1
  · have ht : t = 1 := hsmall (Or.inl hs)
    subst t
    simp
  have hs2 : 2 ≤ s := by omega
  by_cases hr : r = 1
  · have ht : t = 1 := hsmall (Or.inr hr)
    subst t
    simp
  have hr2 : 2 ≤ r := by omega
  obtain ⟨hAindex, hBindex⟩ := hlarge ⟨hs2, hr2⟩
  have hAnormal : (A.subgroupOf (A ⊔ Subgroup.zpowers t)).Normal :=
    Subgroup.normal_of_index_eq_two hAindex
  have hBnormal : (B.subgroupOf (B ⊔ Subgroup.zpowers t)).Normal :=
    Subgroup.normal_of_index_eq_two hBindex
  constructor
  · exact (le_sup_right : Subgroup.zpowers t ≤ A ⊔ Subgroup.zpowers t) |>.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hAnormal)
  · exact (le_sup_right : Subgroup.zpowers t ≤ B ⊔ Subgroup.zpowers t) |>.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hBnormal)

end GLS3.Chapter5
/- END Theory.PrimeCentralizerExtensionNormalizer -/

/- BEGIN Theory.A6StandardNineLiftsNotCommute -/
noncomputable section

namespace GLS3.Chapter5

/-- Lifts of the displayed basis of the standard `E₉` cannot commute in a
triple cover of `A₆`. -/
public theorem a6StandardNine_lifts_not_commute
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 6)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (u v : K)
    (hu : f u = SchurPresentation.Theorem523BaseNine.a6X)
    (hv : f v = SchurPresentation.Theorem523BaseNine.a6Y) :
    ¬ Commute u v := by
  intro huv
  apply a6StandardNine_preimage_noncommutative f hker
  rw [isMulCommutative_iff]
  intro a b
  let af : SchurPresentation.Theorem523BaseNine.a6StandardNine :=
    ⟨f a.1, a.2⟩
  let bf : SchurPresentation.Theorem523BaseNine.a6StandardNine :=
    ⟨f b.1, b.2⟩
  obtain ⟨i, j, haCoords⟩ := a6StandardNine_exists_zpow_coordinates af
  obtain ⟨k, l, hbCoords⟩ := a6StandardNine_exists_zpow_coordinates bf
  let ua : K := u ^ i * v ^ j
  let ub : K := u ^ k * v ^ l
  let za : K := a.1 * ua⁻¹
  let zb : K := b.1 * ub⁻¹
  have hua : f ua = f a.1 := by
    change f (u ^ i * v ^ j) = f a.1
    rw [map_mul, map_zpow, map_zpow, hu, hv]
    exact haCoords.symm
  have hub : f ub = f b.1 := by
    change f (u ^ k * v ^ l) = f b.1
    rw [map_mul, map_zpow, map_zpow, hu, hv]
    exact hbCoords.symm
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (a.1 * ua⁻¹) = 1
    rw [map_mul, map_inv, hua]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (b.1 * ub⁻¹) = 1
    rw [map_mul, map_inv, hub]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have ha : a.1 = za * ua := by
    dsimp [za]
    group
  have hb : b.1 = zb * ub := by
    dsimp [zb]
    group
  have huaua : Commute (u ^ i) (u ^ k) :=
    (Commute.refl u).zpow_zpow i k
  have huavb : Commute (u ^ i) (v ^ l) := huv.zpow_zpow i l
  have hvaua : Commute (v ^ j) (u ^ k) := huv.symm.zpow_zpow j k
  have hvavb : Commute (v ^ j) (v ^ l) :=
    (Commute.refl v).zpow_zpow j l
  have huaub : Commute ua ub := by
    dsimp [ua, ub]
    exact (huaua.mul_right huavb).mul_left (hvaua.mul_right hvavb)
  have hzaAll (g : K) : Commute za g :=
    (Subgroup.mem_center_iff.mp hzaCenter g).symm
  have hzbAll (g : K) : Commute zb g :=
    (Subgroup.mem_center_iff.mp hzbCenter g).symm
  apply Subtype.ext
  change a.1 * b.1 = b.1 * a.1
  rw [ha, hb]
  exact ((hzaAll zb).mul_right (hzaAll ub)).mul_left
    ((hzbAll ua).symm.mul_right huaub)

end GLS3.Chapter5
/- END Theory.A6StandardNineLiftsNotCommute -/

/- BEGIN Theory.A7StandardNineLiftsNotCommute -/
noncomputable section

namespace GLS3.Chapter5

/-- Lifts of the displayed basis of the standard `E₉` cannot commute in a
triple cover of `A₇`. -/
public theorem a7StandardNine_lifts_not_commute
    {K : Type} [Group K] [Finite K] [IsQuasisimple K]
    (f : Covering K (alternatingGroup (Fin 7)))
    (hker : Nat.card f.toMonoidHom.ker = 3)
    (u v : K)
    (hu : f u = SchurPresentation.Theorem523BaseNine.a7X)
    (hv : f v = SchurPresentation.Theorem523BaseNine.a7Y) :
    ¬ Commute u v := by
  intro huv
  apply a7StandardNine_preimage_noncommutative f hker
  rw [isMulCommutative_iff]
  intro a b
  let af : SchurPresentation.Theorem523BaseNine.a7StandardNine :=
    ⟨f a.1, a.2⟩
  let bf : SchurPresentation.Theorem523BaseNine.a7StandardNine :=
    ⟨f b.1, b.2⟩
  obtain ⟨i, j, haCoords⟩ := a7StandardNine_exists_zpow_coordinates af
  obtain ⟨k, l, hbCoords⟩ := a7StandardNine_exists_zpow_coordinates bf
  let ua : K := u ^ i * v ^ j
  let ub : K := u ^ k * v ^ l
  let za : K := a.1 * ua⁻¹
  let zb : K := b.1 * ub⁻¹
  have hua : f ua = f a.1 := by
    change f (u ^ i * v ^ j) = f a.1
    rw [map_mul, map_zpow, map_zpow, hu, hv]
    exact haCoords.symm
  have hub : f ub = f b.1 := by
    change f (u ^ k * v ^ l) = f b.1
    rw [map_mul, map_zpow, map_zpow, hu, hv]
    exact hbCoords.symm
  have hzaKer : za ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (a.1 * ua⁻¹) = 1
    rw [map_mul, map_inv, hua]
    group
  have hzbKer : zb ∈ f.toMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change f (b.1 * ub⁻¹) = 1
    rw [map_mul, map_inv, hub]
    group
  have hzaCenter : za ∈ Subgroup.center K := f.ker_le_center hzaKer
  have hzbCenter : zb ∈ Subgroup.center K := f.ker_le_center hzbKer
  have ha : a.1 = za * ua := by
    dsimp [za]
    group
  have hb : b.1 = zb * ub := by
    dsimp [zb]
    group
  have huaua : Commute (u ^ i) (u ^ k) :=
    (Commute.refl u).zpow_zpow i k
  have huavb : Commute (u ^ i) (v ^ l) := huv.zpow_zpow i l
  have hvaua : Commute (v ^ j) (u ^ k) := huv.symm.zpow_zpow j k
  have hvavb : Commute (v ^ j) (v ^ l) :=
    (Commute.refl v).zpow_zpow j l
  have huaub : Commute ua ub := by
    dsimp [ua, ub]
    exact (huaua.mul_right huavb).mul_left (hvaua.mul_right hvavb)
  have hzaAll (g : K) : Commute za g :=
    (Subgroup.mem_center_iff.mp hzaCenter g).symm
  have hzbAll (g : K) : Commute zb g :=
    (Subgroup.mem_center_iff.mp hzbCenter g).symm
  apply Subtype.ext
  change a.1 * b.1 = b.1 * a.1
  rw [ha, hb]
  exact ((hzaAll zb).mul_right (hzaAll ub)).mul_left
    ((hzbAll ua).symm.mul_right huaub)

end GLS3.Chapter5
/- END Theory.A7StandardNineLiftsNotCommute -/

/- BEGIN Theory.A6DoubleCoverPermutationModel -/
namespace GLS3.Chapter5

public abbrev Perm144 := Equiv.Perm (Fin 144)

@[reducible, expose] public def a6DoubleCoverGen1 : Perm144 where
  toFun := fun i => Vector.get #v[0, 2, 4, 6, 7, 9, 11, 13, 14, 16, 18, 19, 21, 1, 24, 26, 27, 29, 31,  33, 35, 36, 38, 28, 40, 23, 34, 44, 46, 48, 12, 37, 51, 3, 54, 45, 57, 59,  61, 63, 64, 17, 58, 67, 5, 70, 72, 74, 75, 49, 78, 79, 81, 76, 83, 52, 69,  30, 86, 10, 56, 80, 55, 65, 8, 92, 94, 95, 96, 47, 98, 100, 25, 91, 60, 41,  103, 90, 85, 106, 108, 110, 111, 15, 113, 107, 97, 77, 117, 116, 119, 112,  122, 124, 84, 109, 101, 104, 20, 128, 102, 125, 126, 118, 42, 66, 114, 133,  22, 130, 62, 99, 93, 105, 32, 127, 135, 115, 121, 131, 82, 53, 39, 68, 73,  123, 129, 132, 120, 71, 43, 87, 88, 50, 137, 134, 139, 89, 138, 141, 136,  143, 142, 140] i
  invFun := fun i => Vector.get #v[0, 13, 1, 33, 2, 44, 3, 4, 64, 5, 59, 6, 30, 7, 8, 83, 9, 41, 10,  11, 98, 12, 108, 25, 14, 72, 15, 16, 23, 17, 57, 18, 114, 19, 26, 20, 21, 31,  22, 122, 24, 75, 104, 130, 27, 35, 28, 69, 29, 49, 133, 32, 55, 121, 34, 62,  60, 36, 42, 37, 74, 38, 110, 39, 40, 63, 105, 43, 123, 56, 45, 129, 46, 124,  47, 48, 53, 87, 50, 51, 61, 52, 120, 54, 94, 78, 58, 131, 132, 137, 77, 73,  65, 112, 66, 67, 68, 86, 70, 111, 71, 96, 100, 76, 97, 113, 79, 85, 80, 95,  81, 82, 91, 84, 106, 117, 89, 88, 103, 90, 128, 118, 92, 125, 93, 101, 102,  115, 99, 126, 109, 119, 127, 107, 135, 116, 140, 134, 138, 136, 143, 139,  142, 141] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[reducible, expose] public def a6DoubleCoverGen2 : Perm144 where
  toFun := fun i => Vector.get #v[1, 3, 5, 0, 8, 10, 12, 11, 15, 17, 2, 20, 22, 23, 25, 4, 28, 30, 32,  34, 7, 37, 6, 39, 41, 42, 43, 45, 47, 49, 9, 50, 52, 53, 55, 56, 58, 60, 62,  13, 65, 66, 14, 68, 69, 71, 73, 16, 76, 77, 72, 80, 18, 82, 84, 19, 85, 81,  67, 87, 21, 88, 89, 90, 91, 93, 24, 36, 26, 97, 99, 27, 31, 101, 100, 102,  104, 29, 105, 107, 109, 106, 33, 112, 114, 35, 115, 116, 118, 38, 120, 121,  123, 40, 83, 125, 126, 44, 127, 129, 130, 46, 131, 122, 48, 132, 57, 134,  128, 51, 113, 135, 94, 119, 54, 124, 59, 133, 61, 110, 63, 64, 136, 137, 86,  138, 139, 140, 141, 70, 74, 75, 78, 142, 79, 143, 103, 92, 95, 96, 98, 108,  117, 111] i
  invFun := fun i => Vector.get #v[3, 0, 10, 1, 15, 2, 22, 20, 4, 30, 5, 7, 6, 39, 42, 8, 47, 9, 52,  55, 11, 60, 12, 13, 66, 14, 68, 71, 16, 77, 17, 72, 18, 82, 19, 85, 67, 21,  89, 23, 93, 24, 25, 26, 97, 27, 101, 28, 104, 29, 31, 109, 32, 33, 114, 34,  35, 106, 36, 116, 37, 118, 38, 120, 121, 40, 41, 58, 43, 44, 129, 45, 50, 46,  130, 131, 48, 49, 132, 134, 51, 57, 53, 94, 54, 56, 124, 59, 61, 62, 63, 64,  137, 65, 112, 138, 139, 69, 140, 70, 74, 73, 75, 136, 76, 78, 81, 79, 141,  80, 119, 143, 83, 110, 84, 86, 87, 142, 88, 113, 90, 91, 103, 92, 115, 95,  96, 98, 108, 99, 100, 102, 105, 117, 107, 111, 122, 123, 125, 126, 127, 128,  133, 135] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[reducible, expose] public def a6ExceptionalConjugator : Perm144 where
  toFun := fun i => Vector.get #v[17, 14, 5, 39, 87, 2, 84, 97, 86, 104, 140, 100, 76, 119, 1, 68, 105,  0, 132, 37, 91, 25, 82, 93, 57, 21, 111, 112, 56, 59, 134, 73, 116, 49, 35,  34, 128, 19, 85, 3, 69, 122, 96, 65, 118, 81, 53, 54, 83, 33, 70, 115, 141,  46, 47, 121, 28, 24, 133, 29, 117, 125, 77, 74, 129, 43, 126, 130, 15, 40,  50, 123, 72, 31, 63, 98, 12, 62, 113, 92, 110, 45, 22, 48, 6, 38, 8, 4, 127,  103, 120, 20, 79, 23, 143, 136, 42, 7, 75, 114, 11, 138, 106, 89, 9, 16, 102,  142, 131, 124, 80, 26, 27, 78, 99, 51, 32, 60, 44, 13, 90, 55, 41, 71, 109,  61, 66, 88, 36, 64, 67, 108, 18, 58, 30, 139, 95, 137, 101, 135, 10, 52, 107,  94] i
  invFun := fun i => Vector.get #v[17, 14, 5, 39, 87, 2, 84, 97, 86, 104, 140, 100, 76, 119, 1, 68, 105,  0, 132, 37, 91, 25, 82, 93, 57, 21, 111, 112, 56, 59, 134, 73, 116, 49, 35,  34, 128, 19, 85, 3, 69, 122, 96, 65, 118, 81, 53, 54, 83, 33, 70, 115, 141,  46, 47, 121, 28, 24, 133, 29, 117, 125, 77, 74, 129, 43, 126, 130, 15, 40,  50, 123, 72, 31, 63, 98, 12, 62, 113, 92, 110, 45, 22, 48, 6, 38, 8, 4, 127,  103, 120, 20, 79, 23, 143, 136, 42, 7, 75, 114, 11, 138, 106, 89, 9, 16, 102,  142, 131, 124, 80, 26, 27, 78, 99, 51, 32, 60, 44, 13, 90, 55, 41, 71, 109,  61, 66, 88, 36, 64, 67, 108, 18, 58, 30, 139, 95, 137, 101, 135, 10, 52, 107,  94] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[reducible, expose] public def a6DoubleCoverCentral : Perm144 :=
  (a6DoubleCoverGen1 * a6DoubleCoverGen2) ^ 4

@[reducible, expose] public def a6TwistedReflectionLift : Perm144 :=
  a6DoubleCoverGen1 * (a6DoubleCoverGen1 * a6DoubleCoverGen2) ^ 2 *
    a6DoubleCoverGen1⁻¹

public theorem a6DoubleCoverCentral_sq : a6DoubleCoverCentral ^ 2 = 1 := by
  ext i
  fin_cases i <;> decide +revert +kernel

public theorem a6DoubleCoverCentral_ne_one : a6DoubleCoverCentral ≠ 1 := by
  intro h
  have hne : a6DoubleCoverCentral (0 : Fin 144) ≠ (1 : Perm144) 0 := by
    decide +kernel
  exact hne (Equiv.congr_fun h 0)

public theorem a6ExceptionalConjugator_sq : a6ExceptionalConjugator ^ 2 = 1 := by
  ext i
  fin_cases i <;> decide +revert +kernel

public theorem a6TwistedReflectionLift_sq :
    a6TwistedReflectionLift ^ 2 = a6DoubleCoverCentral := by
  ext i
  fin_cases i <;> decide +revert +kernel

set_option maxRecDepth 10000 in
public theorem a6TwistedReflectionLift_conj :
    a6ExceptionalConjugator⁻¹ * a6TwistedReflectionLift *
        a6ExceptionalConjugator =
      a6DoubleCoverCentral * a6TwistedReflectionLift := by
  ext i
  fin_cases i <;> decide +revert +kernel

end GLS3.Chapter5
/- END Theory.A6DoubleCoverPermutationModel -/
