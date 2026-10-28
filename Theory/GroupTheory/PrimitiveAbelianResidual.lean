module
public import Theory.GroupTheory.PResidual.CoreCentralizer
public import Theory.GroupTheory.PCoreImage

/-!
# Local two-cores with a primitive abelian odd residual

Suppose the two-core is trivial, the two-residual is abelian and minimal
normal, and every Sylow two-subgroup is abelian. The residual centralizer of
an involution is normalized by both the residual and a Sylow containing the
involution. Minimal normality therefore makes it trivial: the alternative
would put the involution in the two-core.

Consequently every subgroup with nontrivial two-core is a two-group, provided
the residual has odd order. Its intersection with the residual centralizes
the local two-core by coprimeness, and the first result kills that intersection.
The subgroup then embeds in the two-group quotient by the residual.

Application: the elementary-nine alternative in Aschbacher--Smith 14.6.12,
printed p.1031, with the actual opposite-point centralizers.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {X : Type*} [Group X] [Finite X]

/-- Every involution acts without nonidentity fixed points on the residual. -/
theorem primitive_residual_involution_fixedFree
    [IsMulCommutative (pResidual 2 X)]
    (hcore : pCore 2 X = ⊥)
    (hmin : ∀ B : Subgroup X, B.Normal → B ≤ pResidual 2 X →
      B = ⊥ ∨ B = pResidual 2 X)
    (hSyl : ∀ S : Sylow 2 X, IsMulCommutative S)
    (t : X) (ht : orderOf t = 2) :
    pResidual 2 X ⊓ centralizer ({t} : Set X) = ⊥ := by
  let P := pResidual 2 X
  let A := zpowers t
  have hpA : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ht]; rfl)
  obtain ⟨S,hAS⟩ := hpA.exists_le_sylow
  let := hSyl S
  have htS : t ∈ (S : Subgroup X) := hAS (mem_zpowers _)
  have hSC : (S : Subgroup X) ≤ centralizer ({t} : Set X) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨s,hs⟩ : S) ⟨t,htS⟩)
  let C := P ⊓ centralizer ({t} : Set X)
  have hPN : P ≤ normalizer (C : Set X) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show C ≤ P from inf_le_left))).trans (centralizer_le_normalizer _)
  have hSN : (S : Subgroup X) ≤ normalizer (C : Set X) :=
    (le_inf le_normalizer_of_normal
      (hSC.trans (centralizer ({t} : Set X)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hn : C.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←pResidual_sup_sylow_eq_top S]
    exact sup_le hPN hSN))
  rcases hmin C hn inf_le_left with h | h
  · exact h
  have hAC : A ≤ centralizer (P : Set X) := by
    apply zpowers_le.mpr
    intro p hp
    exact (mem_centralizer_singleton_iff.mp ((h.ge hp).2))
  have hh := pSubgroup_le_pCore_of_centralizes_pResidual A hpA hAC
  rw [hcore] at hh
  have ht1 : t = 1 := hh (mem_zpowers _)
  rw [ht1,orderOf_one] at ht
  omega

/-- A nontrivial local two-core forces the whole local subgroup to be a two-group. -/
theorem isPGroup_of_nontrivial_core_of_primitive_odd_residual
    [IsMulCommutative (pResidual 2 X)]
    (hcore : pCore 2 X = ⊥)
    (hodd : Odd (Nat.card (pResidual 2 X)))
    (hmin : ∀ B : Subgroup X, B.Normal → B ≤ pResidual 2 X →
      B = ⊥ ∨ B = pResidual 2 X)
    (hSyl : ∀ S : Sylow 2 X, IsMulCommutative S)
    (C : Subgroup X) (hne : pCore 2 C ≠ ⊥) : IsPGroup 2 C := by
  let P := pResidual 2 X
  let R := P.subgroupOf C
  let j : R →* P := (C.subtype.comp R.subtype).codRestrict P (fun x => x.property)
  have hoR : Odd (Nat.card R) := hodd.of_dvd_nat
    (card_dvd_of_injective j (by intro x y h; exact Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : X)) h))))
  have hcop : Nat.Coprime (Nat.card (pCore 2 C)) (Nat.card R) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hoR).pow_left n
  have hdis : Disjoint (pCore 2 C) R := disjoint_of_coprime_natCard hcop
  have hc : pCore 2 C ≤ centralizer (R : Set C) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
  have heven : 2 ∣ Nat.card (pCore 2 C) := by
    rcases (pCore_isPGroup (p := 2) (G := C)).card_eq_or_dvd with hh | hh
    · exact (hne (card_eq_one.mp hh)).elim
    · exact hh
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := pCore 2 C) 2 heven
  have htX : orderOf ((t : C) : X) = 2 :=
    (Subgroup.orderOf_coe (t : C)).trans ((Subgroup.orderOf_coe t).trans ht)
  have hfixed := primitive_residual_involution_fixedFree hcore hmin hSyl (t : C) htX
  have hRP : P.subgroupOf C = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hfixed.le
    refine ⟨hx,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (congrArg Subtype.val (hc t.property x hx))
  let q := (QuotientGroup.mk' P).comp C.subtype
  apply (isPGroup_quotient_pResidual (G := X) 2).of_injective q
  apply (MonoidHom.ker_eq_bot_iff q).mp
  calc
    q.ker = P.subgroupOf C := by
      ext x
      exact QuotientGroup.eq_one_iff (x : X)
    _ = ⊥ := hRP
end Subgroup
