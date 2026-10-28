module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Basic
public import Theory.Mathieu.M22.Basic
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M22.Properties.NoOrder1152
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SubgroupProductCard

/-!
# The M₂₂ exclusion for central covers

An order-nine subgroup permuting with a Sylow two-subgroup of M₂₂ would
give a subgroup of order 1152. Excluding that order makes every permutable
three-subgroup cyclic. The same exclusion then handles arbitrary central
covers: the intersection of the complement with the center either gives
a proper invariant subgroup of its Frattini quotient, or lies in its
Frattini subgroup, in which case cyclicity of the image lifts upstairs.
Both allowed complements, elementary of order nine and extraspecial of
order 27, are noncyclic, so the latter case is impossible.

The checked order-1152 exclusion for the actual Steiner-design group
discharges the model premise in the final assembly. The argument needs no
bound on the center. The source interface also accepts the center-order
bound three, retaining the nontrivial three-cover allowed by the multiplier
bound twelve.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing Aschbacher, *Overgroups of Sylow subgroups in sporadic
groups*, Memoirs AMS 60, no.343 (1986); GLS3, Table 5.3c.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

private theorem m22_sylow_two_card (P : Sylow 2 Sporadic.Mathieu.M22) :
    Nat.card P = 128 := by
  rw [P.card_eq_multiplicity, Sporadic.Mathieu.m22_order]
  rw [show 443520 = 2 ^ 7 * 3465 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3465)]
  rfl

private theorem m22_sylow_three_card (P : Sylow 3 Sporadic.Mathieu.M22) :
    Nat.card P = 9 := by
  rw [P.card_eq_multiplicity, Sporadic.Mathieu.m22_order]
  rw [show 443520 = 3 ^ 2 * 49280 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_three.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 49280)]
  rfl

/-- The subgroup-order obstruction implies cyclicity of every permutable
three-subgroup in the actual Steiner-design M₂₂. -/
theorem m22_cyclic_of_permuting_of_no_subgroup_order1152
    (horder : ∀ H : Subgroup Sporadic.Mathieu.M22, Nat.card H ≠ 1152)
    (P : Sylow 2 Sporadic.Mathieu.M22) (D : Subgroup Sporadic.Mathieu.M22)
    (hD : IsPGroup 3 D)
    (hp : (D : Set Sporadic.Mathieu.M22) * (P : Set Sporadic.Mathieu.M22) =
      (P : Set Sporadic.Mathieu.M22) * (D : Set Sporadic.Mathieu.M22)) :
    IsCyclic D := by
  obtain ⟨U, hDU⟩ := hD.exists_le_sylow
  have hd := Subgroup.card_dvd_of_le hDU
  rw [m22_sylow_three_card U] at hd
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (show Nat.card D ∣ 3 ^ 2 from hd)
  interval_cases n
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hc]; decide)
  · exact isCyclic_of_prime_card (p := 3) (by simpa using hc)
  · have hdis : Disjoint D (P : Subgroup Sporadic.Mathieu.M22) :=
      disjoint_of_coprime_natCard (by rw [hc, m22_sylow_two_card]; decide)
    have hprod := card_set_mul_mul_card_inf D (P : Subgroup Sporadic.Mathieu.M22)
    rw [← coe_sup_of_set_mul_comm D (P : Subgroup Sporadic.Mathieu.M22) hp,
      hdis.eq_bot, card_bot, mul_one, hc, m22_sylow_two_card] at hprod
    exact (horder _ hprod).elim

/-- Conditional assembly through the actual quotient map, with no injectivity
assumption on the complement and no restriction on the central kernel. -/
theorem mathieu_twentyTwo_of_no_subgroup_order1152
    (horder : ∀ H : Subgroup Sporadic.Mathieu.M22, Nat.card H ≠ 1152)
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M22) :
    PairReducible (S : Subgroup Q) R := by
  by_contra hn
  have hK : (center Q).subgroupOf R ≤ frattini R := by
    by_contra hv
    exact hn (AlternatingBinary.pairReducible_of_centralIntersection
      (AlternatingBinary.not_le_center h) hv)
  let f : Q →* Sporadic.Mathieu.M22 :=
    e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hf
  have hp : (R.map f : Set Sporadic.Mathieu.M22) * (P : Set Sporadic.Mathieu.M22) =
      (P : Set Sporadic.Mathieu.M22) * (R.map f : Set Sporadic.Mathieu.M22) := by
    have hh := congrArg (fun A : Set Q => f '' A) h.permutes
    simpa only [P, ← Sylow.coe_coe, Sylow.coe_mapSurjective, coe_map, Set.image_mul] using hh
  let _ := m22_cyclic_of_permuting_of_no_subgroup_order1152 horder P (R.map f)
    (h.oddComplement.isPGroup.map f) hp
  apply h.oddComplement.not_isCyclic
  apply AlternatingBinary.isCyclic_of_frattini_kernel
    (f.subgroupMap R) (f.subgroupMap_surjective R)
  intro x hx
  apply hK
  change (x : Q) ∈ center Q
  apply (QuotientGroup.eq_one_iff (x : Q)).mp
  apply e.injective
  have hx' : f x = 1 := congrArg Subtype.val hx
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply, map_one] using hx'

/-- The M₂₂ pair exclusion for every finite central cover, using the proved
subgroup-order obstruction for the concrete quotient model. -/
theorem mathieu_twentyTwo_cover
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M22) :
    PairReducible (S : Subgroup Q) R :=
  mathieu_twentyTwo_of_no_subgroup_order1152 Sporadic.Mathieu.m22_subgroup_card_ne_1152 h e

/-- The source M₂₂ branch, including its possible nontrivial three-cover.
The center-order bound is supplied by the parent's universal multiplier
bound, although the stronger cover argument does not require it. -/
theorem mathieu_twentyTwo
    {Q : Type*} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (_hc : Nat.card (center Q) ∣ 3)
    (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M22) :
    PairReducible (S : Subgroup Q) R :=
  mathieu_twentyTwo_cover h e

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
