module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.AlternatingBinary.Basic
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple

/-!
# The A₆ Sylow-pair exclusion, including central covers

An order-nine subgroup permuting with a Sylow two-subgroup of A₆ would
generate a subgroup of order 72 and index five. The coset action of the simple
group A₆ would embed its 360 elements in S₅, which is impossible. Thus every
three-subgroup permuting with that Sylow subgroup is cyclic.

For a central cover, either the intersection of R with the center is visible
in R/Φ(R), giving an invariant proper subgroup, or that intersection lies in
Φ(R). In the latter case the cyclic quotient image forces R itself to be
cyclic, contrary to the odd-complement hypothesis. This handles all central
covers without assuming a multiplier order or replacing the Sylow condition.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary

private abbrev A6 := alternatingGroup (Fin 6)

private theorem card_six : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem sylow_two_card_six (P : Sylow 2 A6) : Nat.card P = 8 := by
  rw [P.card_eq_multiplicity, card_six]
  rw [show 360 = 2 ^ 3 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rfl

private theorem sylow_three_card_six (P : Sylow 3 A6) : Nat.card P = 9 := by
  rw [P.card_eq_multiplicity, card_six]
  rw [show 360 = 3 ^ 2 * 40 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    (by decide : Nat.Prime 3).factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 40)]
  rfl

private theorem no_permuting_nine_six (P : Sylow 2 A6) (D : Subgroup A6)
    (hc : Nat.card D = 9)
    (hp : (D : Set A6) * (P : Set A6) = (P : Set A6) * (D : Set A6)) : False := by
  let H : Subgroup A6 := D ⊔ (P : Subgroup A6)
  have hd : Disjoint D (P : Subgroup A6) := disjoint_of_coprime_natCard
    (by rw [hc, sylow_two_card_six]; decide)
  let m : D × P → H := fun p =>
    ⟨(p.1 : A6) * (p.2 : A6), mul_mem_sup p.1.property p.2.property⟩
  have hi : Function.Injective m := fun _ _ h =>
    mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective m := by
    intro x
    have hx : (x : A6) ∈ (D : Set A6) * (P : Set A6) := by
      change (x : A6) ∈ (D : Set A6) * ((P : Subgroup A6) : Set A6)
      rw [← coe_sup_of_set_mul_comm D (P : Subgroup A6) hp]
      exact x.property
    obtain ⟨d, hd, p, hp, he⟩ := hx
    exact ⟨(⟨d, hd⟩, ⟨p, hp⟩), Subtype.ext he⟩
  have hH : Nat.card H = 72 := by
    rw [← Nat.card_congr (Equiv.ofBijective m ⟨hi, hs⟩), Nat.card_prod,
      hc, sylow_two_card_six]
  have hidx : H.index = 5 := by
    have hh := H.card_mul_index
    rw [hH, card_six] at hh
    omega
  let _ : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  have ht : H = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt H (by
    rw [hidx, card_six]
    decide)
  rw [ht, card_top, card_six] at hH
  omega

/-- Every three-subgroup of A₆ permuting with a Sylow two-subgroup is cyclic. -/
theorem cyclic_of_permuting_six (P : Sylow 2 (alternatingGroup (Fin 6)))
    (D : Subgroup (alternatingGroup (Fin 6))) (hD : IsPGroup 3 D)
    (hp : (D : Set (alternatingGroup (Fin 6))) * (P : Set (alternatingGroup (Fin 6))) =
      (P : Set (alternatingGroup (Fin 6))) * (D : Set (alternatingGroup (Fin 6)))) :
    IsCyclic D := by
  obtain ⟨U, hDU⟩ := hD.exists_le_sylow
  have hd := Subgroup.card_dvd_of_le hDU
  rw [sylow_three_card_six U] at hd
  obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp
    (show Nat.card D ∣ 3 ^ 2 from hd)
  interval_cases n
  · exact isCyclic_of_card_dvd_prime (p := 3) (by rw [hc]; decide)
  · exact isCyclic_of_prime_card (p := 3) (by simpa using hc)
  · exact (no_permuting_nine_six P D (by simpa using hc) hp).elim

universe u
variable {Q : Type u} [Group Q] [Finite Q]

/-- The A₆ exclusion in the central quotient, with the actual action on R/Φ(R). -/
theorem alternating_six {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 6)) : PairReducible (S : Subgroup Q) R := by
  by_contra hn
  have hK : (center Q).subgroupOf R ≤ frattini R := by
    by_contra hv
    exact hn (pairReducible_of_centralIntersection (not_le_center h) hv)
  let f : Q →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := S.mapSurjective hf
  have hp : (R.map f : Set (alternatingGroup (Fin 6))) * (P : Set (alternatingGroup (Fin 6))) =
      (P : Set (alternatingGroup (Fin 6))) * (R.map f : Set (alternatingGroup (Fin 6))) := by
    have hh := congrArg (fun A : Set Q => f '' A) h.permutes
    simpa only [P, ← Sylow.coe_coe, Sylow.coe_mapSurjective, coe_map, Set.image_mul] using hh
  let _ := cyclic_of_permuting_six P (R.map f) (h.oddComplement.isPGroup.map f) hp
  apply h.oddComplement.not_isCyclic
  apply isCyclic_of_frattini_kernel (f.subgroupMap R) (f.subgroupMap_surjective R)
  intro x hx
  apply hK
  change (x : Q) ∈ center Q
  apply (QuotientGroup.eq_one_iff (x : Q)).mp
  apply e.injective
  have hx' : f x = 1 := congrArg Subtype.val hx
  simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply, map_one] using hx'

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
