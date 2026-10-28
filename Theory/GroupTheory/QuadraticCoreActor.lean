module
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# Quadratic actors on a self-centralizing p-group

A finite subgroup acting quadratically on a self-centralizing p-subgroup
is a p-group: each prime-order element of order prime to p acts trivially
by coprime commutator idempotence, and then self-centralization excludes it.

If two actors centralize the displacement of the first, its relative normal
closure is quadratic. This closure and the second p-group actor generate
a p-group. This proves the algebraic contradiction used in DGS (11.2)(c),
*Groups and Graphs* (1985), printed p.168. Only relative normalizers and the
centralizer inside the specified actor join are used.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A quadratic actor of a self-centralizing finite p-group is a p-group. -/
theorem isPGroup_of_quadratic_core_action
    (Q A : Subgroup G) [Finite Q] [Finite A] (hQ : IsPGroup p Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hcentral : A ⊓ centralizer (Q : Set G) ≤ Q)
    (hquad : ⁅⁅Q,A⁆,A⁆ = ⊥) : IsPGroup p A := by
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
  intro r hr
  obtain ⟨hrprime, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
  by_cases he : r = p
  · subst r
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) r (hp := ⟨hrprime⟩) hrdvd
    let R := zpowers (x : G)
    have hRA : R ≤ A := zpowers_le.mpr x.property
    have hRquad : ⁅⁅Q,R⁆,R⁆ = ⊥ :=
      bot_unique ((commutator_mono (commutator_mono le_rfl hRA) hRA).trans hquad.le)
    have hRcard : Nat.card R = r := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
      obtain ⟨n, hn⟩ := hQ.exists_card_eq
      rw [hRcard, hn]
      exact ((hrprime.coprime_iff_not_dvd).mpr
        (fun hd => he ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left hrprime.ne_one))).pow_right n
    let : Group.IsNilpotent Q := hQ.isNilpotent
    have hbot := commutator_eq_bot_of_coprime_quadratic Q R (hRA.trans hAQ)
      (inferInstance : Group.IsSolvable Q) hcop hRquad
    have hxQ : (x : G) ∈ Q := hcentral ⟨x.property,
      (commutator_eq_bot_iff_le_centralizer.mp
        (by rwa [commutator_comm] : ⁅R,Q⁆ = ⊥)) (mem_zpowers _)⟩
    obtain ⟨n, hn⟩ := hQ.exists_orderOf_dvd_pow ⟨x,hxQ⟩
    have hd : r ∣ p ^ n := by
      simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe x, hx] using hn
    exact (he ((Nat.dvd_prime Fact.out).mp
      (hrprime.dvd_of_dvd_pow hd) |>.resolve_left hrprime.ne_one)).elim
/-- Centralizing the displacement of one p-subgroup forces the two actors
jointly to be a p-group in a characteristic-p ambient group. -/
theorem isPGroup_sup_of_centralized_displacement
    (Q A C E : Subgroup G) (hQ : IsPGroup p Q) (hC : IsPGroup p C)
    (hAQ : A ≤ normalizer (Q : Set G)) (hCQ : C ≤ normalizer (Q : Set G))
    (hcentral : (A ⊔ C) ⊓ centralizer (Q : Set G) ≤ Q)
    (hcomm : ⁅Q,A⁆ ≤ E)
    (hAE : A ≤ centralizer (E : Set G)) (hCE : C ≤ centralizer (E : Set G)) :
    IsPGroup p (A ⊔ C : Subgroup G) := by
  let L := A ⊔ C
  let N := conjugateSpanBy A L
  have hNL : N ≤ L := conjugateSpanBy_le_self le_sup_left
  have hLE : L ≤ centralizer (E : Set G) := sup_le hAE hCE
  have hLQ : L ≤ normalizer (Q : Set G) := sup_le hAQ hCQ
  have hNQ : ⁅N,Q⁆ ≤ E := by
    rw [commutator_conjugateSpanBy_of_normalized_right A L Q le_sup_left hLQ]
    exact conjugateSpanBy_le ((commutator_comm A Q).trans_le hcomm)
      (hLE.trans (centralizer_le_normalizer _))
  have hquad : ⁅⁅Q,N⁆,N⁆ = ⊥ := by
    rw [commutator_comm Q N]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hNQ.trans (le_centralizer_iff.mp (hNL.trans hLE)))
  have hNp := isPGroup_of_quadratic_core_action Q N hQ (hNL.trans hLQ)
    ((inf_le_inf_right _ hNL).trans hcentral) hquad
  have hcover : N ⊔ C = L := le_antisymm (sup_le hNL le_sup_right)
    (sup_le ((le_conjugateSpanBy A L).trans le_sup_left) le_sup_right)
  change IsPGroup p L
  rw [←hcover]
  exact hNp.to_sup_of_normal_left' hC
    (le_sup_right.trans (le_normalizer_conjugateSpanBy A L))

end Subgroup
