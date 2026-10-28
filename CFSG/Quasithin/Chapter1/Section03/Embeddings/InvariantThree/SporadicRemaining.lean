module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M22.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS
public import Theory.SpecificGroups.Held.Model.Basic
public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# The remaining sporadic branches of the invariant-three sieve

The J₁ case is excluded for every finite quasisimple central cover. Its
concrete matrix model has Sylow three-subgroups of order three. Cyclic
Sylow subgroups lift through perfect central extensions, so the cover has
three-rank at most one, contradicting `PairInput.rank`.

For M₁₁ the checked order 7920 rules out a complement of order 27; the
remaining complement is an actual elementary plane. The trivial-multiplier
implication is stated as an explicit universal earlier input.

The M₁₂, M₂₂, HS, He and Ru subgroup restrictions still require proof.
The imported cover reductions preserve the possible central three-cover
of M₂₂. No complete seven-case sieve is asserted by this module yet.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing Aschbacher, *Overgroups of Sylow subgroups in sporadic
groups*, Memoirs AMS 60, no.343 (1986). Multiplier values use GLS3 §5.3.
-/

@[expose] public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

universe u

/-- The seven fixed central-quotient models in this part of the sieve. -/
def IsRemainingSporadicQuotient (Q : Type u) [Group Q] : Prop :=
  Nonempty (Q ⧸ center Q ≃* Sporadic.Mathieu.M11) ∨
  Nonempty (Q ⧸ center Q ≃* Sporadic.Mathieu.M12) ∨
  Nonempty (Q ⧸ center Q ≃* Sporadic.Mathieu.M22) ∨
  Nonempty (Q ⧸ center Q ≃* Sporadic.LeechRelated.HS.Carrier) ∨
  Nonempty (Q ⧸ center Q ≃* Held.He) ∨
  Nonempty (Q ⧸ center Q ≃* Rudvalis.Model) ∨
  Nonempty (Q ⧸ center Q ≃* Janko1.Model)

/-- The concrete J₁ order has three-part three. -/
theorem j1_sylow_three_isCyclic (P : Sylow 3 Janko1.Model) : IsCyclic P := by
  apply isCyclic_of_prime_card (p := 3)
  have hzero : padicValNat 3 58520 = 0 :=
    padicValNat.eq_zero_iff.mpr (Or.inr (Or.inr (by norm_num)))
  rw [Sylow.card_eq_multiplicity, Janko1.card_model,
    Nat.factorization_def 175560 Nat.prime_three,
    show (175560 : ℕ) = 3 ^ 1 * 58520 by norm_num,
    padicValNat_base_pow_mul (by norm_num) (by norm_num) 1, hzero]
  rfl

/-- The three-rank obstruction persists in every perfect central cover of J₁. -/
theorem j1_cover_three_rank_le_one {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] (e : Q ⧸ center Q ≃* Janko1.Model) :
    primeRank 3 Q ≤ 1 := by
  let f : Q →* Janko1.Model := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ center Q := by
    intro x hx
    change e (QuotientGroup.mk' (center Q) x) = 1 at hx
    have hx' : e (QuotientGroup.mk' (center Q) x) = e 1 := by
      simpa only [map_one] using hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective hx')
  let P : Sylow 3 Q := default
  exact P.primeRank_le_one_of_isCyclic
    (isCyclic_sylow_of_isCyclic_mapSurjective P f hf hk (j1_sylow_three_isCyclic _))

/-- The J₁ branch of the source sieve: no genuine input pair exists. -/
theorem j1_no_pair {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* Janko1.Model) : False := by
  let _ := h.quasisimple.toIsPerfect
  have hr := j1_cover_three_rank_le_one e
  rw [h.rank] at hr
  omega

/-- The actual M₁₁ group admits no complement of extraspecial order 27. -/
theorem m11_plane_of_equiv {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ≃* Sporadic.Mathieu.M11) : Nonempty (R ≃* Plane 3) := by
  apply plane_of_odd_complement_card h.oddComplement
  intro hc
  have hd := R.card_subgroup_dvd_card
  rw [hc, Nat.card_congr e.toEquiv, Sporadic.Mathieu.m11_order] at hd
  norm_num at hd

/-- The M₁₁ survivor, using only the precise universal trivial-multiplier
implication as an earlier parameter. The isomorphism identifies Q itself. -/
theorem m11_survivor_of_multiplier
    (hbound : CentralKernelDivides.{u,0} Sporadic.Mathieu.M11 1)
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (e : Q ⧸ center Q ≃* Sporadic.Mathieu.M11) :
    Nonempty (R ≃* Plane 3) ∧ Nonempty (Q ≃* Sporadic.Mathieu.M11) := by
  let _ := h.quasisimple.toIsPerfect
  have hZ : center Q = ⊥ :=
    (center Q).eq_bot_of_card_eq (Nat.dvd_one.mp (center_card_dvd hbound e))
  let f := equiv_of_center_eq_bot e hZ
  exact ⟨m11_plane_of_equiv h f, ⟨f⟩⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
