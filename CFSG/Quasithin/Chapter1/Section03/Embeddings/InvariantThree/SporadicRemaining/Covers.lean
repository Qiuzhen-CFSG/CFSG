module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair

/-!
# Central-cover reductions for the remaining sporadic cases

`CentralKernelDivides K n` states the precise universal consequence of a
Schur-multiplier bound: the kernel of every finite perfect central extension
of the fixed group K has order dividing n. The sporadic multiplier table is
an explicit earlier input, not a conclusion proved by this module.

When O₂(Q) = 1 the center has odd order. Thus a multiplier bound of two
removes the center, while the M₂₂ bound of twelve leaves a possible center
of order three. In particular the latter case is not identified with M₂₂.
Actual group equivalences transport the Sylow subgroup, odd complement and
permutability to a concrete model.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), with the multiplier conventions of I.1 and GLS3 §5.3.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

universe u v

/-- The universal kernel-order consequence of a Schur-multiplier bound.
The universe of the covering group is independent of that of the model. -/
def CentralKernelDivides (K : Type v) [Group K] (n : ℕ) : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* K), Function.Surjective f → f.ker ≤ center E → Nat.card f.ker ∣ n

/-- Apply the universal bound to the actual quotient by the center. -/
theorem center_card_dvd {K : Type v} [Group K] {n : ℕ}
    (hbound : CentralKernelDivides.{u,v} K n)
    {Q : Type u} [Group Q] [Finite Q] [Group.IsPerfect Q]
    (e : Q ⧸ center Q ≃* K) : Nat.card (center Q) ∣ n := by
  let f : Q →* K := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hk : f.ker = center Q := by
    ext x
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hd := hbound Q f (e.surjective.comp (QuotientGroup.mk'_surjective _)) hk.le
  rwa [hk] at hd

/-- A trivial two-core rules out two-torsion in the center. -/
theorem two_not_dvd_center_card {Q : Type*} [Group Q] [Finite Q]
    (hcore : pCore 2 Q = ⊥) : ¬ 2 ∣ Nat.card (center Q) := by
  let P : Sylow 2 (center Q) := default
  have hl := P.map_le_pCore (inferInstance : (center Q).Normal) inferInstance 2
  have hP : (P : Subgroup (center Q)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hx' : (x : Q) ∈ (P : Subgroup (center Q)).map (center Q).subtype :=
      ⟨x, hx, rfl⟩
    have hone : (x : Q) = 1 := by simpa only [hcore, mem_bot] using hl hx'
    exact mem_bot.mpr (Subtype.ext hone)
  have hi := P.not_dvd_index
  simpa only [hP, index_bot] using hi

/-- A multiplier bound of two and O₂(Q) = 1 remove the center. -/
theorem center_eq_bot_of_card_dvd_two {Q : Type*} [Group Q] [Finite Q]
    (hcore : pCore 2 Q = ⊥) (hc : Nat.card (center Q) ∣ 2) : center Q = ⊥ := by
  have hp : IsPGroup 2 (center Q) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hc)
  have hl : center Q ≤ pCore 2 Q := le_sSup ⟨inferInstance, hp⟩
  exact le_bot_iff.mp (hcore ▸ hl)

/-- The M₂₂ multiplier bound allows the nontrivial central three-cover. -/
theorem center_card_dvd_three_of_dvd_twelve {Q : Type*} [Group Q] [Finite Q]
    (hcore : pCore 2 Q = ⊥) (hc : Nat.card (center Q) ∣ 12) :
    Nat.card (center Q) ∣ 3 := by
  have hcop : Nat.Coprime (Nat.card (center Q)) (2 ^ 2) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr (two_not_dvd_center_card hcore)).symm.pow_right 2
  exact hcop.dvd_of_dvd_mul_left hc

/-- Recover the group itself after proving its center trivial. -/
noncomputable def equiv_of_center_eq_bot {K Q : Type*} [Group K] [Group Q]
    (e : Q ⧸ center Q ≃* K) (hZ : center Q = ⊥) : Q ≃* K :=
  (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e

/-- The universal bound is used before identifying a centerless cover with
the actual model. -/
theorem model_equiv_of_kernel_dvd_two {K : Type v} [Group K]
    (hbound : CentralKernelDivides.{u,v} K 2)
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (e : Q ⧸ center Q ≃* K) : Nonempty (Q ≃* K) := by
  let _ := h.quasisimple.toIsPerfect
  exact ⟨equiv_of_center_eq_bot e
    (center_eq_bot_of_card_dvd_two h.twoCore (center_card_dvd hbound e))⟩

/-- All source hypotheses, including quasisimplicity and strong quasithinness,
are available on the model; a model computation need not recertify them. -/
theorem pairInput_of_equiv {K Q : Type*} [Group K] [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (e : Q ≃* K) :
    PairInput (S.mapSurjective (f := e.toMonoidHom) e.surjective) (R.map e.toMonoidHom) := by
  let _ : Finite K := Finite.of_equiv Q e.toEquiv
  let _ := h.quasisimple
  refine ⟨IsQuasisimple.of_mulEquiv e, ?_, ?_,
    (primeRank_congr 3 e).symm.trans h.rank,
    h.oddComplement.of_mulEquiv (e.subgroupMap R), ?_, ?_⟩
  · rw [← pCore_map_iso 2 e, h.twoCore, Subgroup.map_bot]
  · intro p hp ho
    rw [← primeRank_congr p e]
    exact h.stronglyQuasithin p hp ho
  · have hc := congrArg (Subgroup.map e.toMonoidHom) h.commutator
    simpa only [map_commutator, map_top_of_surjective e.toMonoidHom e.surjective] using hc
  · change (R.map e.toMonoidHom : Set K) *
        ((S : Subgroup Q).map e.toMonoidHom : Set K) =
      ((S : Subgroup Q).map e.toMonoidHom : Set K) * (R.map e.toMonoidHom : Set K)
    simpa only [coe_map, Sylow.coe_coe, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Set.image_mul] using congrArg (Set.image e) h.permutes

/-- A concrete exclusion of permuting Sylow pairs transports along an actual
group equivalence. No completeness of an exhibited subgroup list is assumed. -/
theorem no_pair_of_model_restriction {K Q : Type*} [Group K] [Group Q] [Finite Q]
    (hmodel : ∀ (T : Sylow 2 K) (P : Subgroup K),
      XiOddQuotient 3 P →
      (P : Set K) * (T : Set K) = (T : Set K) * (P : Set K) → False)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) (e : Q ≃* K) : False := by
  apply hmodel (S.mapSurjective (f := e.toMonoidHom) e.surjective) (R.map e.toMonoidHom)
  · exact h.oddComplement.of_mulEquiv (e.subgroupMap R)
  · change (R.map e.toMonoidHom : Set K) *
        ((S : Subgroup Q).map e.toMonoidHom : Set K) =
      ((S : Subgroup Q).map e.toMonoidHom : Set K) * (R.map e.toMonoidHom : Set K)
    simpa only [coe_map, Sylow.coe_coe, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Set.image_mul] using congrArg (Set.image e) h.permutes

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
