module
public import Stellmacher.SectionNine.NineFourFullRemoteObstruction

/-!
# The counterexample module-intersection bound in (9.4)

For the original ambient (9.4) hypotheses, a subgroup A outside the next
module forces that module's intersection with the moved remote module to
have index at least four. The conclusion is stated as the exact finite
cardinality inequality used by the following case analysis.

The two modules have equal order by orbit conjugacy and the remote module
is elementary abelian. Its intersection index is therefore a power of two.
Index one contradicts A's noncontainment. At index two, adjoining the
intersection to A exhausts the remote module; the enlargement preserves
the commutator containment, contrary to the full remote-module obstruction.
Thus the index is at least four. The displacement hypothesis is retained
from (9.4) for its unchanged input contract but is not needed for this step.

Source: Stellmacher (9.4)(4), printed p.51 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem eq_of_index_two_of_intermediate
    {G : Type*} [Group G] [Finite G] (I A V : Subgroup G)
    (hIA : I ≤ A) (hAV : A ≤ V) (hindex : I.relIndex V = 2)
    (hnot : ¬ A ≤ I) : A = V := by
  have hmul := Subgroup.relIndex_mul_relIndex I A V hIA hAV
  rw [hindex] at hmul
  have hdiv : I.relIndex A ∣ 2 := dvd_of_mul_right_eq (A.relIndex V) hmul
  have hIAindex : I.relIndex A = 2 := by
    exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun heq => hnot (Subgroup.relIndex_eq_one.mp heq))
  have hAVindex : A.relIndex V = 1 := by
    rw [hIAindex] at hmul
    omega
  exact le_antisymm hAV (Subgroup.relIndex_eq_one.mp hAVindex)

private theorem index_four_of_no_full_enlargement {G : Type*} [Group G] [Finite G] (U V A : Subgroup G)
    [IsElementaryAbelian 2 V] (hcard : Nat.card U = Nat.card V)
    (hA : A ≤ V) (hnot : ¬ A ≤ U)
    (hlarge : A ⊔ (V ⊓ U) = V → False) :
    4 * Nat.card (U ⊓ V : Subgroup G) ≤ Nat.card U := by
  let I := V ⊓ U
  have hI : I ≤ V := inf_le_left
  have hcount := (I.subgroupOf V).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI).toEquiv] at hcount
  change I.relIndex V * Nat.card I = Nat.card V at hcount
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 V).index (I.subgroupOf V)
  change I.relIndex V = 2 ^ k at hk
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hle : k ≤ 1 := by omega
    interval_cases k
    · simp only [pow_zero] at hk
      exact hnot (hA.trans (Subgroup.relIndex_eq_one.mp hk) |>.trans inf_le_right)
    · simp only [pow_one] at hk
      apply hlarge
      apply eq_of_index_two_of_intermediate I (A ⊔ I) V le_sup_right
        (sup_le hA hI) hk
      intro hleI
      exact hnot ((le_sup_left.trans hleI).trans inf_le_right)
  have hfour : 4 ≤ I.relIndex V := by
    rw [hk]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hk2
  rw [inf_comm U V, hcard, ← hcount]
  exact Nat.mul_le_mul_right _ hfour


public theorem nine_four_counterexample_intersection_index
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (r : ctx.Γ.Vertex)
    (hr : ctx.Γ.distance r ctx.criticalPath.firstStep = 2)
    (t : G)
    (ht : t ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∈ Subgroup.centralizer (VAt ctx.Γ r : Set G))
    (x : G)
    (hx : x ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆)
    (A : Subgroup G)
    (hA : A ≤ VAt ctx.Γ (ctx.Γ.act x r))
    (h1 : ⁅A, Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
    (h2 : ∀ n : ctx.Γ.Vertex,
      n ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
      n ∈ Neighborhood ctx.Γ (ctx.Γ.act x r) →
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
        Subgroup.zpowers t = GAt ctx.Γ ctx.criticalPath.firstStep)
    (_h3 : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep)
      (ZAt ctx.Γ ctx.criticalPath.firstStep) 2)
    (hnot : ¬ A ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act x r) : Subgroup G) ≤
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) := by
  let remote := ctx.Γ.act x r
  have hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2 :=
    nine_four_moved_distance ctx.Γ ctx.criticalPath.firstStep r t x ht.1 hx hr
  let _ : IsElementaryAbelian 2 (VAt ctx.Γ remote) :=
    nine_four_remote_elementary ctx.toLocalContext hb remote hdistance
  have hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) =
      Nat.card (VAt ctx.Γ remote) := by
    obtain ⟨mover, hmover⟩ := nine_four_distance_two_orbit ctx.sectionSeven ctx.Γ
      ctx.criticalPath.firstStep remote (by rwa [ctx.Γ.distance_symm])
    rw [← hmover]
    change Nat.card (v ctx.Γ ctx.criticalPath.firstStep) =
      Nat.card (v ctx.Γ (ctx.Γ.act mover ctx.criticalPath.firstStep))
    rw [v_act, Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective]
  apply index_four_of_no_full_enlargement _ _ A hcard hA hnot
  intro heq
  have henlarged := (nine_four_enlargement ctx.toLocalContext hb remote hdistance
    t ht.1 A hA h1).2.2.2.1
  change ⁅A ⊔ (VAt ctx.Γ remote ⊓ VAt ctx.Γ ctx.criticalPath.firstStep),
    Subgroup.zpowers t⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep at henlarged
  rw [heq] at henlarged
  exact nine_four_remote_commutator_obstruction ctx hb remote hdistance t ht.1 h2 henlarged

end Stellmacher.SectionNine
