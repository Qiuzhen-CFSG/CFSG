module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.PerfectCentralCover
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Central kernels in the alternating and binary-linear pair calculations

A central intersection visible in R/Φ(R) is invariant under every actual
automorphism of the Sylow pair. If it is invisible, a cyclic image of R would
lift to a cyclic R by the nongenerating property of the Frattini subgroup.
These observations retain the central covers in the small alternating cases.

The A₅ case is impossible even for a perfect central cover: transfer lifts
its cyclic Sylow three-subgroups to cyclic Sylow three-subgroups upstairs.
For L₄(2) and L₅(2), the order formula excludes a complement of order 27.
`BinaryMultiplierBound` is the explicitly retained universal multiplier input
from I.1.3; it contains no Sylow-pair or local-action assertion. Its application,
together with O₂(Q)=1, produces an actual isomorphism of Q with its central
quotient, and hence the surviving source model.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Proposition 1.3.4,
printed p.511 (PDF p.528), and the earlier multiplier calculation I.1.3.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
universe u v
variable {Q : Type u} [Group Q] [Finite Q]

/-- The commutator hypothesis prevents the complement from being central. -/
theorem not_le_center {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) :
    ¬ R ≤ center Q := by
  intro hc
  have hb : (⊤ : Subgroup Q) = ⊥ := h.commutator.symm.trans
    (commutator_top_left_eq_bot_iff_le_center.mpr hc)
  have hall (x : Q) : x = 1 := mem_bot.mp (hb ▸ mem_top x)
  let _ : Subsingleton R := ⟨fun x y => Subtype.ext ((hall x).trans (hall y).symm)⟩
  exact h.oddComplement.not_isCyclic inferInstance

/-- A nonzero central intersection in the Frattini quotient excludes every
two-subgroup of the actual pair automizer, including outer automorphisms. -/
theorem pairReducible_of_centralIntersection {S R : Subgroup Q}
    (hproper : ¬ R ≤ center Q)
    (hvisible : ¬ (center Q).subgroupOf R ≤ frattini R) : PairReducible S R := by
  let K := (center Q).subgroupOf R
  let π := QuotientGroup.mk' (frattini R)
  apply pairReducible_of_invariant
  refine ⟨K.map π, ?_, ?_, ?_⟩
  · intro hb
    apply hvisible
    intro x hx
    exact (QuotientGroup.eq_one_iff x).mp
      (mem_bot.mp (hb ▸ (mem_map.mpr ⟨x, hx, rfl⟩ : π x ∈ K.map π)))
  · intro ht
    have hs : K ⊔ frattini R = ⊤ := by
      simpa only [comap_map_eq, π, QuotientGroup.ker_mk', comap_top] using
        congrArg (Subgroup.comap π) ht
    have hK := frattini_nongenerating hs
    apply hproper
    intro x hx
    exact show (⟨x, hx⟩ : R) ∈ K from hK ▸ mem_top _
  · rintro b ⟨c, _, he⟩ _ ⟨x, hx, rfl⟩
    rw [quotientAut_apply_mk]
    refine mem_map.mpr ⟨b x, ?_, rfl⟩
    change (b x : Q) ∈ center Q
    rw [he]
    exact (centerCongr c ⟨x, hx⟩).property

/-- Cyclicity lifts through a kernel contained in the Frattini subgroup. -/
theorem isCyclic_of_frattini_kernel {A : Type u} {B : Type v}
    [Group A] [Finite A] [Group B] [IsCyclic B]
    (f : A →* B) (hf : Function.Surjective f) (hk : f.ker ≤ frattini A) :
    IsCyclic A := by
  obtain ⟨b, hb⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic B)
  obtain ⟨a, rfl⟩ := hf b
  have hm : (zpowers a).map f = ⊤ := by simpa only [MonoidHom.map_zpowers] using hb
  have hs : zpowers a ⊔ f.ker = ⊤ := by
    simpa only [comap_map_eq, comap_top] using congrArg (Subgroup.comap f) hm
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨a, frattini_nongenerating ?_⟩
  exact top_unique (hs ▸ sup_le_sup_left hk (zpowers a))

/-- A₅ has no noncyclic odd complement in any finite perfect central cover. -/
theorem alternating_five_false {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 5)) : False := by
  let _ := h.quasisimple
  let f : Q →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ center Q := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    simpa [f] using hx
  obtain ⟨P, hRP⟩ := h.oddComplement.isPGroup.exists_le_sylow
  have hp : IsCyclic (P.mapSurjective hf) := by
    apply isCyclic_of_prime_card (p := 3)
    rw [Sylow.card_eq_multiplicity, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    rw [show 60 = 3 ^ 1 * 20 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      (by decide : Nat.Prime 3).factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 20)]
    rfl
  let _ := PerfectCentralCovering.isCyclic_sylow_of_isCyclic_mapSurjective P f hf hk hp
  exact h.oddComplement.not_isCyclic
    (isCyclic_of_injective (inclusion hRP) (inclusion_injective hRP))

/-- The exclusion branch for the A₅ entry of Theorem C. -/
theorem alternating_five {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : Q ⧸ center Q ≃* alternatingGroup (Fin 5)) : PairReducible (S : Subgroup Q) R :=
  (alternating_five_false h e).elim

omit [Finite Q] in
/-- The orders of L₄(2) and L₅(2) are not divisible by 27. -/
theorem binary_not_dvd_twentySeven {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL Q n 2) : ¬ 27 ∣ Nat.card Q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ : NeZero n := ⟨by rcases hn with rfl | rfl <;> decide⟩
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) n
  rw [← Nat.card_congr e.toEquiv, hF] at hh
  rcases hn with rfl | rfl
  · norm_num [Fin.prod_univ_succ] at hh
    rw [hh]
    norm_num
  · norm_num [Fin.prod_univ_succ] at hh
    rw [hh]
    norm_num

/-- The exact universal central-kernel bounds from the earlier multiplier
calculation: the multipliers of L₄(2) and L₅(2) have orders two and one. -/
def BinaryMultiplierBound : Prop :=
  ∀ (K : Type u) [Group K] [Finite K], IsQuasisimple K →
    ∀ n : ℕ, (n = 4 ∨ n = 5) → ClassicalGroup.IsPSL (K ⧸ center K) n 2 →
      Nat.card (center K) ∣ if n = 4 then 2 else 1

omit [Finite Q] in
/-- O₂(Q)=1 removes the multiplier's possible central two-part. -/
theorem center_eq_bot_of_two_group (hz : IsPGroup 2 (center Q))
    (hcore : pCore 2 Q = ⊥) : center Q = ⊥ := by
  apply eq_bot_iff.mpr
  rw [← hcore]
  exact le_sSup ⟨inferInstance, hz⟩

/-- Actual cover identification for the surviving binary-linear groups. -/
theorem binary_model (hMult : BinaryMultiplierBound.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (he : ClassicalGroup.IsPSL (Q ⧸ center Q) n 2) : ClassicalGroup.IsPSL Q n 2 := by
  have hd : Nat.card (center Q) ∣ 2 := by
    have hd := hMult Q h.quasisimple n hn he
    rcases hn with rfl | rfl
    · simpa using hd
    · exact (by simpa using hd : Nat.card (center Q) ∣ 1).trans (one_dvd 2)
  have hz : IsPGroup 2 (center Q) := by
    apply IsPGroup.iff_card.mpr
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
    · exact ⟨0, by simpa using hc⟩
    · exact ⟨1, by simpa using hc⟩
  have hZ := center_eq_bot_of_two_group hz h.twoCore
  let e : Q ≃* Q ⧸ center Q :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  obtain ⟨F, hfield, hfinite, hF, ⟨f⟩⟩ := he
  exact ⟨F, hfield, hfinite, hF, ⟨e.trans f⟩⟩

/-- The binary-linear source alternatives, including the actual E₉ complement.
Only the named universal multiplier implication is retained as a parameter. -/
theorem binary_surviving (hMult : BinaryMultiplierBound.{u})
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (he : ClassicalGroup.IsPSL (Q ⧸ center Q) n 2) :
    Nonempty (R ≃* Plane 3) ∧ ExceptionalModel Q := by
  have hm := binary_model hMult h hn he
  refine ⟨plane_of_odd_complement_card h.oddComplement ?_, ?_⟩
  · intro hc
    exact binary_not_dvd_twentySeven hn hm
      (by simpa only [hc, Nat.reducePow] using Subgroup.card_subgroup_dvd_card R)
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr hm)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.AlternatingBinary
