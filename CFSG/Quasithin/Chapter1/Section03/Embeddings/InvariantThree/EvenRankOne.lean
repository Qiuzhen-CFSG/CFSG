module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankOne.CentralImage
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankOne.Unitary
public import CFSG.Quasithin.ClassificationModels
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import BenderSuzuki.SE.Section11Lemma114Models
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Characteristic-two rank-one cases of the three-rank sieve

The linear case uses the cyclic odd Sylow subgroups of the actual binary
PSL₂ model. The central-image argument then applies even to a nontrivial
central cover. The Suzuki case has no nontrivial three-subgroup in its
simple quotient, so [Q,R]=Q gives a contradiction.

The unitary case uses its natural action to prove the Sylow pair generates
a proper subgroup, hence lies in the Borel. Its image in the cyclic Cartan
quotient is faithful. The central-image argument then handles every central
cover. All three constructors of the complete Bender list are discharged,
without multiplier assumptions or an irreducibility hypothesis in the input.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed pp.510–511
(PDF pp.527–528). These are the rank and Cartan steps of the p=3 sieve.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankOne

variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem nontrivial_of_pairInput {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) : Nontrivial Q := by
  let _ := h.quasisimple.simple
  exact (QuotientGroup.mk'_surjective (center Q)).nontrivial

/-- The linear branch retains the finite-field equivalence to the binary carrier. -/
theorem linear (S : Sylow 2 Q) (R : Subgroup Q) (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 (2 ^ f)) :
    PairReducible (S : Subgroup Q) R := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hmodel
  let _ := Fintype.ofFinite F
  let _ := Fintype.ofFinite (BenderSuzuki.PFAppendixIII.BinaryGaloisField f)
  let ef : F ≃+* BenderSuzuki.PFAppendixIII.BinaryGaloisField f :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
      exact (GaloisField.card 2 f (by omega)).symm)
  let em := e.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv ef)
  have hp : IsPGroup 3 (centralImage R) :=
    h.oddComplement.isPGroup.map (QuotientGroup.mk' (center Q))
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  let _ : IsCyclic P :=
    BenderSuzuki.lemma114_psl2_oddSylow_isCyclic_of_equiv hf em 3 (by decide) P
  let _ := nontrivial_of_pairInput h
  exact pairReducible_of_cyclic_centralImage (S : Subgroup Q) R h.oddComplement
    h.commutator (Subgroup.isCyclic_of_le hP)

/-- A three-free central quotient forces a three-subgroup to be central. -/
theorem centralTrace_eq_top_of_three_free (R : Subgroup Q) (hR : IsPGroup 3 R)
    (hfree : ¬ 3 ∣ Nat.card (Q ⧸ center Q)) : centralTrace R = ⊤ := by
  have hp : IsPGroup 3 (centralImage R) := hR.map (QuotientGroup.mk' (center Q))
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hn0 : n = 0 := by
    by_contra hn0
    apply hfree
    exact (hn ▸ dvd_pow_self 3 hn0).trans (centralImage R).card_subgroup_dvd_card
  have hb : centralImage R = ⊥ := Subgroup.card_eq_one.mp (by simpa [hn0] using hn)
  apply top_unique
  intro x _
  change (x : Q) ∈ center Q
  apply (QuotientGroup.eq_one_iff (x : Q)).mp
  exact show (QuotientGroup.mk' (center Q)) (x : Q) ∈ (⊥ : Subgroup (Q ⧸ center Q)) from
    hb ▸ mem_map_of_mem (QuotientGroup.mk' (center Q)) x.property

/-- The Suzuki branch contradicts generation by the commutators with R, for every cover. -/
theorem suzuki_false (S : Sylow 2 Q) (R : Subgroup Q) (h : PairInput S R)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (Q ⧸ center Q) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let _ := nontrivial_of_pairInput h
  apply centralTrace_ne_top R h.commutator
  apply centralTrace_eq_top_of_three_free R h.oddComplement.isPGroup
  rw [Nat.card_congr e.toEquiv]
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega)

theorem suzuki (S : Sylow 2 Q) (R : Subgroup Q) (h : PairInput S R)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (Q ⧸ center Q) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    PairReducible (S : Subgroup Q) R :=
  (suzuki_false S R h hm e).elim

/-- Quotienting the genuine Sylow pair gives the small unitary Borel case. -/
theorem unitary (S : Sylow 2 Q) (R : Subgroup Q) (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU (Q ⧸ center Q) 3 (2 ^ f)) :
    PairReducible (S : Subgroup Q) R := by
  let q := QuotientGroup.mk' (center Q)
  let T := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hRcard : Nat.card R ≤ 27 := by
    rcases h.oddComplement with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> norm_num [hc]
  have hcard : Nat.card (centralImage R) ≤ 27 :=
    (Nat.card_le_card_of_surjective (q.subgroupMap R) (q.subgroupMap_surjective R)).trans
      hRcard
  have hp : IsPGroup 3 (centralImage R) := h.oddComplement.isPGroup.map q
  have hperm : (centralImage R : Set (Q ⧸ center Q)) * (T : Set (Q ⧸ center Q)) =
      (T : Set (Q ⧸ center Q)) * (centralImage R : Set (Q ⧸ center Q)) := by
    have hh := congrArg (fun s : Set Q => q '' s) h.permutes
    change (R.map q : Set (Q ⧸ center Q)) * ((S : Subgroup Q).map q : Set _) =
      ((S : Subgroup Q).map q : Set _) * (R.map q : Set _)
    simpa only [Sylow.coe_coe, coe_map, Set.image_mul] using hh
  let _ := nontrivial_of_pairInput h
  exact pairReducible_of_cyclic_centralImage (S : Subgroup Q) R h.oddComplement
    h.commutator (unitary_smallPair_isCyclic hf hmodel T (centralImage R) hp hcard hperm)

/-- The full characteristic-two rank-one exclusion for the source Sylow pair.
All actual Bender-model constructors, parameter bounds, and central covers
are included; no additional theorem premise remains to be discharged. -/
theorem pairReducible_of_benderModel (S : Sylow 2 Q) (R : Subgroup Q) (h : PairInput S R)
    (hmodel : ClassificationModels.IsBenderModel (Q ⧸ center Q)) :
    PairReducible (S : Subgroup Q) R := by
  cases hmodel with
  | linear f hf he => exact linear S R h hf he
  | unitary f hf he => exact unitary S R h hf he
  | suzuki m hm he => exact suzuki S R h hm he.some

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankOne
