module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction

/-!
# Central obstructions for a three-complement

The intersection of R with the ambient center gives a common invariant subgroup
in R/Φ(R). If the image of R in Q/Z(Q) is cyclic, the central kernel makes R
abelian. The extraspecial alternative is then impossible, so Φ(R) is trivial.
Noncyclicity and the commutator hypothesis make the central intersection
nontrivial and proper. In particular this applies when nine does not divide
|Q/Z(Q)|, without any restriction on the multiplier.

Application: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), the binary A₂ endpoint.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear
universe u
variable {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}

omit [Finite Q] in
/-- The source commutator condition prevents a central complement. -/
theorem complement_not_le_center (h : PairInput S R) : ¬ R ≤ center Q := by
  intro hc
  have hbot : ⁅(⊤ : Subgroup Q), R⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x _ r hr
    exact (mem_center_iff.mp (hc hr) x).symm
  let _ := h.quasisimple
  let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let _ : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
  exact bot_ne_top (hbot.symm.trans h.commutator)

omit [Finite Q] in
/-- Extendible automorphisms preserve the image of the ambient center in the Frattini quotient. -/
theorem central_image_invariant (S R : Subgroup Q) (a : MulAut R)
    (ha : a ∈ pairAutomizer S R) :
    ∀ x ∈ ((center Q).comap R.subtype).map (QuotientGroup.mk' (frattini R)),
      quotientAut (frattini R) a x ∈
        ((center Q).comap R.subtype).map (QuotientGroup.mk' (frattini R)) := by
  obtain ⟨b, _, hab⟩ := ha
  rintro x ⟨r, hr, rfl⟩
  refine ⟨a r, ?_, (quotientAut_apply_mk _ _ _).symm⟩
  change (a r : Q) ∈ center Q
  rw [hab]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z, rfl⟩ := b.surjective y
  have hr' : (r : Q) ∈ center Q := hr
  simpa only [map_mul] using congrArg b (mem_center_iff.mp hr' z)

/-- A nonzero central image gives the required common invariant subgroup. -/
theorem pairReducible_of_central_not_le_frattini (h : PairInput S R)
    (hc : ¬ (center Q).comap R.subtype ≤ frattini R) :
    PairReducible (S : Subgroup Q) R := by
  apply pairReducible_of_invariant
  let C := (center Q).comap R.subtype
  let q := QuotientGroup.mk' (frattini R)
  refine ⟨C.map q, ?_, ?_, fun a ha => central_image_invariant _ _ a ha⟩
  · intro hz
    exact hc (by simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp hz)
  · intro ht
    have hsup : C ⊔ frattini R = ⊤ := by
      have he := congrArg (Subgroup.comap q) ht
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
    have hC : C = ⊤ := frattini_nongenerating hsup
    apply complement_not_le_center h
    intro r hr
    exact (show (⟨r, hr⟩ : R) ∈ C from hC.symm ▸ mem_top _)

/-- A cyclic image modulo the ambient center forces a proper invariant central line. -/
theorem pairReducible_of_cyclic_central_image (h : PairInput S R)
    (hc : IsCyclic (R.map (QuotientGroup.mk' (center Q)))) :
    PairReducible (S : Subgroup Q) R := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  let q := QuotientGroup.mk' (center Q)
  let f := q.subgroupMap R
  let _ := hc
  have hker : f.ker ≤ center R := by
    intro r hr
    have hz : (r : Q) ∈ center Q := (QuotientGroup.eq_one_iff _).mp
      (congrArg Subtype.val hr)
    exact mem_center_iff.mpr (fun s => Subtype.ext (mem_center_iff.mp hz s))
  let _ : IsMulCommutative R := f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have hPhi : frattini R = ⊥ := by
    rcases h.oddComplement with ⟨he, _⟩ | ⟨he, _, _⟩
    · let _ := he
      exact frattini_eq_bot_of_isElementaryAbelian (p := 3)
    · exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
        (center_eq_top (G := R))).elim
  apply pairReducible_of_central_not_le_frattini h
  intro hC
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro r hr
    apply (show (center Q).comap R.subtype ≤ ⊥ from hPhi ▸ hC)
    change (r : Q) ∈ center Q
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hr)
  exact h.oddComplement.not_isCyclic (isCyclic_of_injective f hf)

/-- If the central quotient has three-part at most three, every pair action is reducible. -/
theorem pairReducible_of_not_nine_dvd_central_quotient (h : PairInput S R)
    (h9 : ¬ 9 ∣ Nat.card (Q ⧸ center Q)) : PairReducible (S : Subgroup Q) R := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply pairReducible_of_cyclic_central_image h
  let q := QuotientGroup.mk' (center Q)
  let B := R.map q
  have hB : IsPGroup 3 B :=
    h.oddComplement.isPGroup.of_surjective (q.subgroupMap R) (q.subgroupMap_surjective R)
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hd := B.card_subgroup_dvd_card
  rw [hn] at hd
  have hlt : n < 2 := by
    by_contra hh
    apply h9
    exact (show 3 ^ 2 ∣ 3 ^ n from pow_dvd_pow 3 (by omega)).trans hd
  apply isCyclic_of_card_dvd_prime (p := 3)
  change Nat.card B ∣ 3
  rw [hn]
  interval_cases n <;> norm_num

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear
