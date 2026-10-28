module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.TwoCore

/-!
# Quotient kernels and the prime-center rank obstruction

Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.13–14,
printed p.37. A surjection realizing a counterexample has nontrivial proper
kernel: an isomorphism satisfies both rank inequalities, while a trivial
image contradicts the section's rank greater than two. Thus the ambient
counterexample is not simple.

When quasisimplicity is supplied by the still-required A.2.12 reduction,
the kernel is central. If the center has order p, this nontrivial kernel is
the whole center, giving the second assertion of A.2.14. These results do
not assert the missing quasisimplicity or the prime-group center statement.
-/

public section

open Theory.GroupTheory Subgroup


namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- A counterexample cannot be realized by an isomorphism. -/
theorem CounterexampleToTheoremA.ker_ne_bot
    (h : CounterexampleToTheoremA K G S p) (f : G →* S)
    (hf : Function.Surjective f) : f.ker ≠ ⊥ := by
  intro hk
  let e := MulEquiv.ofBijective f ⟨f.ker_eq_bot_iff.mp hk, hf⟩
  have hc : TheoremAConclusion G G p :=
    ⟨.inl ⟨le_rfl, isQuasithin_iff_twoLocalPrimeRank.mp h.1 p
      h.2.2.2.2.1 h.2.2.2.2.2.1⟩, fun _ => le_rfl⟩
  exact h.2.2.2.2.2.2 (hc.of_mulEquiv e.symm)

/-- The offending quotient is nontrivial, as its prime rank exceeds two. -/
theorem CounterexampleToTheoremA.ker_ne_top
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) : f.ker ≠ ⊤ := by
  intro hk
  have hall : ∀ s : S, s = 1 := by
    intro s
    obtain ⟨g, rfl⟩ := hf s
    exact (MonoidHom.mem_ker.mp (hk ▸ (show g ∈ (⊤ : Subgroup G) from trivial)))
  let : Subsingleton S := ⟨fun x y => (hall x).trans (hall y).symm⟩
  have hs : primeRank p S ≤ 1 := by
    simpa only [Nat.card_unique] using (Theory.GroupTheory.primeRank_le_card (G := S) p)
  exact (not_lt_of_ge (hs.trans (by decide))) (lemma_A_2_14 h ih)

/-- The A-counterexample branch of A.2.13 cannot have simple ambient group. -/
theorem CounterexampleToTheoremA.not_isSimpleGroup
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    ¬ IsSimpleGroup G := by
  intro hs
  let := hs
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  exact ((inferInstance : f.ker.Normal).eq_bot_or_eq_top.resolve_left
    (h.ker_ne_bot f hf)) |> h.ker_ne_top ih f hf

/-- Once A.2.12 supplies quasisimplicity, the offending quotient has nontrivial central kernel. -/
theorem CounterexampleToTheoremA.quotient_by_nontrivial_center_subgroup
    [IsQuasisimple G] (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) :
    ∃ (N : Subgroup G) (_ : N.Normal), N ≠ ⊥ ∧ N ≤ center G ∧
      Nonempty ((G ⧸ N) ≃* S) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  exact ⟨f.ker, inferInstance, h.ker_ne_bot f hf,
    (IsQuasisimple.normal_le_center_or_eq_top f.ker).resolve_right (h.ker_ne_top ih f hf),
    ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

/-- A.2.14, prime-center clause, under the quasisimplicity of Case II. -/
theorem lemma_A_2_14_center [IsQuasisimple G]
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hz : Nat.card (center G) = p) : 2 < primeRank p (G ⧸ center G) := by
  obtain ⟨N, hN, hne, hle, ⟨e⟩⟩ := h.quotient_by_nontrivial_center_subgroup ih
  let := hN
  let : Fact (Nat.card (center G)).Prime := ⟨by rw [hz]; exact h.2.2.2.2.1⟩
  have heq : N = center G := by
    rcases (N.subgroupOf (center G)).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hm := congrArg (Subgroup.map (center G).subtype) hb
      rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hm
      exact (hne hm).elim
    · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp ht)
  have hr := lemma_A_2_14 h ih
  rw [← primeRank_equiv p e] at hr
  exact hr.trans_eq (primeRank_equiv p (QuotientGroup.quotientMulEquivOfEq heq))

end CFSG.Quasithin.ChapterA.Section02
