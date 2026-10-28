module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Gamma
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Signalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree

/-!
# Minimal theta choice and assembly of the distinguished chain

The geometric input is Proposition 7.4, stated as `ActionGamma`. We choose
an actual nonbase coset minimizing the order of its theta core, apply Lemma
7.5, and use conjugation for the cardinality comparison of Lemma 7.7.
The closure argument constructs the conjugate p-group required by Lemma 7.6.

The final assembly constructs Gamma and proves the local signalizer
inclusion inside `W₁ O_{2'}(D)`. It discharges the full theta chain from
the minimal-counterexample, simple-reduction and counting hypotheses;
the two-point stabilizer `D` may have even order.

Source: GLS, Volume 4, Chapter 2, Proposition 7.4 and Lemmas 7.5--7.7.
The closure and minimal-choice arguments adapt `SE.Section7` and
`SE.Section7Proposition74` without their ambient strong-embedding premise.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Convert (7C) to the subgroup input of the signalizer argument. This
constructs `W₁` as the conjugate of `W`, so its p-group property is proved. -/
public theorem action_conjugate_pgroup_centralizer_le
    (d : ActionCounterexample Z M) {beta : G ⧸ M} (t : G)
    (hK1E : rightConjugateSet d.toTheorem4bSixA.invertedSet
      (rightConjugateElem t d.z) ⊆ theorem4bSection7E M d.z beta)
    (hcent : theorem4bSection7D M beta ⊓
      Subgroup.centralizer (rightConjugateSet d.toTheorem4bSixA.invertedSet
        (rightConjugateElem t d.z)) ≤ theorem4bSection7E M d.z beta) :
    ∃ W₁ : Subgroup (theorem4bSection7D M beta), IsPGroup d.p W₁ ∧
      W₁ ⊔ Subgroup.centralizer (W₁ : Set (theorem4bSection7D M beta)) ≤
        (theorem4bSection7E M d.z beta).subgroupOf (theorem4bSection7D M beta) := by
  classical
  let : Fact d.p.Prime := ⟨d.hp⟩
  let g : G := rightConjugateElem t d.z
  let K1 : Set G := rightConjugateSet d.toTheorem4bSixA.invertedSet g
  let W1G : Subgroup G := rightConjugate d.W g
  have hclosureConj :
      Subgroup.closure (rightConjugateSet d.toTheorem4bSixA.invertedSet g) =
        rightConjugate (Subgroup.closure d.toTheorem4bSixA.invertedSet) g := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by simpa [rightConjugateElem] using hxy.symm⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, by simpa [rightConjugateElem] using hxy.symm⟩
  have hclosureK1 : Subgroup.closure K1 = W1G := by
    calc
      Subgroup.closure K1 =
          rightConjugate (Subgroup.closure d.toTheorem4bSixA.invertedSet) g := by
            simpa [K1] using hclosureConj
      _ = W1G := by rw [d.toTheorem4bSixA.closure_invertedSet_eq]
  have hW1GE : W1G ≤ theorem4bSection7E M d.z beta := by
    rw [← hclosureK1, Subgroup.closure_le]
    simpa [K1, g] using hK1E
  have hED : theorem4bSection7E M d.z beta ≤
      theorem4bSection7D M beta := inf_le_left
  have hW1GD : W1G ≤ theorem4bSection7D M beta := hW1GE.trans hED
  let W1 : Subgroup (theorem4bSection7D M beta) :=
    W1G.subgroupOf (theorem4bSection7D M beta)
  have hW1Gp : IsPGroup d.p W1G := by
    change IsPGroup d.p
      (d.W.map (MulAut.conj g⁻¹).toMonoidHom)
    exact d.hWp.map (MulAut.conj g⁻¹).toMonoidHom
  have hW1p : IsPGroup d.p W1 :=
    hW1Gp.of_equiv (Subgroup.subgroupOfEquivOfLe hW1GD).symm
  have hW1E : W1 ≤
      (theorem4bSection7E M d.z beta).subgroupOf
        (theorem4bSection7D M beta) := by
    intro x hx
    have hxE : (x : G) ∈ theorem4bSection7E M d.z beta := hW1GE hx
    exact (Subgroup.mem_subgroupOf).2 hxE
  have hcentW1E : Subgroup.centralizer
      (W1 : Set (theorem4bSection7D M beta)) ≤
        (theorem4bSection7E M d.z beta).subgroupOf
          (theorem4bSection7D M beta) := by
    intro x hx
    have hxK1 : (x : G) ∈ Subgroup.centralizer K1 := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkW1G : k ∈ W1G := by
        rw [← hclosureK1]
        exact Subgroup.subset_closure hk
      let kD : theorem4bSection7D M beta := ⟨k, hW1GD hkW1G⟩
      have hkW1 : kD ∈ W1 := by
        exact (Subgroup.mem_subgroupOf).2 hkW1G
      have hcomm := Subgroup.mem_centralizer_iff.mp hx kD hkW1
      exact congrArg Subtype.val hcomm
    have hxE : (x : G) ∈ theorem4bSection7E M d.z beta :=
      hcent ⟨x.property, by simpa [K1, g] using hxK1⟩
    exact (Subgroup.mem_subgroupOf).2 hxE
  exact ⟨W1, hW1p, sup_le hW1E hcentW1E⟩

private theorem action_exists_minimal_nonbase_theta
    (d : ActionCounterexample Z M) (Gamma : Set (G ⧸ M))
    (hbase : (QuotientGroup.mk 1 : G ⧸ M) ∈ Gamma)
    (hcard : 1 < Nat.card Gamma) :
    ∃ beta : G ⧸ M, beta ∈ Gamma ∧ beta ≠ QuotientGroup.mk 1 ∧
      ∀ gamma : G ⧸ M, gamma ∈ Gamma → gamma ≠ QuotientGroup.mk 1 →
        Nat.card (corollary64Theta d.p (theorem4bSection7D M beta)) ≤
          Nat.card (corollary64Theta d.p (theorem4bSection7D M gamma)) := by
  classical
  have hnonbase : ∃ beta : G ⧸ M,
      beta ∈ Gamma ∧ beta ≠ QuotientGroup.mk 1 := by
    by_contra h
    push Not at h
    have hcardOne : Nat.card Gamma = 1 := by
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨QuotientGroup.mk 1, hbase⟩, ?_⟩
      intro beta
      apply Subtype.ext
      exact h beta.1 beta.2
    omega
  let S : Set (G ⧸ M) := {beta | beta ∈ Gamma ∧ beta ≠ QuotientGroup.mk 1}
  let : Fintype S := Fintype.ofFinite S
  have hSuniv : (Finset.univ : Finset S).Nonempty := by
    obtain ⟨beta, hbeta, hne⟩ := hnonbase
    exact ⟨⟨beta, hbeta, hne⟩, by simp⟩
  obtain ⟨beta, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset S)
    (fun beta : S => Nat.card (corollary64Theta d.p
      (theorem4bSection7D M beta.1))) hSuniv
  refine ⟨beta.1, beta.2.1, beta.2.2, ?_⟩
  intro gamma hgamma hne
  exact hmin ⟨gamma, hgamma, hne⟩ (by simp)

/-- Assembly of Lemmas 7.5--7.7 from their geometric and local signalizer
inputs, without imposing odd order on the two-point stabilizer. -/
public theorem actionThetaChain_of_gamma_and_signalizer
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M)
    (hGamma : ActionGamma d)
    (hsignalizer : ∀ beta : G ⧸ M,
      beta ∈ d.toTheorem4bSixA.kFixedPoints → beta ≠ QuotientGroup.mk 1 →
      ∀ W₁ : Subgroup (theorem4bSection7D M beta), IsPGroup d.p W₁ →
        W₁ ⊔ Subgroup.centralizer (W₁ : Set (theorem4bSection7D M beta)) ≤
          (theorem4bSection7E M d.z beta).subgroupOf (theorem4bSection7D M beta) →
        corollary64Theta d.p (theorem4bSection7E M d.z beta) ≤
          corollary64Theta d.p (theorem4bSection7D M beta)) :
    ActionThetaChain d := by
  obtain ⟨Gamma, hGammaK, hbase, hcard, hzGamma, hpair, hlocal⟩ := hGamma
  obtain ⟨beta, hbetaGamma, hbetaNe, hminimal⟩ :=
    action_exists_minimal_nonbase_theta d Gamma hbase hcard
  have hbetaK := hGammaK hbetaGamma
  obtain ⟨t, _htZ, _htBase, hK1E, hcent, g, hgzbeta, hgbetaGamma⟩ :=
    hlocal beta hbetaGamma hbetaNe
  have hzMoves : d.z • beta ≠ beta := by
    intro hfix
    exact hbetaNe (action_fixedPoint_eq_base h d.hzZ d.hzM hfix)
  have hpairF := hpair beta (d.z • beta) hbetaGamma
    ((hzGamma beta).mp hbetaGamma) (Ne.symm hzMoves)
  have hCFW : subgroupCentralizerIn (theorem4bSection7F d.z beta) d.W ≤ M := by
    intro x hx
    apply hpairF
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer d.toTheorem4bSixA.invertedSet
    have hxCW : x ∈ Subgroup.centralizer (d.W : Set G) := hx.2
    rw [← d.toTheorem4bSixA.closure_invertedSet_eq] at hxCW
    simpa only [Subgroup.centralizer_closure] using hxCW
  have hFE := action_lemma75 h d hbetaK hCFW
  obtain ⟨W₁, hW₁p, hW₁E⟩ := action_conjugate_pgroup_centralizer_le d t hK1E hcent
  have hED := hsignalizer beta hbetaK hbetaNe W₁ hW₁p hW₁E
  have hgbetaNe : g • beta ≠ (QuotientGroup.mk 1 : G ⧸ M) := by
    intro hgbeta
    have heq : beta = d.z • beta := smul_left_cancel g (hgbeta.trans hgzbeta.symm)
    exact hzMoves heq.symm
  have hbound := theorem4b_lemma77_of_minimal d.p Gamma hminimal
    hgbetaGamma hgbetaNe rfl hgzbeta
  exact ⟨beta, hbetaK, hbetaNe, hFE, hED, hbound⟩

/-- The complete distinguished theta chain of GLS Lemmas 7.5--7.7. -/
public theorem actionThetaChain_of_minimalCounterexample
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M) :
    ActionThetaChain d.data := by
  have h3 := actionSectionThree_of_productDisconnected h.disconnected
  apply actionThetaChain_of_gamma_and_signalizer h.disconnected d.data
    (actionGamma_of_minimalCounterexample h r hc h3 d)
  intro beta _hbeta hne W₁ hW₁p hW₁E
  exact action_lemma76 h.disconnected h3 d.data hne W₁ hW₁p hW₁E

end BenderSuzuki.ZD
