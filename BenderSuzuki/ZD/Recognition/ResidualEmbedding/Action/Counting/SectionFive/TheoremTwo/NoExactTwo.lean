module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.Seeds
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary

/-!
# Normalizers when no p-subgroup fixes exactly two points

A p-subgroup maximal with at least three fixed points through a specified
point is Sylow in each pair stabilizer through that point. The distinguished
swaps from Section 3 therefore make its normalizer transitive on its fixed
set. Conjugating a larger candidate to retain the specified point promotes
this local maximality to global maximality. Proposition 5.2 then supplies a
distinguished involution fixing a point of that set, and normalizer
transitivity supplies one at every point.

This is the second clause of GLS, Volume 4, Chapter 2, Theorem 2, from the
no-exact-two branch of Lemma 5.8, printed p.41. The transitivity argument
adapts the source calculation in SE.Theorem2 to the distinguished swaps;
no ambient strong embedding is assumed.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise

private theorem local_maximal_two_fixed_transitive_and_global
    {X : Type*} [Group X] [Finite X] {M P : Subgroup X} {Z : Set X}
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    {p : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p)
    {beta : conjugateCosetSpace M}
    (hPp : IsPGroup p P)
    (hPbeta : P ≤ MulAction.stabilizer X beta)
    (hPtwo : 2 ≤ Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P})
    (hmax : ∀ Q : Subgroup X,
      IsPGroup p Q →
      Q ≤ MulAction.stabilizer X beta →
      2 ≤ Nat.card {omega : conjugateCosetSpace M //
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Q} →
      P ≤ Q → Q = P) :
    IsTransitiveOn (Subgroup.normalizer (P : Set X))
        (fixedPointsOfSubgroup X (conjugateCosetSpace M) P) ∧
      Maximal (fun Q : Subgroup X =>
        IsPGroup p Q ∧
          1 < Nat.card {omega : conjugateCosetSpace M //
            omega ∈ fixedPointsOfSubgroup X
              (conjugateCosetSpace M) Q}) P := by
  classical
  let Omega := conjugateCosetSpace M
  have hbeta : beta ∈ fixedPointsOfSubgroup X Omega P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPbeta hxP)
  have hreach : ∀ gamma : Omega,
      gamma ∈ fixedPointsOfSubgroup X Omega P →
      ∃ n : Subgroup.normalizer (P : Set X),
        (n : X) • beta = gamma := by
    intro gamma hgamma
    by_cases hbetaGamma : beta = gamma
    · exact ⟨1, by simp [hbetaGamma]⟩
    let D : Subgroup X :=
      MulAction.stabilizer X beta ⊓ MulAction.stabilizer X gamma
    have hPD : P ≤ D := by
      intro x hxP
      exact ⟨hPbeta hxP,
        MulAction.mem_stabilizer_iff.mpr (hgamma x hxP)⟩
    let PD : Subgroup D := P.subgroupOf D
    have hPDp : IsPGroup p PD :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
    obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
    let Q : Subgroup X := (S : Subgroup D).map D.subtype
    have hPQ : P ≤ Q := by
      intro x hxP
      let xD : D := ⟨x, hPD hxP⟩
      exact Subgroup.mem_map.mpr
        ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
    have hQp : IsPGroup p Q := S.isPGroup'.map D.subtype
    have hQD : Q ≤ D := by
      simpa [Q] using Subgroup.map_le_range D.subtype (S : Subgroup D)
    have hQbeta : beta ∈ fixedPointsOfSubgroup X Omega Q := by
      intro x hxQ
      exact MulAction.mem_stabilizer_iff.mp (hQD hxQ).1
    have hQgamma : gamma ∈ fixedPointsOfSubgroup X Omega Q := by
      intro x hxQ
      exact MulAction.mem_stabilizer_iff.mp (hQD hxQ).2
    have hQtwo : 2 ≤ Nat.card {omega : Omega //
        omega ∈ fixedPointsOfSubgroup X Omega Q} := by
      let f : Fin 2 → {omega : Omega //
          omega ∈ fixedPointsOfSubgroup X Omega Q} :=
        fun i => if i = 0 then ⟨beta, hQbeta⟩ else ⟨gamma, hQgamma⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaGamma
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaGamma
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
    have hQP : Q = P :=
      hmax Q hQp (hQD.trans inf_le_left) hQtwo hPQ
    have hPsyl : theorem4bIsSylowSubgroupOf p P D :=
      ⟨S, by simpa [Q] using hQP.symm⟩
    obtain ⟨t, _ht, htNorm, htBeta⟩ :=
      sectionFive_distinguished_sylow_swap
        h h3 hp hpOdd hbetaGamma hPsyl
    exact ⟨⟨t, htNorm⟩, htBeta⟩
  have htrans : IsTransitiveOn (Subgroup.normalizer (P : Set X))
      (fixedPointsOfSubgroup X Omega P) := by
    intro gamma delta hgamma hdelta
    obtain ⟨ngamma, hngamma⟩ := hreach gamma hgamma
    obtain ⟨ndelta, hndelta⟩ := hreach delta hdelta
    let n : Subgroup.normalizer (P : Set X) := ndelta * ngamma⁻¹
    refine ⟨n, ?_⟩
    change ((ndelta : X) * (ngamma : X)⁻¹) • gamma = delta
    rw [mul_smul, ← hngamma]
    simp [hndelta]
  refine ⟨htrans, ⟨⟨hPp, by omega⟩, ?_⟩⟩
  intro Q hQgood hPQ
  let FixedQ := {omega : Omega //
    omega ∈ fixedPointsOfSubgroup X Omega Q}
  have hFixedQpos : 0 < Nat.card FixedQ := by
    exact lt_trans (by decide) hQgood.2
  let : Nonempty FixedQ := (Nat.card_pos_iff.mp hFixedQpos).1
  let deltaQ : FixedQ := Classical.choice inferInstance
  let delta : Omega := deltaQ
  have hdeltaQ : delta ∈ fixedPointsOfSubgroup X Omega Q :=
    deltaQ.property
  have hdeltaP : delta ∈ fixedPointsOfSubgroup X Omega P := by
    intro x hxP
    exact hdeltaQ x (hPQ hxP)
  obtain ⟨n, hn⟩ := htrans hdeltaP hbeta
  let Qn : Subgroup X := Q.conjBy (n : X)
  have hQnp : IsPGroup p Qn := by
    exact hQgood.1.map (MulAut.conj (n : X)).toMonoidHom
  have hPconj : P.conjBy (n : X) = P :=
    section11_conjBy_eq_of_mem_normalizer n.property
  have hPQn : P ≤ Qn := by
    rw [← hPconj]
    exact Subgroup.map_mono hPQ
  have hnInvBeta : (n : X)⁻¹ • beta = delta := by
    rw [← hn]
    exact inv_smul_smul (n : X) delta
  have hQnBeta : Qn ≤ MulAction.stabilizer X beta := by
    intro x hxQn
    change x ∈ Q.conjBy (n : X) at hxQn
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxQn
    rcases hxQn with ⟨y, hyQ, rfl⟩
    apply MulAction.mem_stabilizer_iff.mpr
    calc
      ((n : X) * y * (n : X)⁻¹) • beta =
          (n : X) • (y • ((n : X)⁻¹ • beta)) := by
            simp [mul_smul, mul_assoc]
      _ = (n : X) • (y • delta) := by rw [hnInvBeta]
      _ = (n : X) • delta := by rw [hdeltaQ y hyQ]
      _ = beta := hn
  have hQntwo : 2 ≤ Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup X Omega Qn} := by
    let f : FixedQ → {omega : Omega //
        omega ∈ fixedPointsOfSubgroup X Omega Qn} := fun omega =>
      ⟨(n : X) • (omega : Omega), by
        intro x hxQn
        change x ∈ Q.conjBy (n : X) at hxQn
        rw [Subgroup.conjBy, Subgroup.mem_map] at hxQn
        rcases hxQn with ⟨y, hyQ, rfl⟩
        calc
          ((n : X) * y * (n : X)⁻¹) •
              ((n : X) • (omega : Omega)) =
                (n : X) • (y • (omega : Omega)) := by
                  simp [mul_smul, mul_assoc]
          _ = (n : X) • (omega : Omega) := by
            rw [omega.property y hyQ]⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply MulAction.injective (n : X)
      exact congrArg Subtype.val hab
    have hFixedQtwo : 2 ≤ Nat.card FixedQ := by
      have hQgood' : 1 < Nat.card FixedQ := by
        simpa only [FixedQ] using hQgood.2
      omega
    exact hFixedQtwo.trans (Nat.card_le_card_of_injective f hf)
  have hQnP : Qn = P := hmax Qn hQnp hQnBeta hQntwo hPQn
  have hnInvNorm : (n : X)⁻¹ ∈
      Subgroup.normalizer (P : Set X) :=
    (Subgroup.normalizer (P : Set X)).inv_mem n.property
  have hQnP' : Q.conjBy (n : X) = P := by
    simpa [Qn] using hQnP
  have hQP : Q = P := by
    calc
      Q = (Q.conjBy (n : X)).conjBy (n : X)⁻¹ :=
        (Subgroup.conjBy_inv Q (n : X)).symm
      _ = P.conjBy (n : X)⁻¹ := by rw [hQnP']
      _ = P := section11_conjBy_eq_of_mem_normalizer hnInvNorm
  exact hQP.le

/-- In the absence of a two-point fixed set, the source maximal subgroup
has transitive normalizer and a distinguished involution at every fixed point. -/
public theorem sectionFive_normalizer_of_no_exact_two
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (hf : ActionPrimeShareMaximalFixes Z M)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hno : ¬ ∃ Q : Subgroup G, IsPGroup p Q ∧ Nat.card (theorem4bFixedPoints M Q) = 2)
    (beta : G ⧸ M) (P : Subgroup G) (hPp : IsPGroup p P)
    (hPbeta : P ≤ MulAction.stabilizer G beta)
    (hPthree : 3 ≤ Nat.card (theorem4bFixedPoints M P))
    (hmax : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ MulAction.stabilizer G beta →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) → P ≤ Q → Q = P) :
    (∀ gamma delta : G ⧸ M,
      gamma ∈ fixedPointsOfSubgroup G (G ⧸ M) P →
      delta ∈ fixedPointsOfSubgroup G (G ⧸ M) P →
      ∃ n : Subgroup.normalizer (P : Set G), (n : G) • gamma = delta) ∧
    ∀ gamma : G ⧸ M, gamma ∈ fixedPointsOfSubgroup G (G ⧸ M) P →
      ∃ s ∈ Z, s ∈ Subgroup.normalizer (P : Set G) ∧ s • gamma = gamma := by
  classical
  have hmaxTwo : ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ MulAction.stabilizer G beta →
      2 ≤ Nat.card (theorem4bFixedPoints M Q) → P ≤ Q → Q = P := by
    intro Q hQp hQbeta hQtwo hPQ
    have hne : Nat.card (theorem4bFixedPoints M Q) ≠ 2 := fun hc => hno ⟨Q, hQp, hc⟩
    exact hmax Q hQp hQbeta (by omega) hPQ
  obtain ⟨htrans, hglobal⟩ := local_maximal_two_fixed_transitive_and_global
    h h3 hp hpodd hPp hPbeta
      (by change 2 ≤ Nat.card (theorem4bFixedPoints M P); omega) hmaxTwo
  have hbeta : beta ∈ fixedPointsOfSubgroup G (G ⧸ M) P := fun x hx =>
    MulAction.mem_stabilizer_iff.mp (hPbeta hx)
  let betaP : theorem4bFixedPoints M P := ⟨beta, hbeta⟩
  let : Nontrivial (theorem4bFixedPoints M P) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨delta, hd⟩ := exists_ne betaP
  have hbd : beta ≠ delta.val := fun he => hd (Subtype.ext he.symm)
  let D := MulAction.stabilizer G beta ⊓ MulAction.stabilizer G delta.val
  have hPD : P ≤ D := le_inf hPbeta (fun x hx => MulAction.mem_stabilizer_iff.mpr (delta.property x hx))
  obtain ⟨R, hPR⟩ := (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm).exists_le_sylow
  let Rg : Subgroup G := (R : Subgroup D).map D.subtype
  have hPRg : P ≤ Rg := fun x hx => ⟨⟨x, hPD hx⟩, hPR hx, rfl⟩
  have hRD : Rg ≤ D := by simpa [Rg] using Subgroup.map_le_range D.subtype (R : Subgroup D)
  have hRntr : Nontrivial (theorem4bFixedPoints M Rg) :=
    ⟨⟨⟨beta, fun x hx => MulAction.mem_stabilizer_iff.mp (hRD hx).1⟩,
      ⟨delta.val, fun x hx => MulAction.mem_stabilizer_iff.mp (hRD hx).2⟩,
      fun he => hbd (congrArg Subtype.val he)⟩⟩
  have hRgP : Rg = P :=
    (hglobal.2 ⟨R.isPGroup'.map D.subtype, Finite.one_lt_card_iff_nontrivial.mpr hRntr⟩ hPRg).antisymm hPRg
  have hPsyl : theorem4bIsSylowSubgroupOf p P D := ⟨R, hRgP.symm⟩
  obtain ⟨s, hsZ, hsN, hsMove⟩ := sectionFive_distinguished_sylow_swap h h3 hp hpodd hbd hPsyl
  obtain ⟨z, hzZ, hzM⟩ := h.nonempty
  have hInv : theorem4bInvertedCard s P = theorem4bPrimeShare M z p :=
    (h3.swapping_bound z hzZ hzM s hsZ beta (by simpa [hsMove] using hbd.symm)
      p hp hpodd P hPp (by simpa only [D, hsMove] using hPD) hsN).2
      (by simpa [hsMove] using hPsyl)
  have hPc : actionPrimeShareCandidate Z M z p P := ⟨hPp, hPthree, s, hsZ, hsN, hInv⟩
  have hPcmax : Maximal (actionPrimeShareCandidate Z M z p) P := by
    refine ⟨hPc, ?_⟩
    intro Q hQc hPQ
    apply hglobal.2 _ hPQ
    refine ⟨hQc.1, ?_⟩
    change 1 < Nat.card (theorem4bFixedPoints M Q)
    have := hQc.2.1
    omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (productDisconnected_isConj h s hsZ z hzZ)
  let base : G ⧸ M := QuotientGroup.mk 1
  let alpha : G ⧸ M := g⁻¹ • base
  have hzbase : z • base = base := by
    apply MulAction.mem_stabilizer_iff.mp
    simpa only [base, baseCoset_stabilizer] using (show z ∈ M from hzM)
  have hsalpha : s • alpha = alpha := by
    apply MulAction.injective g
    calc
      g • (s • alpha) = (g * s * g⁻¹) • base := by simp [alpha, mul_smul]
      _ = base := by rw [hg, hzbase]
      _ = g • alpha := by simp [alpha]
  have hPalpha := hf z hzZ hzM p hp hpodd P hPcmax s hsZ hsN alpha hsalpha
  refine ⟨htrans, ?_⟩
  intro gamma hgamma
  have halpha : alpha ∈ fixedPointsOfSubgroup G (G ⧸ M) P := fun x hx =>
    MulAction.mem_stabilizer_iff.mp (hPalpha hx)
  obtain ⟨n, hn⟩ := htrans halpha hgamma
  refine ⟨MulAut.conj (n : G) s, h.invariant n s hsZ, ?_, ?_⟩
  · exact (Subgroup.normalizer (P : Set G)).mul_mem
      ((Subgroup.normalizer (P : Set G)).mul_mem n.property hsN)
      ((Subgroup.normalizer (P : Set G)).inv_mem n.property)
  · rw [← hn]
    simp [MulAut.conj_apply, mul_smul, hsalpha]

end BenderSuzuki.ZD
