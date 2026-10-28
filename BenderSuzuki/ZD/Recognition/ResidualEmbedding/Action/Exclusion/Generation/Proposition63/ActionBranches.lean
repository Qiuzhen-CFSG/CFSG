module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.Proposition63.Foundations
public import BenderSuzuki.PFchapter1section1.proposition_4_c

/-!
# The two action branches of distinguished Proposition 6.3

The nontrivial normal residual excludes two-transitivity. In the other
branch, Theorem 2 extends each odd-core Sylow subgroup to a subgroup
normalized by a distinguished involution. The explicit local factorization
conjugates that involution to `z` within the odd core; quotient centralization
then shows that `z` normalizes the Sylow subgroup times the residual.

Source: GLS, Volume 4, Chapter 2, Proposition 6.3, lines 1003–1023.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The source inverted set `K = I_W(z)` is contained in `Y = O²(M°)`. -/
public theorem ActionCounterexample.prop63_invertedSet_subset_residual
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M) :
    d.invertedSet ⊆
      ((prop63Residual Z M).map M.subtype : Set X) := by
  intro x hx
  have hx := (d.toTheorem4bSixA.mem_invertedSet_iff x).mp hx
  let : Fact d.p.Prime := ⟨d.hp⟩
  have hWodd : Odd (Nat.card d.W) := by
    obtain ⟨n, hn⟩ := d.hWp.exists_card_eq
    rw [hn]
    exact d.hpOdd.pow
  have hxOrderDvd : orderOf x ∣ Nat.card d.W := by
    simpa using orderOf_dvd_natCard (⟨x, hx.1⟩ : d.W)
  have hxOdd : Odd (orderOf x) := hWodd.of_dvd_nat hxOrderDvd
  have hxResidual :
      (⟨x, d.hWM hx.1⟩ : M) ∈ prop63Residual Z M :=
    prop63_mem_residual_of_inverted h
      (d.hWM hx.1) hxOdd d.hzZ d.hzM hx.2
  exact Subgroup.mem_map.mpr ⟨⟨x, d.hWM hx.1⟩, hxResidual, rfl⟩

/-- Since `K` generates the nontrivial subgroup `W`, the residual
`Y = O²(M°)` is nontrivial. -/
public theorem ActionCounterexample.prop63_residual_ne_bot
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M) : prop63Residual Z M ≠ ⊥ := by
  intro hbot
  have hmapBot :
      (prop63Residual Z M).map M.subtype =
        (⊥ : Subgroup X) := by
    rw [hbot]
    simp
  have hclosureLe : Subgroup.closure d.invertedSet ≤
      (prop63Residual Z M).map M.subtype := by
    rw [Subgroup.closure_le]
    exact d.prop63_invertedSet_subset_residual h
  have hWbot : d.W = ⊥ := by
    rw [← d.closure_invertedSet_eq]
    exact eq_bot_iff.mpr (by simpa [hmapBot] using hclosureLe)
  exact d.hWne hWbot

/-- The two-transitive branch of Proposition 6.3 is impossible.  Normality
of the nontrivial residual `Y` makes one additional fixed point propagate to
every point under the base stabilizer; simplicity then makes the action core
trivial, contradicting `Y ≠ 1`. -/
public theorem prop63_not_twoTransitive
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (hX : IsSimpleGroup X)
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M) {t : X} (ht : PFAppendixIII.IsInvolution t)
    (hbetaNe :
      (QuotientGroup.mk t : conjugateCosetSpace M) ≠ QuotientGroup.mk 1)
    (hYleD : (prop63Residual Z M).map M.subtype ≤
      M ⊓ rightConjugate M t) :
    ¬ MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2 := by
  intro htwo
  let _ := prop63Residual_normal h
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  let Y : Subgroup M := prop63Residual Z M
  let YX : Subgroup X := Y.map M.subtype
  have hYX_M : YX ≤ M := Subgroup.map_subtype_le _
  have hYX_beta : YX ≤ MulAction.stabilizer X beta := by
    rw [show MulAction.stabilizer X beta = rightConjugate M t from by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    exact hYleD.trans inf_le_right
  have hYX_fixes : ∀ omega : conjugateCosetSpace M,
      YX ≤ MulAction.stabilizer X omega := by
    intro omega
    by_cases homega : omega = alpha
    · subst omega
      simpa [alpha, baseCoset_stabilizer] using hYX_M
    · have halphaBeta : alpha ≠ beta := by
        exact hbetaNe.symm
      have htwo' : ∀ {a b c d : conjugateCosetSpace M},
          a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d :=
        MulAction.is_two_pretransitive_iff.mp htwo
      obtain ⟨m, hmAlpha, hmBeta⟩ :=
        htwo' (a := alpha) (b := beta) (c := alpha) (d := omega)
          halphaBeta (fun h => homega h.symm)
      have hmM : m ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact MulAction.mem_stabilizer_iff.mpr hmAlpha
      intro y hyYX
      apply MulAction.mem_stabilizer_iff.mpr
      rcases Subgroup.mem_map.mp hyYX with ⟨yM, hyY, rfl⟩
      let mM : M := ⟨m, hmM⟩
      have hconjY : mM⁻¹ * yM * mM ∈ Y := by
        simpa using
          (inferInstance : Y.Normal).conj_mem yM hyY mM⁻¹
      have hconjFix : ((mM⁻¹ * yM * mM : M) : X) • beta = beta :=
        MulAction.mem_stabilizer_iff.mp
          (hYX_beta (Subgroup.mem_map_of_mem M.subtype hconjY))
      calc
        (yM : X) • omega = (yM : X) • (m • beta) := by rw [hmBeta]
        _ = m • (((mM⁻¹ * yM * mM : M) : X) • beta) := by
          simp [mM, mul_smul]
        _ = m • beta := by rw [hconjFix]
        _ = omega := hmBeta
  have hYXcore : YX ≤ pointStabilizerCore X (conjugateCosetSpace M) :=
    (le_pointStabilizerCore_iff).2 hYX_fixes
  let C : Subgroup X := pointStabilizerCore X (conjugateCosetSpace M)
  have hCnormal : C.Normal :=
    PFchapter1section1.proposition_4_c_pointStabilizerCore_normal
  rcases hX.eq_bot_or_eq_top_of_normal C hCnormal with hCbot | hCtop
  · have hYXbot : YX = ⊥ :=
      eq_bot_iff.mpr (by simpa [C, hCbot] using hYXcore)
    have hYbot : Y = ⊥ := by
      apply Subgroup.map_injective (f := M.subtype) Subtype.val_injective
      simp [YX, hYXbot]
    exact d.prop63_residual_ne_bot h hYbot
  · apply h.proper
    apply top_unique
    have hCleM : C ≤ M := by
      rw [show M = MulAction.stabilizer X alpha by
        simp [alpha]]
      exact (le_pointStabilizerCore_iff.mp le_rfl) alpha
    simpa [C, hCtop] using hCleM

/-- Quotient centralization modulo `Y = O²(M°)` lifts to normalization of
`P Y` for every subgroup `P` of a normalized odd-prime subgroup `R`. -/
public theorem prop63_normalizes_sup_residual
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M P R : Subgroup X} {z : X}
    {q : ℕ} (hq : q.Prime) (hqOdd : Odd q)
    (h : IsProductDisconnected Z M) (hzM : z ∈ M) (hz : z ∈ Z)
    (hRp : IsPGroup q R) (hRM : R ≤ M) (hPR : P ≤ R)
    (hzNormR : z ∈ Subgroup.normalizer (R : Set X)) :
    z ∈ Subgroup.normalizer
      ((P ⊔ (prop63Residual Z M).map M.subtype :
        Subgroup X) : Set X) := by
  let _ := prop63Residual_normal h
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y : Subgroup M := prop63Residual Z M
  let qM : M →* M ⧸ Y := QuotientGroup.mk' Y
  let RM : Subgroup M := R.subgroupOf M
  let PM : Subgroup M := P.subgroupOf M
  let Rbar : Subgroup (M ⧸ Y) := RM.map qM
  let Pbar : Subgroup (M ⧸ Y) := PM.map qM
  have hPM : P ≤ M := hPR.trans hRM
  have hRMp : IsPGroup q RM := by
    exact hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRM).symm
  have hzMNormR : (⟨z, hzM⟩ : M) ∈
      Subgroup.normalizer (RM : Set M) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRM]
    exact hzNormR
  have hzbarNormR : qM ⟨z, hzM⟩ ∈
      Subgroup.normalizer (Rbar : Set (M ⧸ Y)) := by
    apply Subgroup.le_normalizer_map qM
    exact Subgroup.mem_map_of_mem qM hzMNormR
  have hzbarCore : qM ⟨z, hzM⟩ ∈ pCore 2 (M ⧸ Y) := by
    exact prop63_image_mem_twoCore h hzM hz
  have htwoNeQ : 2 ≠ q := by
    intro hqTwo
    subst q
    exact (by decide : ¬ Odd 2) hqOdd
  have hzbarCentralR : qM ⟨z, hzM⟩ ∈
      Subgroup.centralizer (Rbar : Set (M ⧸ Y)) := by
    apply mem_centralizer_of_mem_pCore_of_mem_normalizer htwoNeQ
      hzbarCore
    · exact hRMp.map qM
    · exact hzbarNormR
  have hPMRM : PM ≤ RM := Subgroup.subgroupOf_mono M hPR
  have hPbarRbar : Pbar ≤ Rbar := Subgroup.map_mono hPMRM
  have hzbarCentralP : qM ⟨z, hzM⟩ ∈
      Subgroup.centralizer (Pbar : Set (M ⧸ Y)) :=
    (Subgroup.centralizer_le hPbarRbar) hzbarCentralR
  have hzbarNormP : qM ⟨z, hzM⟩ ∈
      Subgroup.normalizer (Pbar : Set (M ⧸ Y)) :=
    centralizer_le_normalizer Pbar hzbarCentralP
  have hzMNormComap : (⟨z, hzM⟩ : M) ∈
      Subgroup.normalizer ((Pbar.comap qM : Subgroup M) : Set M) := by
    have hzComap : (⟨z, hzM⟩ : M) ∈
        (Subgroup.normalizer (Pbar : Set (M ⧸ Y))).comap qM :=
      hzbarNormP
    rw [Subgroup.comap_normalizer_eq_of_surjective Pbar
      (QuotientGroup.mk'_surjective Y)] at hzComap
    exact hzComap
  have hcomap : Pbar.comap qM = PM ⊔ Y := by
    dsimp [Pbar]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hzMNormSup : (⟨z, hzM⟩ : M) ∈
      Subgroup.normalizer ((PM ⊔ Y : Subgroup M) : Set M) := by
    rw [← hcomap]
    exact hzMNormComap
  have hzNormMap : z ∈ Subgroup.normalizer
      ((((PM ⊔ Y : Subgroup M).map M.subtype) : Subgroup X) : Set X) := by
    apply Subgroup.le_normalizer_map M.subtype
    exact Subgroup.mem_map_of_mem M.subtype hzMNormSup
  simpa [PM, Y, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hPM] using hzNormMap

/-- Theorem 2 supplies a maximal `q`-subgroup fixing at least three points,
together with an involution fixing the base point and normalizing it. -/
public theorem prop63_exists_maximal_pSubgroup
    {X : Type u} [Group X] [Finite X]
    {Z : Set X} (M D : Subgroup X) (beta : conjugateCosetSpace M)
    (q : ℕ) (hq : q.Prime) (hqOdd : Odd q)
    (hDM : D ≤ M) (hDbeta : D ≤ MulAction.stabilizer X beta)
    (hbetaNe : beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (hT2 : ActionTheoremTwo Z M)
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    ∃ (P₀ : Sylow q (twoPrimeCore D)) (R : Subgroup X) (s : X),
      let P : Subgroup X :=
        (((P₀ : Subgroup (twoPrimeCore D)).map
          (twoPrimeCore D).subtype).map D.subtype)
      P ≤ R ∧ IsPGroup q R ∧ R ≤ M ∧
        s ∈ Z ∧
        s ∈ Subgroup.normalizer (R : Set X) ∧
        s • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
          QuotientGroup.mk 1 := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let O : Subgroup D := twoPrimeCore D
  let P₀ : Sylow q O := default
  let PD : Subgroup D := (P₀ : Subgroup O).map O.subtype
  let P : Subgroup X := PD.map D.subtype
  have hPp : IsPGroup q P := by
    exact (P₀.2.map O.subtype).map D.subtype
  have hPD : P ≤ D := by
    exact Subgroup.map_subtype_le PD
  have hPM : P ≤ M := hPD.trans hDM
  have hPbeta : P ≤ MulAction.stabilizer X beta := hPD.trans hDbeta
  have hPbase :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) P :=
    theorem4b_baseCoset_mem_fixedPoints hPM
  have hPbetaFixed :
      beta ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) P := by
    intro x hxP
    exact MulAction.mem_stabilizer_iff.mp (hPbeta hxP)
  let base : theorem4bFixedPoints M P :=
    ⟨QuotientGroup.mk 1, hPbase⟩
  let other : theorem4bFixedPoints M P := ⟨beta, hPbetaFixed⟩
  let f : Bool → theorem4bFixedPoints M P := fun b => cond b other base
  have hf : Function.Injective f := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exfalso
      apply hbetaNe
      simpa [f, base, other] using (congrArg Subtype.val hab).symm
    · exfalso
      apply hbetaNe
      simpa [f, base, other] using congrArg Subtype.val hab
    · rfl
  have hPfixed : 2 ≤ Nat.card (theorem4bFixedPoints M P) := by
    simpa using Nat.card_le_card_of_injective f hf
  let Good : Subgroup X → Prop := fun Q =>
    IsPGroup q Q ∧ Q ≤ M ∧ 2 ≤ Nat.card (theorem4bFixedPoints M Q)
  have hPgood : Good P := ⟨hPp, hPM, hPfixed⟩
  obtain ⟨R, hPR, hRmax⟩ := Finite.exists_le_maximal hPgood
  have hRgood : Good R := hRmax.1
  have hnoTwo : ¬ ∃ Q : Subgroup X,
      IsPGroup q Q ∧ Nat.card (theorem4bFixedPoints M Q) = 2 := by
    intro hexact
    exact hnot2 ((hT2 q hq hqOdd).1 hexact)
  have hRneTwo : Nat.card (theorem4bFixedPoints M R) ≠ 2 := by
    intro hcard
    exact hnoTwo ⟨R, hRgood.1, hcard⟩
  have hRthree : 3 ≤ Nat.card (theorem4bFixedPoints M R) := by
    omega
  have hRbase : R ≤ MulAction.stabilizer X
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    simpa [baseCoset_stabilizer] using hRgood.2.1
  have hRmaxThree : ∀ Q : Subgroup X,
      IsPGroup q Q →
      Q ≤ MulAction.stabilizer X
        (QuotientGroup.mk 1 : conjugateCosetSpace M) →
      3 ≤ Nat.card (theorem4bFixedPoints M Q) →
      R ≤ Q → Q = R := by
    intro Q hQp hQbase hQthree hRQ
    have hQM : Q ≤ M := by
      simpa [baseCoset_stabilizer] using hQbase
    have hQgood : Good Q := ⟨hQp, hQM, by omega⟩
    exact (hRmax.eq_of_le hQgood hRQ).symm
  have hsource := (hT2 q hq hqOdd).2 hnoTwo
    (QuotientGroup.mk 1 : conjugateCosetSpace M) R
    hRgood.1 hRbase hRthree hRmaxThree
  have hRbaseFixed :
      (QuotientGroup.mk 1 : conjugateCosetSpace M) ∈
        fixedPointsOfSubgroup X (conjugateCosetSpace M) R :=
    theorem4b_baseCoset_mem_fixedPoints hRgood.2.1
  obtain ⟨s, hsZ, hsNorm, hsFix⟩ :=
    hsource.2 _ hRbaseFixed
  refine ⟨P₀, R, s, ?_⟩
  change P ≤ R ∧ IsPGroup q R ∧ R ≤ M ∧
    s ∈ Z ∧
    s ∈ Subgroup.normalizer (R : Set X) ∧
    s • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
      QuotientGroup.mk 1
  exact ⟨hPR, hRgood.1, hRgood.2.1, hsZ, hsNorm, hsFix⟩


/-- The local factorization realizes distinguished conjugacy inside the odd core. -/
public theorem prop63_oddCore_conjugator
    (h : IsProductDisconnected Z M) {z s : G} (hz : z ∈ Z) (hzM : z ∈ M)
    (hs : s ∈ Z) (hsM : s ∈ M) (D : Subgroup G)
    (hf : ∀ m ∈ M, ∃ o ∈ corollary64OddCore D,
      ∃ c ∈ elementCentralizerIn M z, m = o * c) :
    ∃ o ∈ corollary64OddCore D, rightConjugateElem s o = z := by
  obtain ⟨m, hm⟩ := productDisconnected_conjugator_mem h hz hzM hs hsM
  obtain ⟨o, ho, c, hc, he⟩ := hf m m.property
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  refine ⟨o, ho, ?_⟩
  rw [← hm, he]
  change o⁻¹ * (o * c * z * (o * c)⁻¹) * o = z
  calc
    _ = c * z * c⁻¹ := by group
    _ = z := by rw [hcz, mul_assoc, mul_inv_cancel, mul_one]

/-- For each odd prime, the non-two-transitive branch produces a Sylow
subgroup of `O₂'(D)` whose product with `Y` is normalized by `z`. -/
public theorem prop63_exists_sylow_normalized
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) {z t : X}
    (hzM : z ∈ M) (hz : z ∈ Z)
    (ht : PFAppendixIII.IsInvolution t) (htM : t ∉ M)
    (hT2 : ActionTheoremTwo Z M)
    (hnot2 : ¬ MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2)
    (hf : ∀ m ∈ M, ∃ o ∈ corollary64OddCore (residualPairStabilizer M t),
      ∃ c ∈ elementCentralizerIn M z, m = o * c)
    (q : ℕ) (hq : q.Prime) (hqOdd : Odd q) :
    let D : Subgroup X := M ⊓ rightConjugate M t
    ∃ P₀ : Sylow q (twoPrimeCore D),
      z ∈ Subgroup.normalizer
        (((((P₀ : Subgroup (twoPrimeCore D)).map
            (twoPrimeCore D).subtype).map D.subtype) ⊔
          (prop63Residual Z M).map M.subtype :
          Subgroup X) : Set X) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let D : Subgroup X := M ⊓ rightConjugate M t
  let beta : conjugateCosetSpace M := QuotientGroup.mk t
  have hDM : D ≤ M := inf_le_left
  have hDbeta : D ≤ MulAction.stabilizer X beta := by
    rw [show MulAction.stabilizer X beta = rightConjugate M t from by
      simpa [beta, ht.inv_eq_self] using conjugateCoset_stabilizer M t]
    exact inf_le_right
  have hbetaNe : beta ≠
      (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
    intro h
    apply htM
    simpa [beta, ht.inv_eq_self] using QuotientGroup.eq.mp h
  obtain ⟨P₀, R, s, hPR, hRp, hRM, hsZ, hsNorm, hsFix⟩ :=
    prop63_exists_maximal_pSubgroup
      M D beta q hq hqOdd hDM hDbeta hbetaNe hT2 hnot2
  have hsM : s ∈ M := by
    rw [← baseCoset_stabilizer M]
    exact MulAction.mem_stabilizer_iff.mpr hsFix
  obtain ⟨d, hdO, hsd⟩ := prop63_oddCore_conjugator h hz hzM hsZ hsM D hf
  have hdD : d ∈ D := (Subgroup.map_subtype_le _) hdO
  let dD : D := ⟨d, hdD⟩
  let O : Subgroup D := twoPrimeCore D
  let φ : MulAut O := MulAut.conjNormal (H := O) dD⁻¹
  have hφsurj : Function.Surjective (φ : O →* O) := by
    exact φ.surjective
  let P₀' : Sylow q O :=
    P₀.mapSurjective (f := (φ : O →* O)) hφsurj
  let P : Subgroup X :=
    (((P₀ : Subgroup O).map O.subtype).map D.subtype)
  let P' : Subgroup X :=
    (((P₀' : Subgroup O).map O.subtype).map D.subtype)
  let R' : Subgroup X := R.conjBy d⁻¹
  have hPconj : P' = P.conjBy d⁻¹ := by
    have hhom :
        (D.subtype.comp O.subtype).comp (φ : O →* O) =
          ((MulAut.conj d⁻¹).toMonoidHom.comp D.subtype).comp
            O.subtype := by
      ext a
      simp [φ, dD]
    change
      (((P₀' : Subgroup O).map O.subtype).map D.subtype) =
        ((((P₀ : Subgroup O).map O.subtype).map D.subtype).conjBy d⁻¹)
    dsimp [P₀', Sylow.mapSurjective]
    rw [Subgroup.map_map, Subgroup.map_map]
    simpa only [Subgroup.conjBy, Subgroup.map_map, MonoidHom.comp_assoc] using
      congrArg (fun f : O →* X => (P₀ : Subgroup O).map f) hhom
  have hPR' : P' ≤ R' := by
    rw [hPconj]
    exact Subgroup.map_mono hPR
  have hRp' : IsPGroup q R' := by
    exact hRp.map (MulAut.conj d⁻¹).toMonoidHom
  have hRM' : R' ≤ M := by
    have hdInvNormM : d⁻¹ ∈ Subgroup.normalizer (M : Set X) :=
      Subgroup.le_normalizer (M.inv_mem hdD.1)
    have hMconj : M.conjBy d⁻¹ = M :=
      section11_conjBy_eq_of_mem_normalizer hdInvNormM
    change R.conjBy d⁻¹ ≤ M
    rw [← hMconj]
    exact Subgroup.map_mono hRM
  have hzNormR' : z ∈ Subgroup.normalizer (R' : Set X) := by
    have hsZpowNorm : Subgroup.zpowers s ≤
        Subgroup.normalizer (R : Set X) :=
      Subgroup.zpowers_le.mpr hsNorm
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        hsZpowNorm d⁻¹
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨s, Subgroup.mem_zpowers s, ?_⟩
    simpa [MulAut.conj_apply, rightConjugateElem] using hsd
  have hzNormSup := prop63_normalizes_sup_residual
    hq hqOdd h hzM hz hRp' hRM' hPR' hzNormR'
  refine ⟨P₀', ?_⟩
  simpa [O, P'] using hzNormSup


end BenderSuzuki.ZD
