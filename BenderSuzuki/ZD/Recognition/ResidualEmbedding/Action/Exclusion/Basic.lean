module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Reduction
public import BenderSuzuki.SE.Section7

/-!
# Elementary reductions for the distinguished Section 7 argument

Saturating a normalized odd-prime subgroup preserves its inverted set, prime,
and distinguished involution. This gives Lemma 6.2 using only the authorized
counting input and maximality with the same prime and involution. Sylow
intersection with the odd core does not require an odd two-point stabilizer.

Source: GLS, Volume 4, Chapter 2, (6C)--(6D), Lemma 6.2 and Section 7.
The saturation proof adapts `SE.Theorem4` while retaining the parameters that
its existential interface forgets. No ambient strong embedding is used.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Saturation with the same distinguished involution and prime. -/
public theorem actionCounterexample_of_normalized_pSubgroup
    (h : IsProductDisconnected Z M)
    {z : G} {p : ℕ} {beta : G ⧸ M} {P : Subgroup G}
    (hzZ : z ∈ Z) (hzM : z ∈ M)
    (hp : Nat.Prime p) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPD : P ≤ M ⊓ MulAction.stabilizer G beta)
    (hbeta : beta ≠ (QuotientGroup.mk 1 : G ⧸ M))
    (hzNormP : z ∈ Subgroup.normalizer (P : Set G))
    (htwo : 2 ≤ theorem4bInvertedCard z P) :
    ∃ e : ActionCounterexample Z M, e.p = p ∧ e.z = z ∧
      theorem4bInvertedCard e.z e.W = theorem4bInvertedCard z P := by
  have hz := h.involutions z hzZ
  let : Fact p.Prime := ⟨hp⟩
  let I : Set G := {x : G | x ∈ P ∧ z * x * z⁻¹ = x⁻¹}
  let W : Subgroup G := Subgroup.closure I
  let A : Subgroup G := Subgroup.zpowers z
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    rw [hn]
    exact hpOdd.pow
  have hWP : W ≤ P := by
    change Subgroup.closure I ≤ P
    rw [Subgroup.closure_le]
    exact fun _ hx => hx.1
  have hA_normP : A ≤ Subgroup.normalizer (P : Set G) := by
    change Subgroup.zpowers z ≤ Subgroup.normalizer (P : Set G)
    rw [Subgroup.zpowers_le]
    exact hzNormP
  have hforward : ∀ x : G, x ∈ W → z * x * z⁻¹ ∈ W := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun q : G => fun _hq => z * q * z⁻¹ ∈ W)
      ?_ ?_ ?_ ?_ hx
    · intro q hq
      rw [hq.2]
      exact W.inv_mem (Subgroup.subset_closure hq)
    · simp
    · intro a b _ha _hb ha hb
      have hab : z * (a * b) * z⁻¹ =
          (z * a * z⁻¹) * (z * b * z⁻¹) := by group
      rw [hab]
      exact W.mul_mem ha hb
    · intro a _ha ha
      have hainv : z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
      rw [hainv]
      exact W.inv_mem ha
  have hzNormW : z ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (z * x * z⁻¹) hx
      have hzz : z * z = 1 := by
        simpa [pow_two] using hz.sq_eq_one
      have hcancel : z * (z * x * z⁻¹) * z⁻¹ = x := by
        rw [hz.inv_eq_self]
        calc
          z * (z * x * z) * z = (z * z) * x * (z * z) := by group
          _ = x := by rw [hzz]; simp
      simpa only [hcancel] using hback
  have hA_normW : A ≤ Subgroup.normalizer (W : Set G) := by
    change Subgroup.zpowers z ≤ Subgroup.normalizer (W : Set G)
    rw [Subgroup.zpowers_le]
    exact hzNormW
  have hcomm : ⁅W, A⁆ = W := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx a ha
      have hconj : a * x⁻¹ * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hA_normW ha) x⁻¹).1 (W.inv_mem hx)
      simpa [commutatorElement_def, mul_assoc] using W.mul_mem hx hconj
    · change Subgroup.closure I ≤ ⁅W, A⁆
      rw [Subgroup.closure_le]
      intro x hx
      have hxW : x ∈ W := Subgroup.subset_closure hx
      have hzA : z ∈ A := Subgroup.mem_zpowers z
      have hx2 : x ^ 2 ∈ ⁅W, A⁆ := by
        have hc := Subgroup.commutator_mem_commutator hxW hzA
        have hcx : ⁅x, z⁆ = x ^ 2 := by
          calc
            ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by
              simp [commutatorElement_def, mul_assoc]
            _ = x * (z * x * z⁻¹)⁻¹ := by group
            _ = x * (x⁻¹)⁻¹ := by rw [hx.2]
            _ = x ^ 2 := by simp [pow_two]
        rwa [hcx] at hc
      have hxOrderDvd : orderOf x ∣ Nat.card P := by
        simpa using orderOf_dvd_natCard (⟨x, hx.1⟩ : P)
      have hxOrderOdd : Odd (orderOf x) := hPodd.of_dvd_nat hxOrderDvd
      have hcop : Nat.Coprime 2 (orderOf x) := by
        simpa using hxOrderOdd.coprime_two_left
      obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 2) hcop
      rw [← hn]
      exact (⁅W, A⁆).pow_mem hx2 n
  have hWsubp : IsPGroup p (W.subgroupOf P) := hPp.to_subgroup _
  have hWmap : (W.subgroupOf P).map P.subtype = W := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWP]
  have hWp : IsPGroup p W := by
    rw [← hWmap]
    exact hWsubp.map P.subtype
  have hInvCard : theorem4bInvertedCard z W = theorem4bInvertedCard z P := by
    let e : {x : G // x ∈ W ∧ z * x * z⁻¹ = x⁻¹} ≃
        {x : G // x ∈ P ∧ z * x * z⁻¹ = x⁻¹} :=
      { toFun := fun x => ⟨x, hWP x.property.1, x.property.2⟩
        invFun := fun x =>
          ⟨x, Subgroup.subset_closure (show (x : G) ∈ I from x.property),
            x.property.2⟩
        left_inv := fun x => by apply Subtype.ext; rfl
        right_inv := fun x => by apply Subtype.ext; rfl }
    simpa [theorem4bInvertedCard] using Nat.card_congr e
  have hWne : W ≠ ⊥ := by
    intro hWbot
    have htwoW : 2 ≤ theorem4bInvertedCard z W := by
      rw [hInvCard]
      exact htwo
    have hcardOne : theorem4bInvertedCard z W = 1 := by
      rw [theorem4bInvertedCard, hWbot]
      apply Nat.card_eq_one_iff_exists.mpr
      refine ⟨⟨1, by simp⟩, ?_⟩
      intro x
      apply Subtype.ext
      simpa using x.property.1
    omega
  have hWM : W ≤ M := hWP.trans (hPD.trans inf_le_left)
  have hWbeta : W ≤ MulAction.stabilizer G beta :=
    hWP.trans (hPD.trans inf_le_right)
  let e : ActionCounterexample Z M :=
    { p := p, hp := hp, hpOdd := hpOdd, z := z, W := W,
      hz := hz, hzM := hzM, hWp := hWp, hWM := hWM, hzNorm := hzNormW,
      hcomm := by simpa [A] using hcomm
      hWne := hWne
      hfixed := action_two_le_fixedPoints hWM hWbeta hbeta
      hzZ := hzZ }
  exact ⟨e, rfl, rfl, hInvCard⟩

/-- Nontriviality of the saturated commutator gives at least two inverted
 elements, including the identity. -/
public theorem ActionCounterexample.two_le_invertedCard
    (d : ActionCounterexample Z M) :
    2 ≤ theorem4bInvertedCard d.z d.W := by
  have hset : d.toTheorem4bSixA.invertedSet =
      {x : G | x ∈ d.W ∧ d.z * x * d.z⁻¹ = x⁻¹} :=
    Set.ext (fun x => d.toTheorem4bSixA.mem_invertedSet_iff x)
  have ht := d.toTheorem4bSixA.two_le_card_invertedSet
  rw [hset] at ht
  exact ht

/-- Distinguished Lemma 6.2. Maximality is used only with the same `p` and `z`. -/
public theorem ActionMaximalCounterexample.invariant_sylow_iff
    (d : ActionMaximalCounterexample Z M)
    (h : IsProductDisconnected Z M) (hc : ActionCounting Z M)
    {beta : G ⧸ M}
    (hbeta : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) :
    (∃ Q : Subgroup G,
      theorem4bIsSylowSubgroupOf d.data.p Q (theorem4bSection7D M beta) ∧
      d.data.z ∈ Subgroup.normalizer (Q : Set G)) ↔
    theorem4bInvertedCard d.data.z d.data.W =
      theorem4bPrimeShare M d.data.z d.data.p := by
  have hWD : d.data.W ≤ M ⊓ MulAction.stabilizer G beta :=
    le_inf d.data.hWM (d.data.toTheorem4bSixA.kFixedPoints_subset_fixedPoints hbeta)
  have hi := hc.invariant_sylow d.data.z d.data.hzZ d.data.hzM
    d.data.p d.data.hp d.data.hpOdd beta hne
  constructor
  · intro hs
    obtain ⟨P, hPp, hPD, hzP, hcard⟩ := hi.mp hs
    have htwo : 2 ≤ theorem4bInvertedCard d.data.z P := by
      rw [hcard]
      exact d.data.two_le_invertedCard.trans (hc.bound d.data)
    obtain ⟨e, hep, hez, hecard⟩ := actionCounterexample_of_normalized_pSubgroup
      h d.data.hzZ d.data.hzM d.data.hp d.data.hpOdd hPp hPD hne hzP htwo
    apply le_antisymm (hc.bound d.data)
    calc
      theorem4bPrimeShare M d.data.z d.data.p =
          theorem4bInvertedCard e.z e.W := hcard.symm.trans hecard.symm
      _ ≤ theorem4bInvertedCard d.data.z d.data.W := d.maximal e hep hez
  · intro heq
    exact hi.mpr ⟨d.data.W, d.data.hWp, hWD, d.data.hzNorm, heq⟩

/-- A Sylow subgroup contains a Sylow subgroup of the odd core. The ambient
 subgroup `D` can have even order. -/
public theorem action_sylow_contains_oddCore
    {p : ℕ} (hp : p.Prime) {D R : Subgroup G}
    (hs : theorem4bIsSylowSubgroupOf p R D) :
    ∃ P₀ : Sylow p (twoPrimeCore D),
      (((P₀ : Subgroup (twoPrimeCore D)).map (twoPrimeCore D).subtype).map
        D.subtype) ≤ R := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hs
  let P₀ := External.hallSylowSubgroupOfNormal S (twoPrimeCore D)
  refine ⟨P₀, ?_⟩
  rw [hS]
  apply Subgroup.map_mono
  rw [Subgroup.map_le_iff_le_comap]
  rw [External.hallSylowSubgroupOfNormal_coe]

/-- The commutator-saturated witness lies in the triple stabilizer. No
 oddness of that stabilizer is asserted. -/
public theorem ActionCounterexample.le_triple_stabilizer
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hbeta : beta ∈ d.toTheorem4bSixA.kFixedPoints) :
    d.W ≤ theorem4bSection7E M d.z beta := by
  exact theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer d.hzNorm
    (le_inf d.hWM (d.toTheorem4bSixA.kFixedPoints_subset_fixedPoints hbeta))

/-- The action commutator of the triple stabilizer contains the nontrivial
 `p`-group `W`, as needed at the start of the second stage. -/
public theorem ActionCounterexample.le_triple_commutator
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hbeta : beta ∈ d.toTheorem4bSixA.kFixedPoints) :
    d.W ≤ ⁅theorem4bSection7E M d.z beta, Subgroup.zpowers d.z⁆ := by
  rw [← d.hcomm]
  exact Subgroup.commutator_mono (d.le_triple_stabilizer hbeta) le_rfl

/-- Distinguished Lemma 7.5 from the pair-centralizer containment in
Proposition 7.4(c). Coprime action is on the odd theta core, not on the
possibly even pair stabilizer. This adapts `SE.Section7`. -/
public theorem action_lemma75
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M)
    {beta : G ⧸ M} (hbetaK : beta ∈ d.toTheorem4bSixA.kFixedPoints)
    (hCFW : subgroupCentralizerIn (theorem4bSection7F d.z beta) d.W ≤ M) :
    corollary64Theta d.p (theorem4bSection7F d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7E M d.z beta) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let F : Subgroup G := theorem4bSection7F d.z beta
  let E : Subgroup G := theorem4bSection7E M d.z beta
  let O : Subgroup G := corollary64OddCore F
  let T : Subgroup G := corollary64Theta d.p F
  have hWbeta : d.W <= MulAction.stabilizer G beta := by
    have hfix := d.toTheorem4bSixA.kFixedPoints_subset_fixedPoints hbetaK
    intro w hw
    exact MulAction.mem_stabilizer_iff.mpr (hfix w hw)
  have hWzbeta : d.W <= MulAction.stabilizer G (d.z • beta) :=
    theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      d.hzNorm hWbeta
  have hWF : d.W <= F := le_inf hWbeta hWzbeta
  have hWE : d.W <= E :=
    le_inf (le_inf d.hWM hWbeta) hWzbeta
  have hEF : E <= F :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hOF : O <= F := by
    simpa [O, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore F))
  have hTO : T <= O := by
    simpa [T, O, corollary64Theta] using
      (Subgroup.map_subtype_le (pPrimeCore d.p O))
  have hTF : T <= F := hTO.trans hOF
  have : (twoPrimeCore F).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := F))
  have hNormFNormO : Subgroup.normalizer (F : Set G) <=
      Subgroup.normalizer (O : Set G) := by
    simpa [O, corollary64OddCore] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := F) (K := twoPrimeCore F))
  have hNormONormT : Subgroup.normalizer (O : Set G) <=
      Subgroup.normalizer (T : Set G) := by
    simpa [T, corollary64Theta] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := O) (K := pPrimeCore d.p O))
  have hFNormT : F <= Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer.trans (hNormFNormO.trans hNormONormT)
  have hWT : d.W <= Subgroup.normalizer (T : Set G) :=
    hWF.trans hFNormT
  have hzT : d.z ∈ Subgroup.normalizer (T : Set G) := by
    simpa [T, F] using theorem4b_mem_normalizer_section7ThetaF
      d.hz d.p beta
  have hgen : Lemma75II146Conclusion T d.W d.z := by
    apply lemma75_II146_specialized d.hz d.hzNorm hWT hzT d.hcomm
    · simpa [T, F] using lemma75_theta_odd_card d.p F
    · simpa [T, F] using
        lemma75_theta_actor_card_coprime d.hp d.hWp d.hz d.hzNorm F
  have hCTW : subgroupCentralizerIn T d.W <= E := by
    intro x hx
    have hxF : x ∈ F := hTF hx.1
    have hxM : x ∈ M := hCFW ⟨by simpa [F] using hxF, hx.2⟩
    exact ⟨⟨hxM, hxF.1⟩, hxF.2⟩
  have hCTz : elementCentralizerIn T d.z <= E := by
    intro x hx
    have hxF : x ∈ F := hTF hx.1
    have hxM : x ∈ M := h.centralizer_le d.hzZ d.hzM hx.2
    exact ⟨⟨hxM, hxF.1⟩, hxF.2⟩
  have hTE : T <= E :=
    lemma75_le_of_II146Conclusion hgen hCTW hCTz hWE
  exact theorem4b_lemma75_theta_le_theta_of_le
    (p := d.p) (E := E) (F := F) hEF (by simpa [T] using hTE)

/-- The first clause of Corollary 6.4 from the actual odd-core generation
statement. The source generation theorem must still be proved. -/
public theorem action_theta_eq_bot_of_generation
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {p : ℕ} {z t : G} (ht : IsInvolution t)
    (hgen : residualGenerated M z t = ⊤)
    (hzNorm : z ∈ Subgroup.normalizer
      (corollary64Theta p (residualPairStabilizer M t) : Set G)) :
    corollary64Theta p (residualPairStabilizer M t) = ⊥ := by
  let D := residualPairStabilizer M t
  let O := corollary64OddCore D
  let T := corollary64Theta p D
  have : (twoPrimeCore D).Characteristic := by
    simpa [twoPrimeCore] using (pPrimeCore_characteristic (p := 2) (G := D))
  have hNO : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (O : Set G) := by
    exact section8_normalizer_map_subtype_le_of_characteristic
      (H := D) (K := twoPrimeCore D)
  have hNT : Subgroup.normalizer (O : Set G) ≤ Subgroup.normalizer (T : Set G) := by
    exact section8_normalizer_map_subtype_le_of_characteristic
      (H := O) (K := pPrimeCore p O)
  have htN : t ∈ Subgroup.normalizer (T : Set G) :=
    hNT (hNO (inf_rightConjugate_mem_normalizer_of_isInvolution M ht))
  have hDN : D ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.le_normalizer.trans (hNO.trans hNT)
  have hON : O ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.map_subtype_le _).trans hDN
  have hcomm : ⁅O, Subgroup.zpowers t⁆ ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.commutator_le.mpr (by
      intro x hx y hy
      let N := Subgroup.normalizer (T : Set G)
      have hxN : x ∈ N := hON hx
      have hyN : y ∈ N := (Subgroup.zpowers_le.mpr htN) hy
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hxN hyN) (N.inv_mem hxN)) (N.inv_mem hyN))
  have hgenN : residualGenerated M z t ≤ Subgroup.normalizer (T : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr hzNorm)
      (Subgroup.zpowers_le.mpr htN)) hcomm
  have hnormal : T.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ hgenN))
  rcases r.simple.eq_bot_or_eq_top_of_normal T hnormal with hbot | htop
  · exact hbot
  · have hTM : T ≤ M :=
      (Subgroup.map_subtype_le _).trans ((Subgroup.map_subtype_le _).trans inf_le_left)
    exact False.elim (h.proper (top_unique (htop ▸ hTM)))

end BenderSuzuki.ZD
