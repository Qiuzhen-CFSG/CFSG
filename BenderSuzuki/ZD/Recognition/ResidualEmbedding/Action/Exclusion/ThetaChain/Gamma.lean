module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Interfaces
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Gamma.Factorization
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.ThetaChain.Gamma.NormalizingSwap
import BenderSuzuki.SE.Lemma311

/-!
# Both branches of the distinguished Gamma construction

When C_G(K) ≤ M, use all K-fixed cosets. Section 3 extends W to a z-invariant
Sylow subgroup of the triple stabilizer, without assuming that stabilizer
has odd order. A distinguished normalizing swap from Lemma 7.3 then supplies
the required conjugation and centralizer containments.

Otherwise Lemma 3.11 constructs an odd prime orbit inside the H-orbit of
the base point, where H = C_G(K)⟨z⟩. Its odd subgroup is inverted by z.
Square roots in that subgroup express each swapping reflection as a
conjugate of z, proving membership in Z. Normalization of K supplies the
remaining clauses of Proposition 7.4.

The final minimal-counterexample theorem discharges the normalizing-swap
and operational Z-star factorization premises using `Gamma.NormalizingSwap`
and `Gamma.Factorization`. Only the Section 3 and counting inputs from the
surrounding action argument remain explicit.

Source: GLS, Volume 4, Chapter 2, Lemma 3.11 and Proposition 7.4.
The orbit transport and coset calculations adapt `SE.Section7Proposition74`.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u

private abbrev gammaBase
    {X : Type u} [Group X] [Finite X] {M : Subgroup X} :
    conjugateCosetSpace M :=
  QuotientGroup.mk 1

private def gammaPairCentralizer
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (K : Set X) (beta gamma : conjugateCosetSpace M) : Subgroup X :=
  (Subgroup.centralizer K ⊓ MulAction.stabilizer X beta) ⊓
    MulAction.stabilizer X gamma

private theorem rightConjugateSet_comp_section7
    {G : Type*} [Group G] (K : Set G) (a b : G) :
    rightConjugateSet (rightConjugateSet K a) b =
      rightConjugateSet K (a * b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by simp [rightConjugateElem, mul_assoc]⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨rightConjugateElem k a, ⟨k, hk, rfl⟩, ?_⟩
    simp [rightConjugateElem, mul_assoc]

private theorem actionGamma_invertedSet_conjugate_z
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (d : Theorem4bSixA M) :
    rightConjugateSet d.invertedSet d.z = d.invertedSet := by
  have hconj_mem : ∀ {x : X}, x ∈ d.invertedSet →
      rightConjugateElem x d.z ∈ d.invertedSet := by
    intro x hx
    have hx' := (d.mem_invertedSet_iff x).mp hx
    have hxeq : rightConjugateElem x d.z = x⁻¹ := by
      simpa [rightConjugateElem, d.hz.inv_eq_self] using hx'.2
    apply (d.mem_invertedSet_iff _).mpr
    constructor
    · rw [hxeq]
      exact d.W.inv_mem hx'.1
    · rw [hxeq]
      calc
        d.z * x⁻¹ * d.z⁻¹ = (d.z * x * d.z⁻¹)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [hx'.2]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hconj_mem hx
  · intro hy
    refine ⟨rightConjugateElem y d.z, hconj_mem hy, ?_⟩
    exact (rightConjugateElem_rightConjugateElem d.hz.inv_eq_self).symm

private theorem centralizer_rightConjugateSet_le_stabilizer_section7
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {K : Set G} {u : G} {alpha : Omega}
    (hu : IsInvolution u)
    (hC : Subgroup.centralizer K ≤ MulAction.stabilizer G alpha) :
    Subgroup.centralizer (rightConjugateSet K u) ≤
      MulAction.stabilizer G (u • alpha) := by
  intro c hc
  apply MulAction.mem_stabilizer_iff.mpr
  have huu : u * u = 1 := by simpa [pow_two] using hu.sq_eq_one
  let c0 : G := rightConjugateElem c u
  have hc0 : c0 ∈ Subgroup.centralizer K := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let ku : G := rightConjugateElem k u
    have hku : ku ∈ rightConjugateSet K u := ⟨k, hk, rfl⟩
    have hcomm : ku * c = c * ku :=
      (Subgroup.mem_centralizer_iff.mp hc) ku hku
    calc
      k * c0 = rightConjugateElem ku u * rightConjugateElem c u := by
        rw [rightConjugateElem_rightConjugateElem hu.inv_eq_self]
      _ = rightConjugateElem (ku * c) u := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (c * ku) u := by rw [hcomm]
      _ = rightConjugateElem c u * rightConjugateElem ku u := by
        simp [rightConjugateElem, mul_assoc]
      _ = c0 * k := by
        rw [rightConjugateElem_rightConjugateElem hu.inv_eq_self]
  have hc0fix : c0 • alpha = alpha :=
    MulAction.mem_stabilizer_iff.mp (hC hc0)
  have hcu : c * u = u * c0 := by
    have hc0eq : c0 = u * c * u := by
      simp [c0, rightConjugateElem, hu.inv_eq_self]
    rw [hc0eq]
    calc
      c * u = 1 * (c * u) := by simp
      _ = (u * u) * (c * u) := by rw [huu]
      _ = u * (u * c * u) := by group
  calc
    c • (u • alpha) = (c * u) • alpha := by rw [smul_smul]
    _ = (u * c0) • alpha := by rw [hcu]
    _ = u • (c0 • alpha) := by rw [smul_smul]
    _ = u • alpha := by rw [hc0fix]

private theorem mem_normalizer_of_rightConjugateSet_eq_self_of_involution_section7
    {X : Type u} [Group X] (K : Set X) {z : X}
    (hz : IsInvolution z)
    (hK : rightConjugateSet K z = K) :
    z ∈ Subgroup.normalizer K := by
  change ∀ n : X, n ∈ K ↔ z * n * z⁻¹ ∈ K
  have hforward : ∀ {n : X}, n ∈ K → z * n * z⁻¹ ∈ K := by
    intro n hn
    have hright : rightConjugateElem n z ∈ rightConjugateSet K z :=
      ⟨n, hn, rfl⟩
    rw [hK] at hright
    simpa [rightConjugateElem, hz.inv_eq_self] using hright
  intro n
  constructor
  · exact hforward
  · intro hn
    have hback := hforward hn
    have hsq : z * z = 1 := by
      simpa [pow_two] using hz.sq_eq_one
    have heq : z * (z * n * z⁻¹) * z⁻¹ = n := by
      rw [hz.inv_eq_self]
      calc
        z * (z * n * z) * z = (z * z) * n * (z * z) := by group
        _ = n := by rw [hsq]; simp
    rw [heq] at hback
    exact hback

private theorem rightConjugateSet_eq_self_of_mem_normalizer_section7
    {X : Type u} [Group X] (K : Set X) {u : X}
    (hu : u ∈ Subgroup.normalizer K) :
    rightConjugateSet K u = K := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hui : u⁻¹ ∈ Subgroup.normalizer K :=
      (Subgroup.normalizer K).inv_mem hu
    change u⁻¹ * k * u ∈ K
    change ∀ n : X, n ∈ K ↔ u⁻¹ * n * (u⁻¹)⁻¹ ∈ K at hui
    simpa [mul_assoc] using (hui k).mp hk
  · intro hy
    have hforward : u * y * u⁻¹ ∈ K := by
      change ∀ n : X, n ∈ K ↔ u * n * u⁻¹ ∈ K at hu
      exact (hu y).mp hy
    refine ⟨u * y * u⁻¹, hforward, ?_⟩
    simp [rightConjugateElem, mul_assoc]


private theorem distinguished_reflection_of_odd_inverted
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) {z : G} (hz : z ∈ Z)
    (R : Subgroup G) (hRodd : Odd (Nat.card R))
    (hinv : ∀ q : G, q ∈ R → z * q * z⁻¹ = q⁻¹)
    {a : G} (ha : a ∈ R) : a * z ∈ Z := by
  have haodd : Odd (orderOf a) := hRodd.of_dvd_nat (by
    simpa using orderOf_dvd_natCard (⟨a, ha⟩ : R))
  have hcop : Nat.Coprime 2 (orderOf a) := by
    simpa using haodd.coprime_two_left
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := a) (n := 2) hcop
  let q : G := a ^ n
  have hqR : q ∈ R := R.pow_mem ha n
  have hq2 : q ^ 2 = a := by
    dsimp [q]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact hn
  have hzq : z * q⁻¹ = q * z := by
    have hh := hinv q⁻¹ (R.inv_mem hqR)
    simpa [mul_assoc] using congrArg (fun x : G => x * z) hh
  have heq : MulAut.conj q z = a * z := by
    change q * z * q⁻¹ = a * z
    calc
      q * z * q⁻¹ = q * (z * q⁻¹) := by group
      _ = q * (q * z) := by rw [hzq]
      _ = q ^ 2 * z := by rw [pow_two]; group
      _ = a * z := by rw [hq2]
  exact heq ▸ h.invariant q z hz

private theorem action_orbit_of_factorization
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M)
    (hCnot : ¬ Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M)
    (hfactor :
      let H := Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔ Subgroup.zpowers d.z
      let zH : H := ⟨d.z, (show Subgroup.zpowers d.z ≤ H from le_sup_right) (Subgroup.mem_zpowers d.z)⟩
      pPrimeCore 2 H ⊔ Subgroup.centralizer ({zH} : Set H) = ⊤) :
    let H := Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔ Subgroup.zpowers d.z
    ∃ R : Subgroup X, ∃ Gamma : Set (conjugateCosetSpace M),
    R ≤ H ∧
    Gamma = MulAction.orbit R gammaBase ∧
    (∃ r : ℕ, Nat.Prime r ∧ Odd r ∧ IsPGroup r R ∧
      Nat.card Gamma = r) ∧
    d.toTheorem4bSixA.z ∈ Subgroup.normalizer (R : Set X) ∧
    (∀ beta, beta ∈ Gamma → d.toTheorem4bSixA.z • beta ∈ Gamma) ∧
    (∀ {beta gamma}, beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
      ∀ x, x ∈ H → x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta) ∧
    (∀ beta, beta ∈ Gamma → beta ≠ gammaBase →
      ∃ t, t ∈ Z ∧ t ∈ H ∧
        t • gammaBase = beta ∧
        t • beta = gammaBase) := by
  classical
  let K : Set X := d.toTheorem4bSixA.invertedSet
  let C : Subgroup X := Subgroup.centralizer K
  let H : Subgroup X := C ⊔ Subgroup.zpowers d.toTheorem4bSixA.z
  let alpha : conjugateCosetSpace M := gammaBase
  let OmegaH := MulAction.orbit H alpha
  let alphaH : OmegaH := ⟨alpha, MulAction.mem_orbit_self alpha⟩
  have hzHmem : d.toTheorem4bSixA.z ∈ H :=
    (show Subgroup.zpowers d.toTheorem4bSixA.z ≤ H from le_sup_right)
      (Subgroup.mem_zpowers d.toTheorem4bSixA.z)
  let zH : H := ⟨d.toTheorem4bSixA.z, hzHmem⟩
  let YH : Subgroup H := M.comap H.subtype
  let : MulAction H OmegaH := inferInstance
  let : MulAction.IsPretransitive H OmegaH := inferInstance
  have hYstab : MulAction.stabilizer H alphaH = YH := by
    ext h
    constructor
    · intro hh
      change (h : X) ∈ M
      have hfix : h • alphaH = alphaH :=
        MulAction.mem_stabilizer_iff.mp hh
      have hfixX : (h : X) • alpha = alpha := congrArg Subtype.val hfix
      rw [← baseCoset_stabilizer M]
      exact MulAction.mem_stabilizer_iff.mpr hfixX
    · intro hh
      apply MulAction.mem_stabilizer_iff.mpr
      apply Subtype.ext
      have hmem : (h : X) ∈ MulAction.stabilizer X alpha := by
        dsimp [alpha]
        rw [baseCoset_stabilizer]
        exact hh
      exact MulAction.mem_stabilizer_iff.mp hmem
  have hYproper : YH ≠ ⊤ := by
    intro htop
    apply hCnot
    intro c hc
    have hcH : c ∈ H := (show C ≤ H from le_sup_left) hc
    let cH : H := ⟨c, hcH⟩
    have hcY : cH ∈ YH := by
      rw [htop]
      trivial
    exact hcY
  have hzY : zH ∈ YH := d.toTheorem4bSixA.hzM
  have hzHI : IsInvolution zH := IsInvolution.subtype d.toTheorem4bSixA.hz hzHmem
  have hcentH : Subgroup.centralizer ({zH} : Set H) ≤ YH := by
    intro c hc
    change (c : X) ∈ M
    apply h.centralizer_le d.hzZ d.hzM
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hfactorH : pPrimeCore 2 H ⊔
      Subgroup.centralizer ({zH} : Set H) = ⊤ := by
    simpa [K, C, H, zH] using
      hfactor
  have hrec :=
    lemma_3_11 YH zH alphaH hYstab hYproper hzY hzHI
      hcentH hfactorH
  rcases hrec with
    ⟨RH, GammaH, hGammaH, hPrimeH, _hcyclicH, hinvH,
      hzNormH, hzGammaH, hPointH, _hSwapH⟩
  obtain ⟨r, hrPrime, hrOdd, hRpH, hGammaHCard⟩ := hPrimeH
  let R : Subgroup X := RH.map H.subtype
  let Gamma : Set (conjugateCosetSpace M) :=
    (fun w : OmegaH => (w : conjugateCosetSpace M)) '' GammaH
  have hRleH : R ≤ H := by
    dsimp [R]
    exact Subgroup.map_subtype_le RH
  have hGammaCard : Nat.card Gamma = Nat.card GammaH := by
    calc
      Nat.card Gamma = Gamma.ncard := Nat.card_coe_set_eq Gamma
      _ = GammaH.ncard :=
        Set.ncard_image_of_injective _ Subtype.val_injective
      _ = Nat.card GammaH := (Nat.card_coe_set_eq GammaH).symm
  have hGammaOrbit : Gamma = MulAction.orbit R alpha := by
    ext beta
    constructor
    · rintro ⟨betaH, hbetaH, rfl⟩
      rw [hGammaH] at hbetaH
      rcases MulAction.mem_orbit_iff.mp hbetaH with ⟨qH, hqH⟩
      let q : R := ⟨(qH : X), ⟨qH, qH.property, rfl⟩⟩
      refine MulAction.mem_orbit_iff.mpr ⟨q, ?_⟩
      exact congrArg Subtype.val hqH
    · intro hbeta
      rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
      rcases Subgroup.mem_map.mp q.property with ⟨qH, hqHR, hqEq⟩
      have hqEqX : (q : X) = (qH : X) := by simpa using hqEq.symm
      have hqHX : (qH : X) • alpha = beta := by
        have hqX : (q : X) • alpha = beta := hq
        rwa [hqEqX] at hqX
      have hbetaOrbitH : beta ∈ MulAction.orbit H alpha := by
        rw [MulAction.mem_orbit_iff]
        exact ⟨qH, hqHX⟩
      let betaH : OmegaH := ⟨beta, hbetaOrbitH⟩
      have hbetaH : betaH ∈ GammaH := by
        rw [hGammaH]
        let qRH : RH := ⟨qH, hqHR⟩
        exact MulAction.mem_orbit_iff.mpr ⟨qRH, by
          apply Subtype.ext
          exact hqHX⟩
      exact ⟨betaH, hbetaH, rfl⟩
  have hRp : IsPGroup r R := by
    simpa [R] using hRpH.map H.subtype
  have hzNormR : d.toTheorem4bSixA.z ∈ Subgroup.normalizer (R : Set X) := by
    have hzMap : d.toTheorem4bSixA.z ∈
        (Subgroup.normalizer (RH : Set H)).map H.subtype :=
      Subgroup.mem_map_of_mem H.subtype hzNormH
    exact (Subgroup.le_normalizer_map (H := RH) H.subtype) hzMap
  have hzGamma : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma → d.toTheorem4bSixA.z • beta ∈ Gamma := by
    intro beta hbeta
    rcases hbeta with ⟨betaH, hbetaH, rfl⟩
    have hzbetaH : zH • betaH ∈ GammaH := hzGammaH betaH hbetaH
    exact ⟨zH • betaH, hzbetaH, rfl⟩
  have hPoint : ∀ {beta gamma : conjugateCosetSpace M},
      beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
      ∀ x : X, x ∈ H → x • beta = beta → x • gamma = gamma →
        ∀ delta, delta ∈ Gamma → x • delta = delta := by
    intro beta gamma hbeta hgamma hne x hxH hxbeta hxgamma delta hdelta
    rcases hbeta with ⟨betaH, hbetaH, rfl⟩
    rcases hgamma with ⟨gammaH, hgammaH, rfl⟩
    rcases hdelta with ⟨deltaH, hdeltaH, rfl⟩
    let xH : H := ⟨x, hxH⟩
    have hxbetaH : xH • betaH = betaH := by
      apply Subtype.ext
      exact hxbeta
    have hxgammaH : xH • gammaH = gammaH := by
      apply Subtype.ext
      exact hxgamma
    have hneH : betaH ≠ gammaH := by
      intro heq
      exact hne (congrArg Subtype.val heq)
    exact congrArg Subtype.val
      (hPointH hbetaH hgammaH hneH xH hxbetaH hxgammaH deltaH hdeltaH)
  have hRodd : Odd (Nat.card R) := by
    let : Fact r.Prime := ⟨hrPrime⟩
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact hrOdd.pow
  have hinv : ∀ q : X, q ∈ R → d.z * q * d.z⁻¹ = q⁻¹ := by
    intro q hq
    obtain ⟨qH, hqH, rfl⟩ := Subgroup.mem_map.mp hq
    exact congrArg Subtype.val (hinvH qH hqH)
  have hzAlpha : d.z • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact d.hzM
  have hSwap : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma → beta ≠ alpha →
      ∃ t : X, t ∈ Z ∧ t ∈ H ∧
        t • alpha = beta ∧ t • beta = alpha := by
    intro beta hbeta _hne
    rw [hGammaOrbit] at hbeta
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hbeta
    let t : X := (a : X) * d.z
    have htZ : t ∈ Z :=
      distinguished_reflection_of_odd_inverted h d.hzZ R hRodd hinv a.property
    have htAlpha : t • alpha = beta := by
      change ((a : X) * d.z) • alpha = beta
      rw [mul_smul, hzAlpha]
      exact ha
    have ht := h.involutions t htZ
    refine ⟨t, htZ, H.mul_mem (hRleH a.property) hzHmem, htAlpha, ?_⟩
    rw [← htAlpha, ← mul_smul, show t * t = 1 by simpa [pow_two] using ht.sq_eq_one,
      one_smul]
  have hGammaCard' : Nat.card Gamma = r := by
    rw [hGammaCard]
    exact hGammaHCard
  refine ⟨R, Gamma, ?_, ?_,
    ⟨r, hrPrime, hrOdd, hRp, hGammaCard'⟩,
    hzNormR, hzGamma, hPoint, ?_⟩
  · simpa [H, C, K] using hRleH
  · simpa [alpha] using hGammaOrbit
  · simpa [alpha] using hSwap


/-- Second branch of Proposition 7.4 from the operational local Z-star
factorization. The swapping involutions are proved to lie in Z. -/
public theorem actionGamma_of_centralizer_factorization
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) (d : ActionCounterexample Z M)
    (hCnot : ¬ Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M)
    (hfactor :
      let H := Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔ Subgroup.zpowers d.z
      let zH : H := ⟨d.z, (show Subgroup.zpowers d.z ≤ H from le_sup_right) (Subgroup.mem_zpowers d.z)⟩
      pPrimeCore 2 H ⊔ Subgroup.centralizer ({zH} : Set H) = ⊤) :
    ActionGamma d := by
  let K : Set X := d.toTheorem4bSixA.invertedSet
  let C : Subgroup X := Subgroup.centralizer K
  let H : Subgroup X := C ⊔ Subgroup.zpowers d.toTheorem4bSixA.z
  have h311H := action_orbit_of_factorization h d hCnot hfactor
  rcases h311H with
    ⟨R, Gamma, hRH, hGammaOrbit, hGammaPrime, hzR, hzGammaForward,
      hPointwise, hSwap⟩
  obtain ⟨r, hrPrime, hrOdd, hrPGroup, hGammaCard⟩ := hGammaPrime
  have hCnorm : C ≤ Subgroup.normalizer K := by
    have hforward : ∀ {a n : X}, a ∈ C → n ∈ K →
        a * n * a⁻¹ ∈ K := by
      intro a n ha hn
      have hcomm : n * a = a * n :=
        (Subgroup.mem_centralizer_iff.mp ha) n hn
      have heq : a * n * a⁻¹ = n := by
        rw [← hcomm]
        simp
      rw [heq]
      exact hn
    intro a ha
    change ∀ n : X, n ∈ K ↔ a * n * a⁻¹ ∈ K
    intro n
    constructor
    · exact hforward ha
    · intro hn
      have hback := hforward (C.inv_mem ha) hn
      have heq : a⁻¹ * (a * n * a⁻¹) * (a⁻¹)⁻¹ = n := by
        group
      rw [heq] at hback
      exact hback
  have hKz : rightConjugateSet K d.toTheorem4bSixA.z = K := by
    simpa [K] using actionGamma_invertedSet_conjugate_z d.toTheorem4bSixA
  have hzNormK : d.toTheorem4bSixA.z ∈ Subgroup.normalizer K := by
    exact mem_normalizer_of_rightConjugateSet_eq_self_of_involution_section7
      K d.toTheorem4bSixA.hz hKz
  have hHNorm : H ≤ Subgroup.normalizer K := by
    apply sup_le hCnorm
    rw [Subgroup.zpowers_le]
    exact hzNormK
  have hCH : C ≤ H := le_sup_left
  have hzH : d.toTheorem4bSixA.z ∈ H := by
    exact (show Subgroup.zpowers d.toTheorem4bSixA.z ≤ H from le_sup_right)
      (Subgroup.mem_zpowers d.toTheorem4bSixA.z)
  have hbase : gammaBase (X := X) (M := M) ∈ Gamma := by
    rw [hGammaOrbit]
    exact MulAction.mem_orbit_self _
  have hcard : 1 < Nat.card Gamma := by
    rw [hGammaCard]
    exact hrPrime.one_lt
  have hGammaK : Gamma ⊆ d.toTheorem4bSixA.kFixedPoints := by
    intro beta hbeta
    rw [hGammaOrbit] at hbeta
    rcases MulAction.mem_orbit_iff.mp hbeta with ⟨q, hq⟩
    apply (d.toTheorem4bSixA.mem_kFixedPoints_iff beta).mpr
    intro k hk
    have hqNorm : (q : X) ∈ Subgroup.normalizer K :=
      hHNorm (hRH q.property)
    have hqInvNorm : (q : X)⁻¹ ∈ Subgroup.normalizer K :=
      (Subgroup.normalizer K).inv_mem hqNorm
    change ∀ n : X, n ∈ K ↔
      (q : X)⁻¹ * n * ((q : X)⁻¹)⁻¹ ∈ K at hqInvNorm
    have hkq : (q : X)⁻¹ * k * (q : X) ∈ K := by
      simpa using (hqInvNorm k).mp hk
    have hKbase : ∀ {a : X}, a ∈ K →
        a • gammaBase (X := X) (M := M) =
          gammaBase (X := X) (M := M) := by
      intro a ha
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer]
      exact d.toTheorem4bSixA.hWM ((d.toTheorem4bSixA.mem_invertedSet_iff a).mp ha).1
    have hqX : (q : X) • gammaBase = beta := hq
    calc
      k • beta = k • ((q : X) • gammaBase) := by rw [hqX]
      _ = (k * (q : X)) • gammaBase := by rw [smul_smul]
      _ = ((q : X) * ((q : X)⁻¹ * k * (q : X))) •
          gammaBase := by congr 1; group
      _ = (q : X) • (((q : X)⁻¹ * k * (q : X)) •
          gammaBase) := by rw [smul_smul]
      _ = (q : X) • gammaBase := by rw [hKbase hkq]
      _ = beta := hqX
  have hzGamma : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma ↔ d.toTheorem4bSixA.z • beta ∈ Gamma := by
    intro beta
    constructor
    · exact hzGammaForward beta
    · intro hbeta
      have htwice := hzGammaForward (d.toTheorem4bSixA.z • beta) hbeta
      have hsq : d.toTheorem4bSixA.z * d.toTheorem4bSixA.z = 1 := by
        simpa [pow_two] using d.toTheorem4bSixA.hz.sq_eq_one
      have hzz : d.toTheorem4bSixA.z • (d.toTheorem4bSixA.z • beta) = beta := by
        rw [← mul_smul, hsq, one_smul]
      simpa [hzz] using htwice
  have hpair : ∀ {beta gamma : conjugateCosetSpace M},
      beta ∈ Gamma → gamma ∈ Gamma → beta ≠ gamma →
        gammaPairCentralizer K beta gamma ≤ M := by
    intro beta gamma hbeta hgamma hne x hx
    have hxH : x ∈ H := hCH hx.1.1
    have hxbase : x • gammaBase =
        gammaBase :=
      hPointwise hbeta hgamma hne x hxH
        (MulAction.mem_stabilizer_iff.mp hx.1.2)
        (MulAction.mem_stabilizer_iff.mp hx.2)
        _ hbase
    rw [← baseCoset_stabilizer M]
    exact hxbase
  refine ⟨Gamma, hGammaK, hbase, hcard, hzGamma, ?_, ?_⟩
  · intro beta gamma hbeta hgamma hne x hx
    exact hpair hbeta hgamma hne ⟨⟨hx.2, hx.1.1⟩, hx.1.2⟩
  · intro beta hbeta hbetaNe
    obtain ⟨t, htZ, htH, htBase, _htBeta⟩ :=
      hSwap beta hbeta hbetaNe
    let u : X := rightConjugateElem t d.toTheorem4bSixA.z
    have huH : u ∈ H := by
      exact H.mul_mem (H.mul_mem (H.inv_mem hzH) htH) hzH
    have huNorm : u ∈ Subgroup.normalizer K := hHNorm huH
    have hKu : rightConjugateSet K u = K :=
      rightConjugateSet_eq_self_of_mem_normalizer_section7 K huNorm
    let E : Subgroup X := theorem4bSection7E M d.toTheorem4bSixA.z beta
    have hKleE : K ≤ E := by
      intro k hk
      have hkBeta : k ∈ MulAction.stabilizer X beta :=
        MulAction.mem_stabilizer_iff.mpr
          (((d.toTheorem4bSixA.mem_kFixedPoints_iff beta).mp (hGammaK hbeta)) k hk)
      have hzbetaGamma : d.toTheorem4bSixA.z • beta ∈ Gamma :=
        hzGammaForward beta hbeta
      have hkZbeta : k ∈ MulAction.stabilizer X (d.toTheorem4bSixA.z • beta) :=
        MulAction.mem_stabilizer_iff.mpr
          (((d.toTheorem4bSixA.mem_kFixedPoints_iff (d.toTheorem4bSixA.z • beta)).mp
            (hGammaK hzbetaGamma)) k hk)
      have hkM : k ∈ M := d.toTheorem4bSixA.hWM
        ((d.toTheorem4bSixA.mem_invertedSet_iff k).mp hk).1
      exact ⟨⟨hkM, hkBeta⟩, hkZbeta⟩
    have hpairE : gammaPairCentralizer K
        gammaBase beta ≤ E := by
      intro x hx
      have hxH : x ∈ H := hCH hx.1.1
      have hbaseNe : gammaBase (X := X) (M := M) ≠ beta :=
        hbetaNe.symm
      have hxbase : x • gammaBase = gammaBase :=
        hPointwise hbase hbeta hbaseNe x hxH
          (MulAction.mem_stabilizer_iff.mp hx.1.2)
          (MulAction.mem_stabilizer_iff.mp hx.2)
          _ hbase
      have hxM : x ∈ M := by
        rw [← baseCoset_stabilizer M]
        exact hxbase
      have hzbetaGamma : d.toTheorem4bSixA.z • beta ∈ Gamma :=
        hzGammaForward beta hbeta
      have hxZbeta : x • (d.toTheorem4bSixA.z • beta) = d.toTheorem4bSixA.z • beta :=
        hPointwise hbase hbeta hbaseNe x hxH
          (MulAction.mem_stabilizer_iff.mp hx.1.2)
          (MulAction.mem_stabilizer_iff.mp hx.2)
          _ hzbetaGamma
      exact ⟨⟨hxM, hx.2⟩, MulAction.mem_stabilizer_iff.mpr hxZbeta⟩
    have hpairU : gammaPairCentralizer
        (rightConjugateSet d.toTheorem4bSixA.invertedSet u)
        gammaBase beta ≤ E := by
      simpa [K, hKu, E] using hpairE
    have hKsubU : rightConjugateSet d.toTheorem4bSixA.invertedSet u ⊆ E := by
      simpa [K, hKu, E] using hKleE
    have hg : ∃ g : X,
        g • (d.toTheorem4bSixA.z • beta) = gammaBase ∧
          g • beta ∈ Gamma := by
      have hzbetaOrbit : d.toTheorem4bSixA.z • beta ∈
          MulAction.orbit R gammaBase := by
        rw [← hGammaOrbit]
        exact hzGammaForward beta hbeta
      rcases MulAction.mem_orbit_iff.mp hzbetaOrbit with ⟨q, hq⟩
      have hbetaOrbit : beta ∈ MulAction.orbit R gammaBase := by
        rw [← hGammaOrbit]
        exact hbeta
      let g : X := (q⁻¹ : R)
      refine ⟨g, ?_, ?_⟩
      · have hqInv : q⁻¹ • (d.toTheorem4bSixA.z • beta) = gammaBase := by
          rw [← hq]
          simp
        change ((q⁻¹ : R) : X) • (d.toTheorem4bSixA.z • beta) = gammaBase at hqInv
        simpa [g, Subgroup.coe_inv] using hqInv
      · have hqBetaOrbit := MulAction.mem_orbit_of_mem_orbit q⁻¹ hbetaOrbit
        rw [hGammaOrbit]
        change ((q⁻¹ : R) : X) • beta ∈ MulAction.orbit R gammaBase at hqBetaOrbit
        simpa [g, Subgroup.coe_inv] using hqBetaOrbit
    rcases hg with ⟨g, hgFirst, hgBeta⟩
    refine ⟨t, htZ, htBase, ?_, ?_, g, hgFirst, hgBeta⟩
    · exact hKsubU
    · intro x hx
      apply hpairU
      refine ⟨⟨hx.2, ?_⟩, hx.1.2⟩
      rw [baseCoset_stabilizer]
      exact hx.1.1


/-- First branch of Proposition 7.4, conditional on the distinguished
normalizing-swap assertion of Lemma 7.3. No odd pair stabilizer is assumed. -/
public theorem actionGamma_of_centralizer_le
    {X : Type u} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (d : ActionCounterexample Z M)
    (hC : Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M)
    (hswap : ∀ {beta : conjugateCosetSpace M} {P : Subgroup X},
      beta ∈ d.toTheorem4bSixA.kFixedPoints →
      beta ≠ (QuotientGroup.mk 1 : X ⧸ M) →
      theorem4bIsSylowSubgroupOf d.toTheorem4bSixA.p P
        (theorem4bSection7E M d.toTheorem4bSixA.z beta) →
      d.toTheorem4bSixA.z ∈ Subgroup.normalizer (P : Set X) →
      ∃ t : X,
        t ∈ Z ∧
        t ∈ Subgroup.normalizer (P : Set X) ∧
        t • (QuotientGroup.mk 1 : X ⧸ M) = beta) :
    ActionGamma d := by
  let Gamma : Set (conjugateCosetSpace M) := d.toTheorem4bSixA.kFixedPoints
  have hbase : gammaBase ∈ Gamma := by
    apply d.toTheorem4bSixA.fixedPoints_subset_kFixedPoints
    exact theorem4b_baseCoset_mem_fixedPoints d.toTheorem4bSixA.hWM
  have hcard : 1 < Nat.card Gamma := by
    obtain ⟨beta, hbetaW, hbetaNe⟩ := d.toTheorem4bSixA.exists_nonbase_fixedPoint
    have hbetaK : beta ∈ Gamma :=
      d.toTheorem4bSixA.fixedPoints_subset_kFixedPoints hbetaW
    let alphaPoint : Gamma := ⟨gammaBase, hbase⟩
    let betaPoint : Gamma := ⟨beta, hbetaK⟩
    let f : Bool → Gamma := fun b => cond b betaPoint alphaPoint
    have hf : Function.Injective f := by
      intro a b hab
      cases a <;> cases b
      · rfl
      · exfalso
        apply hbetaNe
        simpa [f, alphaPoint, betaPoint] using
          (congrArg Subtype.val hab).symm
      · exfalso
        apply hbetaNe
        simpa [f, alphaPoint, betaPoint] using congrArg Subtype.val hab
      · rfl
    have htwo : 2 ≤ Nat.card Gamma := by
      simpa using Nat.card_le_card_of_injective f hf
    omega
  have hzGammaForward : ∀ {beta : conjugateCosetSpace M},
      beta ∈ Gamma → d.toTheorem4bSixA.z • beta ∈ Gamma := by
    intro beta hbeta
    have hbetaW := d.toTheorem4bSixA.kFixedPoints_subset_fixedPoints hbeta
    have hWbeta : d.toTheorem4bSixA.W ≤ MulAction.stabilizer X beta := by
      intro w hw
      exact MulAction.mem_stabilizer_iff.mpr (hbetaW w hw)
    have hWzBeta : d.toTheorem4bSixA.W ≤
        MulAction.stabilizer X (d.toTheorem4bSixA.z • beta) :=
      theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
        d.toTheorem4bSixA.hzNorm hWbeta
    apply d.toTheorem4bSixA.fixedPoints_subset_kFixedPoints
    intro w hw
    exact MulAction.mem_stabilizer_iff.mp (hWzBeta hw)
  have hzGamma : ∀ beta : conjugateCosetSpace M,
      beta ∈ Gamma ↔ d.toTheorem4bSixA.z • beta ∈ Gamma := by
    intro beta
    constructor
    · exact hzGammaForward
    · intro hbeta
      have htwice := hzGammaForward hbeta
      have hzz : d.toTheorem4bSixA.z • (d.toTheorem4bSixA.z • beta) = beta := by
        rw [← mul_smul]
        have hsq : d.toTheorem4bSixA.z * d.toTheorem4bSixA.z = 1 := by
          simpa [pow_two] using d.toTheorem4bSixA.hz.sq_eq_one
        rw [hsq, one_smul]
      simpa [hzz] using htwice
  refine ⟨Gamma, fun _ h => h, hbase, hcard, hzGamma, ?_, ?_⟩
  · intro beta gamma _hbeta _hgamma _hne x hx
    exact hC hx.2
  · intro beta hbeta hbetaNe
    let E : Subgroup X := theorem4bSection7E M d.toTheorem4bSixA.z beta
    have hbetaW := d.toTheorem4bSixA.kFixedPoints_subset_fixedPoints hbeta
    have hWbeta : d.toTheorem4bSixA.W ≤ MulAction.stabilizer X beta := by
      intro w hw
      exact MulAction.mem_stabilizer_iff.mpr (hbetaW w hw)
    have hWD : d.toTheorem4bSixA.W ≤ theorem4bSection7D M beta :=
      le_inf d.toTheorem4bSixA.hWM hWbeta
    have hWE : d.toTheorem4bSixA.W ≤ E := by
      simpa [E, theorem4bSection7E, theorem4bSection7D] using
        theorem4b_le_triple_stabilizer_of_le_two_point_stabilizer
          d.toTheorem4bSixA.hzNorm hWD
    have hzE : d.toTheorem4bSixA.z ∈ Subgroup.normalizer (E : Set X) := by
      simpa [E, theorem4bSection7E, theorem4bSection7D] using
        theorem4b_mem_normalizer_tripleStabilizer
          (M := M) (z := d.toTheorem4bSixA.z) (beta := beta)
          d.toTheorem4bSixA.hz d.toTheorem4bSixA.hzM
    have hmove : d.z • beta ≠ beta := by
      intro hf
      exact hbetaNe (action_fixedPoint_eq_base h d.hzZ d.hzM hf)
    have hEF : E ≤ MulAction.stabilizer X beta ⊓
        MulAction.stabilizer X (d.z • beta) :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    obtain ⟨P, hPsyl, hWP, hzP, _⟩ :=
      h3.swapping_sylow d.z d.hzZ beta hmove d.p d.hp d.hpOdd
        E d.W hEF hzE d.hWp hWE d.hzNorm
    obtain ⟨t, htZ, htP, htBase⟩ :=
      hswap hbeta hbetaNe (by simpa [E] using hPsyl) hzP
    have ht := h.involutions t htZ
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    have htBeta : t • beta = gammaBase := by
      calc
        t • beta = t • (t • gammaBase) := by rw [htBase]
        _ = (t * t) • gammaBase := by rw [smul_smul]
        _ = gammaBase := by rw [htt, one_smul]
    have hPE : P ≤ E := by
      rcases hPsyl with ⟨Q, rfl⟩
      simpa using Subgroup.map_le_range E.subtype (Q : Subgroup E)
    let u : X := rightConjugateElem t d.toTheorem4bSixA.z
    have hu : IsInvolution u := isInvolution_rightConjugateElem ht
    have huNormP : u ∈ Subgroup.normalizer (P : Set X) := by
      change d.toTheorem4bSixA.z⁻¹ * t * d.toTheorem4bSixA.z ∈
        Subgroup.normalizer (P : Set X)
      exact (Subgroup.normalizer (P : Set X)).mul_mem
        ((Subgroup.normalizer (P : Set X)).mul_mem
          ((Subgroup.normalizer (P : Set X)).inv_mem hzP) htP) hzP
    have hKconjP : rightConjugateSet d.toTheorem4bSixA.invertedSet u ⊆ P := by
      intro x hx
      rcases hx with ⟨k, hk, rfl⟩
      have hkW : k ∈ d.toTheorem4bSixA.W :=
        ((d.toTheorem4bSixA.mem_invertedSet_iff k).mp hk).1
      have hkP : k ∈ P := hWP hkW
      have huInvNorm : u⁻¹ ∈ Subgroup.normalizer (P : Set X) :=
        (Subgroup.normalizer (P : Set X)).inv_mem huNormP
      simpa [rightConjugateElem] using
        ((Subgroup.mem_normalizer_iff.mp huInvNorm k).mp hkP)
    have hKconjE : rightConjugateSet d.toTheorem4bSixA.invertedSet u ⊆ E :=
      fun x hx => hPE (hKconjP hx)
    have hzBase : d.toTheorem4bSixA.z •
        (gammaBase (X := X) (M := M)) =
          gammaBase (X := X) (M := M) := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer]
      exact d.toTheorem4bSixA.hzM
    have huBase : u • gammaBase = d.toTheorem4bSixA.z • beta := by
      simp [u, rightConjugateElem, d.toTheorem4bSixA.hz.inv_eq_self,
        mul_smul, hzBase, htBase]
    have hCbase : Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤
        MulAction.stabilizer X
          (gammaBase (X := X) (M := M)) := by
      simpa [gammaBase, baseCoset_stabilizer] using hC
    have hCzBeta :
        Subgroup.centralizer (rightConjugateSet d.toTheorem4bSixA.invertedSet u) ≤
          MulAction.stabilizer X (d.toTheorem4bSixA.z • beta) := by
      simpa [huBase] using
        centralizer_rightConjugateSet_le_stabilizer_section7 hu hCbase
    have hpairE : theorem4bSection7D M beta ⊓
        Subgroup.centralizer (rightConjugateSet d.toTheorem4bSixA.invertedSet u) ≤ E := by
      intro x hx
      exact ⟨hx.1, hCzBeta hx.2⟩
    let g : X := t * d.toTheorem4bSixA.z
    have hgFirst : g • (d.toTheorem4bSixA.z • beta) = gammaBase := by
      have hzz : d.toTheorem4bSixA.z • (d.toTheorem4bSixA.z • beta) = beta := by
        rw [← mul_smul]
        have hsq : d.toTheorem4bSixA.z * d.toTheorem4bSixA.z = 1 := by
          simpa [pow_two] using d.toTheorem4bSixA.hz.sq_eq_one
        rw [hsq, one_smul]
      calc
        g • (d.toTheorem4bSixA.z • beta) =
            t • (d.toTheorem4bSixA.z • (d.toTheorem4bSixA.z • beta)) := by
              rw [show g = t * d.toTheorem4bSixA.z by rfl, mul_smul]
        _ = t • beta := by rw [hzz]
        _ = gammaBase := htBeta
    have hKz : rightConjugateSet d.toTheorem4bSixA.invertedSet d.toTheorem4bSixA.z =
        d.toTheorem4bSixA.invertedSet :=
      actionGamma_invertedSet_conjugate_z d.toTheorem4bSixA
    have hKuKg : rightConjugateSet d.toTheorem4bSixA.invertedSet u =
        rightConjugateSet d.toTheorem4bSixA.invertedSet g := by
      calc
        rightConjugateSet d.toTheorem4bSixA.invertedSet u =
            rightConjugateSet d.toTheorem4bSixA.invertedSet
              (d.toTheorem4bSixA.z * (t * d.toTheorem4bSixA.z)) := by
                simp [u, rightConjugateElem, d.toTheorem4bSixA.hz.inv_eq_self,
                  mul_assoc]
        _ = rightConjugateSet
              (rightConjugateSet d.toTheorem4bSixA.invertedSet d.toTheorem4bSixA.z)
              (t * d.toTheorem4bSixA.z) :=
                (rightConjugateSet_comp_section7
                  d.toTheorem4bSixA.invertedSet d.toTheorem4bSixA.z (t * d.toTheorem4bSixA.z)).symm
        _ = rightConjugateSet d.toTheorem4bSixA.invertedSet (t * d.toTheorem4bSixA.z) := by
              rw [hKz]
        _ = rightConjugateSet d.toTheorem4bSixA.invertedSet g := rfl
    have hKconjG : rightConjugateSet d.toTheorem4bSixA.invertedSet g ⊆ E := by
      rw [← hKuKg]
      exact hKconjE
    have hEstabBeta : E ≤ MulAction.stabilizer X beta :=
      inf_le_left.trans inf_le_right
    have hgBeta : g • beta ∈ Gamma := by
      apply (d.toTheorem4bSixA.mem_kFixedPoints_iff (g • beta)).mpr
      intro k hk
      let kg : X := rightConjugateElem k g
      have hkg : kg ∈ rightConjugateSet d.toTheorem4bSixA.invertedSet g :=
        ⟨k, hk, rfl⟩
      have hkgFix : kg • beta = beta :=
        MulAction.mem_stabilizer_iff.mp (hEstabBeta (hKconjG hkg))
      calc
        k • (g • beta) = (k * g) • beta := by rw [smul_smul]
        _ = (g * kg) • beta := by
          simp [kg, rightConjugateElem, mul_assoc]
        _ = g • (kg • beta) := by rw [smul_smul]
        _ = g • beta := by rw [hkgFix]
    refine ⟨t, htZ, htBase, ?_, ?_, g, hgFirst, hgBeta⟩
    · simpa [u] using hKconjE
    · simpa [u] using hpairE


/-- Assemble Proposition 7.4 from its two local inputs. Neither
input is a Gamma certificate: they are the normalizing swap of Lemma 7.3
and the operational odd-core factorization preceding Lemma 3.11. -/
public theorem actionGamma_of_local_inputs
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (d : ActionCounterexample Z M)
    (hswap : ∀ {beta : G ⧸ M} {P : Subgroup G},
      beta ∈ d.toTheorem4bSixA.kFixedPoints → beta ≠ QuotientGroup.mk 1 →
      theorem4bIsSylowSubgroupOf d.p P (theorem4bSection7E M d.z beta) →
      d.z ∈ Subgroup.normalizer (P : Set G) →
      ∃ t ∈ Z, t ∈ Subgroup.normalizer (P : Set G) ∧
        t • (QuotientGroup.mk 1 : G ⧸ M) = beta)
    (hfactor : ¬ Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M →
      let H := Subgroup.centralizer d.toTheorem4bSixA.invertedSet ⊔ Subgroup.zpowers d.z
      let zH : H := ⟨d.z,
        (show Subgroup.zpowers d.z ≤ H from le_sup_right) (Subgroup.mem_zpowers d.z)⟩
      pPrimeCore 2 H ⊔ Subgroup.centralizer ({zH} : Set H) = ⊤) :
    ActionGamma d := by
  by_cases hC : Subgroup.centralizer d.toTheorem4bSixA.invertedSet ≤ M
  · exact actionGamma_of_centralizer_le h h3 d hC hswap
  · exact actionGamma_of_centralizer_factorization h d hC (hfactor hC)

/-- Proposition 7.4 for a minimal counterexample, with the Section 3 inputs.
Lemma 7.3 supplies the distinguished normalizing swaps, and local strong
embedding supplies the odd-core factorization in the other centralizer branch. -/
public theorem actionGamma_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (h3 : ActionSectionThree Z M)
    (d : ActionMaximalCounterexample Z M) : ActionGamma d.data := by
  apply actionGamma_of_local_inputs h.disconnected h3 d.data
  · intro beta P hbeta hne hP hzP
    exact actionGamma_normalizing_swap h r hc h3 d hbeta hne hP hzP
  · exact actionGamma_local_factorization h r d.data

end BenderSuzuki.ZD
