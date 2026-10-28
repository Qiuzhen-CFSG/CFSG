module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.LocalData
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed.NormalizerStructure
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Preliminaries.Elementary
public import BenderSuzuki.SE.Proposition53
public import BenderSuzuki.SE.Section7Final

/-!
# The counting contradiction for Proposition 5.2(a)

The distinguished version of Lemmas 5.4--5.6 proves the maximal prime-share
fixed-point assertion. The local normalizer structure is discharged from
the minimal-counterexample and simple-reduction hypotheses in the final theorem.
Choose a pair not interchanged by a distinguished normalizing involution. A
Sylow subgroup of its stabilizer fixes exactly two points. Its relative
normalizer of P is larger than P; an invariant Sylow overgroup and the
fixed-point congruence show that this larger subgroup is another candidate.
Equality of inverted cardinalities supplies its invariant involution.

Adapted from the elementary counting proof in `BenderSuzuki.SE.Theorem2`;
no ambient strong embedding is used. The conditional interfaces remain
available independently of the final source assembly.

Source: GLS, Volume 4, Chapter 2, Proposition 5.2(a), Lemmas 5.4--5.6.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise

private theorem fixedPoints_card_even_of_fixedPoint_free_involution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Finite Omega] {P : Subgroup G} {s : G}
    (hs : PFAppendixIII.IsInvolution s)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set G))
    (hfree : ∀ omega : Omega,
      omega ∈ fixedPointsOfSubgroup G Omega P → s • omega ≠ omega) :
    Even (Nat.card {omega : Omega //
      omega ∈ fixedPointsOfSubgroup G Omega P}) := by
  classical
  let C : Subgroup G := Subgroup.zpowers s
  have hCNorm : C ≤ Subgroup.normalizer (P : Set G) := by
    exact Subgroup.zpowers_le.mpr hsNorm
  let FixedP : SubMulAction C Omega :=
    { carrier := fixedPointsOfSubgroup G Omega P
      smul_mem' := fun c omega homega =>
        fixedPoints_smul_of_mem_normalizer (hCNorm c.property) homega }
  have hCp : IsPGroup 2 C := by
    apply IsPGroup.of_card (p := 2) (G := C) (n := 1)
    simp [C, Nat.card_zpowers,
      orderOf_eq_prime hs.sq_eq_one hs.ne_one]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfixedZero : Nat.card (MulAction.fixedPoints C FixedP) = 0 := by
    rw [Finite.card_eq_zero_iff]
    refine ⟨fun omega => ?_⟩
    have hsFix := MulAction.mem_fixedPoints.mp omega.property
      (⟨s, Subgroup.mem_zpowers s⟩ : C)
    have hsFixVal : s • (omega : Omega) = omega :=
      congrArg Subtype.val hsFix
    exact hfree omega omega.1.property hsFixVal
  have hmod := hCp.card_modEq_card_fixedPoints FixedP
  rw [hfixedZero] at hmod
  exact even_iff_two_dvd.mpr (Nat.modEq_zero_iff_dvd.mp hmod)


private theorem involution_mem_normalizer_twoPointStabilizer_of_swap
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {t : G} {beta gamma : Omega}
    (ht : PFAppendixIII.IsInvolution t) (htBeta : t • beta = gamma) :
    t ∈ Subgroup.normalizer
      ((MulAction.stabilizer G beta ⊓
        MulAction.stabilizer G gamma : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have htGamma : t • gamma = beta := by
    rw [← htBeta, ← mul_smul, htt, one_smul]
  have hforward : ∀ {x : G},
      x ∈ (MulAction.stabilizer G beta ⊓
        MulAction.stabilizer G gamma : Subgroup G) →
      t * x * t⁻¹ ∈ (MulAction.stabilizer G beta ⊓
        MulAction.stabilizer G gamma : Subgroup G) := by
    intro x hx
    refine ⟨MulAction.mem_stabilizer_iff.mpr ?_,
      MulAction.mem_stabilizer_iff.mpr ?_⟩
    · calc
        (t * x * t⁻¹) • beta = t • (x • (t⁻¹ • beta)) := by
          simp [mul_smul, mul_assoc]
        _ = t • (x • gamma) := by rw [ht.inv_eq_self, htBeta]
        _ = t • gamma := by rw [MulAction.mem_stabilizer_iff.mp hx.2]
        _ = beta := htGamma
    · calc
        (t * x * t⁻¹) • gamma = t • (x • (t⁻¹ • gamma)) := by
          simp [mul_smul, mul_assoc]
        _ = t • (x • beta) := by rw [ht.inv_eq_self, htGamma]
        _ = t • beta := by rw [MulAction.mem_stabilizer_iff.mp hx.1]
        _ = gamma := htBeta
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward
  · intro hx
    have hback := hforward hx
    have hcancel : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [ht.inv_eq_self]
      calc
        t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [htt]; simp
    rwa [hcancel] at hback


private theorem mem_of_mem_inverted_of_card_eq_of_le
    {G : Type*} [Group G] [Finite G] {s : G} {P B : Subgroup G}
    (hPB : P ≤ B)
    (hcard : theorem4bInvertedCard s P = theorem4bInvertedCard s B)
    {x : G} (hxB : x ∈ B) (hxInv : s * x * s⁻¹ = x⁻¹) :
    x ∈ P := by
  let f : {y : G // y ∈ P ∧ s * y * s⁻¹ = y⁻¹} →
      {y : G // y ∈ B ∧ s * y * s⁻¹ = y⁻¹} :=
    fun y => ⟨y, hPB y.property.1, y.property.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hval := congrArg
      (fun q : {y : G // y ∈ B ∧ s * y * s⁻¹ = y⁻¹} => (q : G)) hab
    simpa [f] using hval
  have hcardTypes :
      Nat.card {y : G // y ∈ P ∧ s * y * s⁻¹ = y⁻¹} =
        Nat.card {y : G // y ∈ B ∧ s * y * s⁻¹ = y⁻¹} := by
    simpa [theorem4bInvertedCard] using hcard
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).2
      ⟨hf, hcardTypes⟩).2
  obtain ⟨y, hy⟩ := hsurj ⟨x, hxB, hxInv⟩
  have hyval : (y : G) = x := congrArg Subtype.val hy
  simpa [hyval] using y.property.1

/-- The elementwise form of the Lemma 5.6 commutator argument: if the
inverted sets in nested subgroups `P ≤ A ≤ B` have the same cardinality,
then an involution normalizing `B` also normalizes `A`. -/
private theorem mem_normalizer_of_invertedCard_eq_of_le
    {G : Type*} [Group G] [Finite G] {s : G}
    {P A B : Subgroup G}
    (hs : PFAppendixIII.IsInvolution s)
    (hPA : P ≤ A) (hAB : A ≤ B)
    (hsNormB : s ∈ Subgroup.normalizer (B : Set G))
    (hcard : theorem4bInvertedCard s P = theorem4bInvertedCard s B) :
    s ∈ Subgroup.normalizer (A : Set G) := by
  have hPB : P ≤ B := hPA.trans hAB
  have hss : s * s = 1 := by
    simpa [pow_two] using hs.sq_eq_one
  have hforward : ∀ {a : G}, a ∈ A → s * a * s⁻¹ ∈ A := by
    intro a haA
    have hconjB : s * a * s⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp hsNormB a).1 (hAB haA)
    let c : G := s * a * s⁻¹ * a⁻¹
    have hcB : c ∈ B := B.mul_mem hconjB (B.inv_mem (hAB haA))
    have hcInv : s * c * s⁻¹ = c⁻¹ := by
      dsimp [c]
      rw [hs.inv_eq_self]
      calc
        s * (s * a * s * a⁻¹) * s =
            (s * s) * a * s * a⁻¹ * s := by group
        _ = a * s * a⁻¹ * s := by rw [hss]; simp
        _ = (s * a * s * a⁻¹)⁻¹ := by
          simp only [mul_inv_rev, inv_inv, hs.inv_eq_self]
          group
    have hcP := mem_of_mem_inverted_of_card_eq_of_le
      hPB hcard hcB hcInv
    have hconjEq : s * a * s⁻¹ = c * a := by
      simp [c]
    rw [hconjEq]
    exact A.mul_mem (hPA hcP) haA
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hforward
  · intro ha
    have hback := hforward ha
    have hcancel : s * (s * a * s⁻¹) * s⁻¹ = a := by
      rw [hs.inv_eq_self]
      calc
        s * (s * a * s) * s = (s * s) * a * (s * s) := by group
        _ = a := by rw [hss]; simp
    rwa [hcancel] at hback

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem distinguished_fixed_unique
    (h : IsProductDisconnected Z M)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    {s : G} (hs : s ∈ Z) {a b : G ⧸ M}
    (ha : s • a = a) (hb : s • b = b) : a = b := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  obtain ⟨g, hg⟩ := isConj_iff.mp (hclass s hs z hz)
  have hf {c : G ⧸ M} (hc : s • c = c) : g • c = QuotientGroup.mk 1 := by
    apply action_fixedPoint_eq_base h hz hzM
    rw [← hg]
    simpa [mul_smul] using congrArg (fun d : G ⧸ M => g • d) hc
  exact MulAction.injective g ((hf ha).trans (hf hb).symm)

/-- Section 3.9 with the specified Sylow subgroup and a distinguished swap. -/
public theorem sectionFive_distinguished_sylow_swap
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    {beta delta : G ⧸ M} (hne : beta ≠ delta) {R : Subgroup G}
    (hR : theorem4bIsSylowSubgroupOf p R
      (MulAction.stabilizer G beta ⊓ MulAction.stabilizer G delta)) :
    ∃ t ∈ Z, t ∈ Subgroup.normalizer (R : Set G) ∧ t • beta = delta := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, htZ, htmove⟩ := h3.swap beta delta hne
  have ht := h.involutions t htZ
  let D := MulAction.stabilizer G beta ⊓ MulAction.stabilizer G delta
  have htD : t ∈ Subgroup.normalizer (D : Set G) :=
    involution_mem_normalizer_twoPointStabilizer_of_swap ht htmove
  obtain ⟨Q, hQ, _, htQ, _⟩ := h3.swapping_sylow t htZ beta
    (by simpa [htmove] using hne.symm) p hp hpOdd D ⊥
    (by simp [D, htmove]) htD IsPGroup.of_bot bot_le (by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp)
  obtain ⟨S, hS⟩ := hQ
  obtain ⟨T, hT⟩ := hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D S T
  have hQR : Q.conjBy (g : G) = R := by
    rw [hS, hT, ← hg, Sylow.coe_subgroup_smul]
    change ((S : Subgroup D).map D.subtype).map (MulAut.conj (g : G)).toMonoidHom =
      ((S : Subgroup D).map (MulAut.conj g).toMonoidHom).map D.subtype
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  refine ⟨MulAut.conj (g : G) t, h.invariant g t htZ, ?_, ?_⟩
  · rw [← hQR]
    exact Subgroup.le_normalizer_map (H := Q) (MulAut.conj (g : G)).toMonoidHom
      (Subgroup.mem_map_of_mem _ htQ)
  · have hgb := MulAction.mem_stabilizer_iff.mp g.property.1
    have hgd := MulAction.mem_stabilizer_iff.mp g.property.2
    have hginvb := MulAction.mem_stabilizer_iff.mp (D.inv_mem g.property).1
    simpa [MulAut.conj_apply, mul_smul, hginvb, htmove] using hgd

/-- Lemmas 5.4--5.6 with the local rank, conjugacy and odd-core premises
explicit. These premises must be discharged before asserting Proposition 5.2. -/
public theorem sectionFive_maximal_fixes_of_normalizerStructure
    (h : IsProductDisconnected Z M)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (h3 : ActionSectionThree Z M)
    {z : G} (hzZ : z ∈ Z) (hzM : z ∈ M) {p : ℕ}
    (hp : p.Prime) (hpOdd : Odd p) {P : Subgroup G}
    (hmax : Maximal (actionPrimeShareCandidate Z M z p) P)
    (hlocal : SectionFiveNormalizerStructure Z P)
    {s : G} (hsZ : s ∈ Z)
    (hsNorm : s ∈ Subgroup.normalizer (P : Set G))
    {alpha : G ⧸ M} (hsAlpha : s • alpha = alpha) :
    alpha ∈ fixedPointsOfSubgroup G (G ⧸ M) P := by
  have hs := h.involutions s hsZ
  obtain ⟨u, huZ, huN, huCard⟩ := hmax.1.2.2
  obtain ⟨g, hg⟩ := hlocal.one_class u huZ huN s hsZ hsNorm
  have hsCard : theorem4bInvertedCard s P = theorem4bPrimeShare M z p := by
    have hc := theorem4bInvertedCard_conjBy u (g : G)⁻¹ P
    have hPconj : P.conjBy (g : G) = P :=
      section11_conjBy_eq_of_mem_normalizer g.property
    simpa only [rightConjugateElem, inv_inv, ← MulAut.conj_apply, hg, hPconj] using
      hc.trans huCard
  classical
  by_contra hPAlpha
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let FixedP : SubMulAction N (conjugateCosetSpace M) :=
    { carrier := fixedPointsOfSubgroup G (conjugateCosetSpace M) P
      smul_mem' := fun n omega homega =>
        fixedPoints_smul_of_mem_normalizer n.property homega }
  let sN : N := ⟨s, hsNorm⟩
  have hsN : PFAppendixIII.IsInvolution sN := IsInvolution.subtype hs hsNorm
  have hfree : ∀ omega : conjugateCosetSpace M,
      omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) P →
      s • omega ≠ omega := by
    intro omega homega hsOmega
    have hEq := distinguished_fixed_unique h hclass hsZ hsAlpha hsOmega
    apply hPAlpha
    simpa [hEq] using homega
  have hEven : Even (Nat.card FixedP) := by
    change Even (Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) P})
    exact fixedPoints_card_even_of_fixedPoint_free_involution
      hs hsNorm hfree
  have hFixedPpos : 0 < Nat.card FixedP := by
    change 0 < Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) P}
    exact lt_of_lt_of_le (by decide : 0 < 3) hmax.1.2.1
  let : Nonempty FixedP := (Nat.card_pos_iff.mp hFixedPpos).1
  let L : Subgroup N := Subgroup.closure (N.subtype ⁻¹' Z)
  let : MulAction L FixedP := MulAction.compHom FixedP L.subtype
  have hbadPair : ∃ beta delta : FixedP, beta ≠ delta ∧
      ∀ t : N, (t : G) ∈ Z →
        (t : G) • (beta : conjugateCosetSpace M) ≠
          (delta : conjugateCosetSpace M) := by
    by_contra hno
    push Not at hno
    have hpair : ∀ beta delta : FixedP, beta ≠ delta →
        ∃ t : L, PFAppendixIII.IsInvolution t ∧ t • beta = delta := by
      intro beta delta hne
      obtain ⟨t, ht, htMove⟩ := hno beta delta hne
      have htL : t ∈ L := Subgroup.subset_closure ht
      refine ⟨⟨t, htL⟩,
        IsInvolution.subtype (IsInvolution.subtype (h.involutions t ht) t.property) htL, ?_⟩
      apply Subtype.ext
      exact htMove
    have hcardTwo := chapter1_rank_one_pair_involutions_card_eq_two
      hlocal.rank hEven hpair
    have hthree : 3 ≤ Nat.card FixedP := hmax.1.2.1
    omega
  obtain ⟨betaP, deltaP, hbetaDeltaP, hbad⟩ := hbadPair
  let beta : conjugateCosetSpace M := betaP
  let delta : conjugateCosetSpace M := deltaP
  have hbeta : beta ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) P :=
    betaP.property
  have hdelta : delta ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) P :=
    deltaP.property
  have hbetaDelta : beta ≠ delta := by
    intro h
    exact hbetaDeltaP (Subtype.ext h)
  let D : Subgroup G :=
    MulAction.stabilizer G beta ⊓ MulAction.stabilizer G delta
  have hPD : P ≤ D := by
    intro x hxP
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hbeta x hxP),
      MulAction.mem_stabilizer_iff.mpr (hdelta x hxP)⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hmax.1.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDS⟩ := hPDp.exists_le_sylow
  let R : Subgroup G := (S : Subgroup D).map D.subtype
  have hPR : P ≤ R := by
    intro x hxP
    let xD : D := ⟨x, hPD hxP⟩
    exact Subgroup.mem_map.mpr
      ⟨xD, hPDS (show xD ∈ PD from hxP), rfl⟩
  have hRp : IsPGroup p R := S.isPGroup'.map D.subtype
  have hRD : R ≤ D := by
    simpa [R] using Subgroup.map_le_range D.subtype (S : Subgroup D)
  have hRsyl : theorem4bIsSylowSubgroupOf p R D := ⟨S, rfl⟩
  obtain ⟨t, htZ, htNormR, htBeta⟩ :=
    sectionFive_distinguished_sylow_swap
      h h3 hp hpOdd hbetaDelta hRsyl
  have hPRlt : P < R := by
    apply lt_of_le_of_ne hPR
    intro hEq
    have htNormP : t ∈ Subgroup.normalizer (P : Set G) := by
      rw [hEq]
      exact htNormR
    let tN : N := ⟨t, htNormP⟩
    exact hbad tN htZ htBeta
  have hRbeta : beta ∈
      fixedPointsOfSubgroup G (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).1
  have hRdelta : delta ∈
      fixedPointsOfSubgroup G (conjugateCosetSpace M) R := by
    intro x hxR
    exact MulAction.mem_stabilizer_iff.mp (hRD hxR).2
  have hRcard : Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) R} = 2 := by
    apply Nat.le_antisymm
    · by_contra hle
      have hthree : 2 < Nat.card {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) R} := by
        omega
      have hRexact :=
        (h3.swapping_bound z hzZ hzM t htZ beta
          (by simpa [htBeta] using hbetaDelta.symm) p hp hpOdd R hRp
          (by simpa only [htBeta] using hRD) htNormR).2 (by simpa [htBeta] using hRsyl)
      have hRleP := hmax.2
        ⟨hRp, hthree, ⟨t, htZ, htNormR, hRexact⟩⟩ hPR
      exact (not_le_of_gt hPRlt) hRleP
    · let f : Fin 2 → {omega : conjugateCosetSpace M //
          omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) R} :=
        fun i => if i = 0 then ⟨beta, hRbeta⟩ else ⟨delta, hRdelta⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          apply hbetaDelta
          simpa [f] using congrArg Subtype.val hij
        · exfalso
          apply hbetaDelta
          simpa [f] using (congrArg Subtype.val hij).symm
        · rfl
      simpa using Nat.card_le_card_of_injective f hf
  let : Fact (Nat.Prime p) := ⟨hp⟩
  have hOmegaMod : Nat.card (conjugateCosetSpace M) ≡ 2 [MOD p] := by
    have hRcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hRp
    rwa [hRcard] at hRcong
  obtain ⟨A, hAp, hPA, hAR, hAN⟩ :=
    exists_larger_normalizer_pSubgroup hp hRp hPRlt
  let AN : Subgroup N := A.subgroupOf N
  have hANp : IsPGroup p AN :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨B, hANB⟩ := hANp.exists_le_sylow
  let BN : Subgroup N := (B : Subgroup N)
  let BG : Subgroup G := BN.map N.subtype
  have hABG : A ≤ BG := by
    intro a haA
    let aN : N := ⟨a, hAN haA⟩
    exact Subgroup.mem_map.mpr
      ⟨aN, hANB (show aN ∈ AN from haA), rfl⟩
  have hPBG : P ≤ BG := hPA.le.trans hABG
  have hBGp : IsPGroup p BG := B.isPGroup'.map N.subtype
  have hfactor : pPrimeCore 2 N ⊔
      Subgroup.centralizer ({sN} : Set N) = ⊤ :=
    hlocal.factor sN hsZ
  have hbotp : IsPGroup p (⊥ : Subgroup N) := IsPGroup.of_bot
  obtain ⟨S₀, _hbotS₀, hsNormS₀⟩ :=
    exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top
      hsN hp hpOdd hbotp (by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        simp) hfactor
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N S₀ B
  have hBconj : (B : Subgroup N) =
      (S₀ : Subgroup N).conjBy (g : N) := by
    rw [← hg]
    simp only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.conjBy]
    congr 1
  let vN : N := rightConjugateElem sN (g : N)⁻¹
  have hvN : PFAppendixIII.IsInvolution vN := isInvolution_rightConjugateElem hsN
  have hvNormBN : vN ∈ Subgroup.normalizer ((B : Subgroup N) : Set N) := by
    rw [hBconj]
    have hconjNorm :=
      section11_conjBy_le_normalizer_conjBy_of_le_normalizer
        (Subgroup.zpowers_le.mpr hsNormS₀) (g : N)
    apply hconjNorm
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨sN, Subgroup.mem_zpowers sN, ?_⟩
    simp [vN, rightConjugateElem]
  let v : G := (vN : G)
  have hvZ : v ∈ Z := by
    simpa [v, vN, sN, rightConjugateElem, MulAut.conj_apply] using h.invariant (g : G) s hsZ
  have hv : PFAppendixIII.IsInvolution v :=
    IsInvolution.map_of_injective hvN N.subtype Subtype.val_injective
  have hvNormBG : v ∈ Subgroup.normalizer (BG : Set G) := by
    have hvMapMem : v ∈
        (Subgroup.normalizer ((B : Subgroup N) : Set N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype hvNormBN
    exact (Subgroup.le_normalizer_map (H := (B : Subgroup N)) N.subtype)
      hvMapMem
  have hPconj : P.conjBy (g : G) = P :=
    section11_conjBy_eq_of_mem_normalizer g.property
  have hvEq : v = rightConjugateElem s (g : G)⁻¹ := by
    simp [v, vN, sN, rightConjugateElem]
  have hPconj' : P.conjBy (((g : G)⁻¹)⁻¹) = P := by
    simpa using hPconj
  have hInvPv : theorem4bInvertedCard v P =
      theorem4bPrimeShare M z p := by
    have hcard := theorem4bInvertedCard_conjBy s (g : G)⁻¹ P
    rw [hvEq, ← hPconj']
    exact hcard.trans hsCard
  let FixedB := {omega : conjugateCosetSpace M //
    omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) BG}
  have hBmod : Nat.card FixedB ≡ 2 [MOD p] := by
    have hBGcong := IsPGroup.card_modEq_card_fixedPointsOfSubgroup
      (Omega := conjugateCosetSpace M) hBGp
    exact hBGcong.symm.trans hOmegaMod
  have hpNeTwo : p ≠ 2 := by
    intro h
    subst p
    exact hpOdd.not_two_dvd_nat (dvd_refl 2)
  have hpGtTwo : 2 < p := by
    have hpTwo := hp.two_le
    omega
  have hBcardTwo : 2 ≤ Nat.card FixedB := by
    by_contra hnot
    have hlt : Nat.card FixedB < 2 := by omega
    change Nat.card FixedB % p = 2 % p at hBmod
    rw [Nat.mod_eq_of_lt (lt_trans hlt hpGtTwo),
      Nat.mod_eq_of_lt hpGtTwo] at hBmod
    omega
  let : Nontrivial FixedB :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let lambda₀ : FixedB := Classical.choice inferInstance
  obtain ⟨eta₀, heta₀⟩ := exists_ne lambda₀
  have hexistsMoved : ∃ lambdaB : FixedB,
      v • (lambdaB : conjugateCosetSpace M) ≠ lambdaB := by
    by_cases hlambda₀ : v • (lambda₀ : conjugateCosetSpace M) = lambda₀
    · refine ⟨eta₀, ?_⟩
      intro hetaFix
      apply heta₀
      apply Subtype.ext
      exact distinguished_fixed_unique h hclass hvZ hetaFix hlambda₀
    · exact ⟨lambda₀, hlambda₀⟩
  obtain ⟨lambdaB, hlambdaMove⟩ := hexistsMoved
  let lambda : conjugateCosetSpace M := lambdaB
  let mu : conjugateCosetSpace M := v • lambda
  have hlambdaB : lambda ∈
      fixedPointsOfSubgroup G (conjugateCosetSpace M) BG := lambdaB.property
  have hmuB : mu ∈
      fixedPointsOfSubgroup G (conjugateCosetSpace M) BG :=
    fixedPoints_smul_of_mem_normalizer hvNormBG hlambdaB
  have hlambdaMu : lambda ≠ mu := by
    exact Ne.symm hlambdaMove
  have hvLambda : v • lambda = mu := rfl
  have hvMu : v • mu = lambda := by
    change v • (v • lambda) = lambda
    rw [← mul_smul, show v * v = 1 by
      simpa [pow_two] using hv.sq_eq_one]
    simp
  have hAcardThree : 3 ≤ Nat.card {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) A} := by
    let FixedA := {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup G (conjugateCosetSpace M) A}
    let betaA : FixedA := ⟨beta, fun x hxA => hRbeta x (hAR hxA)⟩
    let deltaA : FixedA := ⟨delta, fun x hxA => hRdelta x (hAR hxA)⟩
    have hbetaDeltaA : betaA ≠ deltaA := by
      intro h
      apply hbetaDelta
      simpa [betaA, deltaA] using
        congrArg (fun q : FixedA =>
          (q : conjugateCosetSpace M)) h
    by_contra hnot
    have hnot' : ¬ 3 ≤ Nat.card FixedA := by
      simpa [FixedA] using hnot
    have hAcardLe : Nat.card FixedA ≤ 2 := by omega
    let : Nontrivial FixedA := ⟨⟨betaA, deltaA, hbetaDeltaA⟩⟩
    have hAcardGtOne : 1 < Nat.card FixedA :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hAcard : Nat.card FixedA = 2 := by omega
    obtain ⟨otherA, _hotherA, hotherAUnique⟩ :=
      (Nat.card_eq_two_iff' betaA).mp hAcard
    have hdeltaOtherA : deltaA = otherA := by
      apply hotherAUnique deltaA
      exact Ne.symm hbetaDeltaA
    have hFixedAEq : ∀ omega : FixedA,
        omega = betaA ∨ omega = deltaA := by
      intro omega
      by_cases homega : omega = betaA
      · exact Or.inl homega
      · exact Or.inr ((hotherAUnique omega homega).trans
          hdeltaOtherA.symm)
    let lambdaA : FixedA := ⟨lambda, fun x hxA =>
      hlambdaB x (hABG hxA)⟩
    let muA : FixedA := ⟨mu, fun x hxA =>
      hmuB x (hABG hxA)⟩
    have hlambdaMuA : lambdaA ≠ muA := by
      intro h
      exact hlambdaMu (congrArg Subtype.val h)
    have hvBetaDelta : v • beta = delta := by
      rcases hFixedAEq lambdaA with hlambdaBetaA | hlambdaDeltaA
      · have hmuDeltaA : muA = deltaA := by
          rcases hFixedAEq muA with hmuBetaA | hmuDeltaA
          · exfalso
            apply hlambdaMuA
            exact hlambdaBetaA.trans hmuBetaA.symm
          · exact hmuDeltaA
        have hlambdaBeta : lambda = beta := by
          simpa [lambdaA, betaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hlambdaBetaA
        have hmuDelta : mu = delta := by
          simpa [muA, deltaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hmuDeltaA
        rw [← hlambdaBeta, hvLambda, hmuDelta]
      · have hmuBetaA : muA = betaA := by
          rcases hFixedAEq muA with hmuBetaA | hmuDeltaA
          · exact hmuBetaA
          · exfalso
            apply hlambdaMuA
            exact hlambdaDeltaA.trans hmuDeltaA.symm
        have hlambdaDelta : lambda = delta := by
          simpa [lambdaA, deltaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hlambdaDeltaA
        have hmuBeta : mu = beta := by
          simpa [muA, betaA] using
            congrArg (fun q : FixedA =>
              (q : conjugateCosetSpace M)) hmuBetaA
        rw [← hmuBeta, hvMu, hlambdaDelta]
    exact hbad vN hvZ (by
      simpa [v] using hvBetaDelta)
  have hBpair : BG ≤ MulAction.stabilizer G lambda ⊓
      MulAction.stabilizer G mu := by
    intro x hxB
    exact ⟨MulAction.mem_stabilizer_iff.mpr (hlambdaB x hxB),
      MulAction.mem_stabilizer_iff.mpr (hmuB x hxB)⟩
  have hInvBGUpper : theorem4bInvertedCard v BG ≤
      theorem4bPrimeShare M z p :=
    (h3.swapping_bound z hzZ hzM v hvZ lambda hlambdaMove p hp hpOdd
      BG hBGp hBpair hvNormBG).1
  have hInvBG : theorem4bInvertedCard v BG =
      theorem4bPrimeShare M z p := by
    apply Nat.le_antisymm hInvBGUpper
    exact hInvPv.symm.trans_le (theorem4bInvertedCard_mono hPBG)
  have hInvPBG : theorem4bInvertedCard v P =
      theorem4bInvertedCard v BG := hInvPv.trans hInvBG.symm
  have hvNormA : v ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_invertedCard_eq_of_le
      hv hPA.le hABG hvNormBG hInvPBG
  have hInvA : theorem4bInvertedCard v A =
      theorem4bPrimeShare M z p := by
    apply Nat.le_antisymm
    · exact (theorem4bInvertedCard_mono hABG).trans_eq hInvBG
    · exact hInvPv.symm.trans_le
        (theorem4bInvertedCard_mono hPA.le)
  have hAleP := hmax.2
    ⟨hAp, by omega, ⟨v, hvZ, hvNormA, hInvA⟩⟩ hPA.le
  exact (not_le_of_gt hPA) hAleP


/-- Final counting assembly, conditional on the separate local-group
reduction. The latter is an outstanding prerequisite, not a conclusion
included in the maximal-candidate hypothesis. -/
public theorem actionPrimeShareMaximalFixes_of_normalizerStructure
    (h : IsProductDisconnected Z M)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (h3 : ActionSectionThree Z M)
    (hlocal : ∀ P : Subgroup G, Odd (Nat.card P) →
      ∀ s ∈ Z, s ∈ Subgroup.normalizer (P : Set G) →
      ∀ beta : G ⧸ M, s • beta = beta →
      ¬ P ≤ MulAction.stabilizer G beta → SectionFiveNormalizerStructure Z P) :
    ActionPrimeShareMaximalFixes Z M := by
  intro z hzZ hzM p hp hpOdd P hmax s hsZ hsN beta hsBeta
  by_contra hnot
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hmax.1.1
    rw [hn]
    exact hpOdd.pow
  have hfix := sectionFive_maximal_fixes_of_normalizerStructure h hclass h3 hzZ hzM
    hp hpOdd hmax (hlocal P hodd s hsZ hsN beta hsBeta hnot) hsZ hsN hsBeta
  exact hnot (fun x hx => MulAction.mem_stabilizer_iff.mpr (hfix x hx))

/-- Proposition 5.2(a), with the local normalizer structure discharged from
the minimal-counterexample and simple-reduction hypotheses. -/
public theorem actionPrimeShareMaximalFixes_of_sectionThree
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (h3 : ActionSectionThree Z M) : ActionPrimeShareMaximalFixes Z M :=
  actionPrimeShareMaximalFixes_of_normalizerStructure h.disconnected
    (productDisconnected_isConj h.disconnected) h3
    (fun P hodd _s hs hsN _beta hsBeta hnot =>
      sectionFive_normalizerStructure_of_not_fixed h r P hodd hs hsN hsBeta hnot)

end BenderSuzuki.ZD
