module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.Evenness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.OrbitControl
public import Theory.GroupTheory.PResidualCommutator
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupAction.OddInvariantSylowConjugacy.Ambient
public import Theory.GroupTheory.Commutator.OddInvolutionRestriction
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.Commutator.FixedConjugateContainment
public import Theory.GroupAction.FourCentralizerCommutatorGeneration
public import Theory.GroupAction.OddInvolutionFrattini
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Local.Sylow

/-!
# Coprime action on the residual odd core

For the two-point stabilizer `D = M ∩ Mᵗ`, conjugation by the involution
`t` exchanges the two factors. Thus it normalizes `D` and its characteristic
odd core. The actual subgroup `K = [O₂′(D), ⟨t⟩]` has odd order and satisfies
`[K, ⟨t⟩] = K` by coprime commutator idempotence. We keep `K` and `O₂′(D)`
distinct throughout.

Four-centralizer generation proves GLS, Volume 4, Chapter 2, Lemma 16.1.
The Section 3 odd-core containment, fixed Sylow conjugators and literal
Frattini quotient actions supply the coprime-action steps of Proposition 16.5.
The model-dependent cyclicity arguments and final rank contradiction are
left to the rank-one assembly.

Source: `refs/KGroup/GLS4/Chapter2.tex`, Section 16, especially Lemma 16.1
and the paragraphs beginning “Now set W₁” and “Set R̄ = R/Φ(R)”.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] {M : Subgroup G} {t : G}

/-- The ambient image of the odd core of the two-point stabilizer. -/
@[expose] public def residualOddCore (M : Subgroup G) (t : G) : Subgroup G :=
  (pPrimeCore 2 (residualPairStabilizer M t)).map (residualPairStabilizer M t).subtype

public theorem residualOddCore_le_pair :
    residualOddCore M t ≤ residualPairStabilizer M t := map_subtype_le _

/-- An involution normalizes the intersection of a subgroup and its conjugate. -/
public theorem involution_mem_normalizer_residualPairStabilizer (ht : PFAppendixIII.IsInvolution t) :
    t ∈ normalizer (residualPairStabilizer M t : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (M ⊓ M.conjBy t⁻¹).map (MulAut.conj t).toMonoidHom = M ⊓ M.conjBy t⁻¹
  rw [map_inf _ _ _ (MulAut.conj t).injective]
  change M.conjBy t ⊓ (M.conjBy t⁻¹).conjBy t = M ⊓ M.conjBy t⁻¹
  rw [conjBy_inv', ht.inv_eq_self, inf_comm]

public theorem pair_sup_zpowers_le_normalizer_residualOddCore (ht : PFAppendixIII.IsInvolution t) :
    residualPairStabilizer M t ⊔ zpowers t ≤ normalizer (residualOddCore M t : Set G) := by
  apply le_trans (sup_le (residualPairStabilizer M t).le_normalizer
    (zpowers_le.mpr (involution_mem_normalizer_residualPairStabilizer ht)))
  exact normalizer_le_normalizer_characteristic_image _ _

public theorem residualOddCore_odd [Finite G] : Odd (Nat.card (residualOddCore M t)) := by
  unfold residualOddCore
  rw [card_map_of_injective (residualPairStabilizer M t).subtype_injective]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

public theorem residualCommutator_le_oddCore (ht : PFAppendixIII.IsInvolution t) :
    residualCommutator M t ≤ residualOddCore M t :=
  le_normalizer_iff_commutator_le_left.mp
    (le_sup_right.trans (pair_sup_zpowers_le_normalizer_residualOddCore ht))

public theorem residualCommutator_odd [Finite G] (ht : PFAppendixIII.IsInvolution t) :
    Odd (Nat.card (residualCommutator M t)) := by
  exact Nat.coprime_two_left.mp
    ((residualOddCore_odd (M := M) (t := t)).coprime_two_left.of_dvd_right
      (card_dvd_of_le (residualCommutator_le_oddCore ht)))

public theorem zpowers_le_normalizer_residualCommutator :
    zpowers t ≤ normalizer (residualCommutator M t : Set G) :=
  normalizer_commutator_ge_right _ _

/-- The repeated-commutator identity is proved from oddness, not assumed. -/
public theorem residualCommutator_idempotent [Finite G] (ht : PFAppendixIII.IsInvolution t) :
    ⁅residualCommutator M t, zpowers t⁆ = residualCommutator M t := by
  change ⁅⁅residualOddCore M t, zpowers t⁆, zpowers t⁆ = ⁅residualOddCore M t, zpowers t⁆
  rw [zpowers_eq_closure]
  apply commutator_closure_coprime_idempotent
  · rw [← zpowers_eq_closure]
    exact le_sup_right.trans (pair_sup_zpowers_le_normalizer_residualOddCore ht)
  · intro a ha
    have he : a = t := Set.mem_singleton_iff.mp ha
    subst a
    rw [orderOf_eq_prime ht.sq_eq_one ht.ne_one]
    exact (residualOddCore_odd (M := M) (t := t)).coprime_two_left

/-- Fixed-centralizer commutators also satisfy the repeated identity. -/
public theorem residualFixedCommutator_idempotent [Finite G] (ht : PFAppendixIII.IsInvolution t)
    {w : G} (hwt : Commute w t) :
    ⁅⁅residualCommutator M t ⊓ centralizer ({w} : Set G), zpowers t⁆, zpowers t⁆ =
      ⁅residualCommutator M t ⊓ centralizer ({w} : Set G), zpowers t⁆ := by
  have hn : zpowers t ≤ normalizer
      ((residualCommutator M t ⊓ centralizer ({w} : Set G)) : Set G) := by
    apply (le_inf zpowers_le_normalizer_residualCommutator ?_).trans
      inf_normalizer_le_normalizer_inf
    exact (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hwt.symm.eq)).trans
      (centralizer ({w} : Set G)).le_normalizer
  rw [zpowers_eq_closure]
  apply commutator_closure_coprime_idempotent
  · rw [← zpowers_eq_closure]
    exact hn
  · intro a ha
    have he : a = t := Set.mem_singleton_iff.mp ha
    subst a
    rw [orderOf_eq_prime ht.sq_eq_one ht.ne_one]
    exact (residualCommutator_odd (M := M) ht).coprime_two_left.of_dvd_right
      (card_dvd_of_le inf_le_left)

/-- Any two-group in `D⟨t⟩` has an invariant Sylow subgroup of the odd core,
with conjugacy controlled by the actual ambient centralizer. -/
public theorem residualOddCore_sylow_control [Finite G]
    (ht : PFAppendixIII.IsInvolution t) (A : Subgroup G) (hA : IsPGroup 2 A)
    (hAD : A ≤ residualPairStabilizer M t ⊔ zpowers t)
    (p : ℕ) [Fact p.Prime] :
    let : MulDistribMulAction A (residualOddCore M t) :=
      conjMulDistribMulActionOfLeNormalizer A (residualOddCore M t)
        (hAD.trans (pair_sup_zpowers_le_normalizer_residualOddCore ht))
    ∃ P : Sylow p (residualOddCore M t),
      IsInvariant A (residualOddCore M t) (P : Subgroup (residualOddCore M t)) ∧
      ∀ R : Subgroup (residualOddCore M t), IsPGroup p R →
        IsInvariant A (residualOddCore M t) R →
        ∃ c : residualOddCore M t, (c : G) ∈ centralizer (A : Set G) ∧
          R.map (MulAut.conj c).toMonoidHom ≤ P := by
  let : MulDistribMulAction A (residualOddCore M t) :=
    conjMulDistribMulActionOfLeNormalizer A (residualOddCore M t)
      (hAD.trans (pair_sup_zpowers_le_normalizer_residualOddCore ht))
  obtain ⟨P, hP, hcontrol⟩ := Theory.GroupAction.exists_invariant_sylow_fixed_control
    hA (residualOddCore_odd (M := M) (t := t)) p
  refine ⟨P, hP, ?_⟩
  intro R hR hRI
  obtain ⟨c, hc, hle⟩ := hcontrol R hR hRI
  refine ⟨c, ?_, hle⟩
  intro a ha
  have he := congrArg Subtype.val (hc ⟨a, ha⟩)
  change a * (c : G) * a⁻¹ = c at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The actor obtained by adjoining `t` to a commuting elementary four
is elementary abelian. The outside condition is needed only for its order. -/
public theorem residualFourActor_elementary
    (ht : PFAppendixIII.IsInvolution t) (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWt : W ≤ centralizer ({t} : Set G)) :
    IsElementaryAbelian 2 (W ⊔ zpowers t : Subgroup G) := by
  let := IsElementaryAbelian.zpowers_of_pow_eq_one ht.sq_eq_one
  apply IsElementaryAbelian.sup_of_le_centralizer
  apply zpowers_le.mpr
  intro w hw
  exact mem_centralizer_singleton_iff.mp (hWt hw)

/-- In Proposition 16.5, `W ≤ D ≤ M` and `t ∉ M` make the actor an eight-group. -/
public theorem residualFourActor_card [Finite G]
    (ht : PFAppendixIII.IsInvolution t) (htM : t ∉ M) (W : Subgroup G)
    (hW : Nat.card W = 4) (hWD : W ≤ residualPairStabilizer M t)
    (hWt : W ≤ centralizer ({t} : Set G)) :
    Nat.card (W ⊔ zpowers t : Subgroup G) = 8 := by
  have htC : t ∈ centralizer (W : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hWt hw)
  rw [card_sup_zpowers_of_normalizing_involution W t ht.sq_eq_one
    (fun h => htM (hWD h).1) (centralizer_le_normalizer W htC), hW]

/-- GLS4, Chapter 2, Lemma 16.1, for the actual residual commutator.
Only K, rather than the whole odd core, is required to be normalized by W. -/
public theorem residualCommutator_four_generation [Finite G]
    (ht : PFAppendixIII.IsInvolution t) (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (hWK : W ≤ normalizer (residualCommutator M t))
    (hWt : W ≤ centralizer ({t} : Set G)) :
    residualCommutator M t = ⨆ (w : W) (_ : (w : G) ≠ 1),
      ⁅residualCommutator M t ⊓ centralizer ({(w : G)} : Set G), zpowers t⁆ := by
  exact commutator_eq_iSup_centralizer_commutators_of_four
    (residualOddCore M t) residualOddCore_odd t
    (orderOf_eq_prime ht.sq_eq_one ht.ne_one)
    ((le_sup_right.trans (pair_sup_zpowers_le_normalizer_residualOddCore ht)) (mem_zpowers t))
    W hW hWK hWt

/-- Section 3.5 places the commutator of D inside its relative odd core.
The two-point stabilizer itself may have even order. -/
public theorem residualPair_commutator_le_oddCore [Finite G] {Z : Set G}
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M) :
    ⁅residualPairStabilizer M t, zpowers t⁆ ≤ residualOddCore M t := by
  have hi := h.involutions t ht
  have hmove : t • (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk 1 := by
    intro he
    apply htM
    exact (baseCoset_stabilizer M) ▸ (MulAction.mem_stabilizer_iff.mpr he)
  have heq : residualPairStabilizer M t =
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
        MulAction.stabilizer G (t • (QuotientGroup.mk 1 : G ⧸ M)) := by
    rw [baseCoset_stabilizer]
    have hs : MulAction.stabilizer G (t • (QuotientGroup.mk 1 : G ⧸ M)) =
        rightConjugate M t := by
      simpa [MulAction.Quotient.smul_mk, smul_eq_mul, hi.inv_eq_self] using
        conjugateCoset_stabilizer M t
    rw [hs]
    rfl
  exact (sectionThreeLocal_of_productDisconnected h).swapping_core t ht
    (QuotientGroup.mk 1) hmove (residualPairStabilizer M t) heq.le
    (involution_mem_normalizer_residualPairStabilizer hi)

/-- K is normal relative to D, as used when W is chosen inside D in 16.5. -/
public theorem residualPair_le_normalizer_residualCommutator [Finite G] {Z : Set G}
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M) :
    residualPairStabilizer M t ≤ normalizer (residualCommutator M t) := by
  rw [residualCommutator_eq_pair_commutator h ht htM]
  exact normalizer_commutator_ge_left _ _

public theorem residualCommutator_normal_in_pair [Finite G] {Z : Set G}
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M) :
    ((residualCommutator M t).subgroupOf (residualPairStabilizer M t)).Normal :=
  normal_subgroupOf_of_le_normalizer (residualPair_le_normalizer_residualCommutator h ht htM)

variable [Finite G] {Z : Set G}

/-- The generation lemma at the actual four-subgroup of D used in 16.5;
relative normality supplies its normalizer hypothesis. -/
public theorem residualPair_four_generation
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t) (hWt : W ≤ centralizer ({t} : Set G)) :
    residualCommutator M t = ⨆ (w : W) (_ : (w : G) ≠ 1),
      ⁅residualCommutator M t ⊓ centralizer ({(w : G)} : Set G), zpowers t⁆ :=
  residualCommutator_four_generation (h.involutions t ht) W hW
    (hWD.trans (residualPair_le_normalizer_residualCommutator h ht htM)) hWt

/-- A subgroup of D generated by t-commutators lies in its odd core. -/
public theorem residualPair_full_commutator_le_oddCore
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M)
    (Q : Subgroup G) (hQD : Q ≤ residualPairStabilizer M t)
    (hQ : ⁅Q, zpowers t⁆ = Q) : Q ≤ residualOddCore M t := by
  rw [← hQ]
  exact (commutator_mono hQD le_rfl).trans (residualPair_commutator_le_oddCore h ht htM)

/-- The actual eight-group actor, invariant Sylow, fixed conjugator, and
operator-preserving embedding in the source Proposition 16.5. -/
public theorem residualFourActor_sylow_fixed_embedding
    (h : IsProductDisconnected Z M) (ht : t ∈ Z) (htM : t ∉ M)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t) (hWt : W ≤ centralizer ({t} : Set G))
    (p : ℕ) [Fact p.Prime] :
    let A := W ⊔ zpowers t
    let := residualFourActor_elementary (h.involutions t ht) W hWt
    Nat.card A = 8 ∧ ∃ P : Sylow p (residualOddCore M t),
      let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
      ∃ hAP : A ≤ normalizer P₁,
        ∀ (Q : Subgroup G), Q ≤ residualPairStabilizer M t → IsPGroup p Q →
          ∀ (hAQ : A ≤ normalizer Q) (w : G) (hw : w ∈ A),
            Q ≤ centralizer ({w} : Set G) → ⁅Q, zpowers t⁆ = Q →
            let Rw := OddInvolutionFrattini.Rw P₁ t w
            let : MulDistribMulAction A Q := conjMulDistribMulActionOfLeNormalizer A Q hAQ
            let : MulDistribMulAction A Rw := conjMulDistribMulActionOfLeNormalizer A Rw
              (OddInvolutionFrattini.normalizes_Rw P₁ A hAP
                ((show zpowers t ≤ A from le_sup_right) (mem_zpowers t)) hw)
            ∃ c : residualOddCore M t, (c : G) ∈ centralizer (A : Set G) ∧
              Q.map (MulAut.conj (c : G)).toMonoidHom ≤ Rw ∧
              ∃ f : Q →* Rw, Function.Injective f ∧
                (∀ x : Q, (f x : G) = (c : G) * x * (c : G)⁻¹) ∧
                ∀ (a : A) (x : Q), f (a • x) = a • f x := by
  let A := W ⊔ zpowers t
  let := residualFourActor_elementary (h.involutions t ht) W hWt
  have hAD : A ≤ residualPairStabilizer M t ⊔ zpowers t := sup_le_sup_right hWD _
  have htA : t ∈ A := (show zpowers t ≤ A from le_sup_right) (mem_zpowers t)
  obtain ⟨P, hAP, hc⟩ := Theory.GroupAction.exists_invariant_sylow_ambient_fixed_control
    (residualOddCore M t) A residualOddCore_odd (IsElementaryAbelian.isPGroup 2 A)
    (hAD.trans (pair_sup_zpowers_le_normalizer_residualOddCore (h.involutions t ht))) p
  refine ⟨residualFourActor_card (h.involutions t ht) htM W hW hWD hWt, P, hAP, ?_⟩
  intro Q hQD hQp hAQ w hw hQw hQ
  dsimp only
  obtain ⟨c, hcA, hQP⟩ := hc Q (residualPair_full_commutator_le_oddCore h ht htM Q hQD hQ)
    hQp hAQ
  have hfix (a : G) (ha : a ∈ A) : (MulAut.conj (c : G)) a = a := by
    change (c : G) * a * (c : G)⁻¹ = a
    rw [← hcA a ha, mul_inv_cancel_right]
  refine ⟨c, hcA, ?_, ?_⟩
  · exact map_le_fixed_commutator_of_full_commutator _ Q t w (MulAut.conj (c : G))
      (hfix t htA) (hfix w hw) hQP hQw hQ
  · exact Theory.GroupAction.equivariant_embedding_fixed_commutator_of_conjugate_le
      A _ Q hAQ htA hw hcA hQP hQw hQ
      (OddInvolutionFrattini.normalizes_Rw _ A hAP htA hw)

/-- The Frattini passage for the actual mapped invariant Sylow of the residual odd core.
The normalization premise is supplied by `residualFourActor_sylow_fixed_embedding`. -/
public theorem residualFourSylow_frattini
    (ht : PFAppendixIII.IsInvolution t) (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWt : W ≤ centralizer ({t} : Set G)) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (P : Sylow p (residualOddCore M t))
    (hAP : W ⊔ zpowers t ≤ normalizer
      ((P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype)) :
    let A := W ⊔ zpowers t
    let := residualFourActor_elementary ht W hWt
    let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
    let R := OddInvolutionFrattini.R P₁ t
    let htA : t ∈ A := (show zpowers t ≤ A from le_sup_right) (mem_zpowers t)
    let hAR := OddInvolutionFrattini.normalizes_R P₁ A hAP htA
    R ≤ residualCommutator M t ∧ IsPGroup p R ∧
      ⁅R, zpowers t⁆ = R ∧
      (∀ q : R ⧸ frattini R,
        OddInvolutionFrattini.quotientConjugation A R hAR ⟨t,htA⟩ q = q⁻¹) ∧
      (∀ (w : G) (hw : w ∈ A),
        let Rw := OddInvolutionFrattini.Rw P₁ t w
        A ≤ normalizer Rw ∧ Rw ≤ R ∧ ⁅Rw, zpowers t⁆ = Rw ∧
          (Rw.subgroupOf R).map (QuotientGroup.mk' (frattini R)) =
            MulAut.fixedSubgroup (OddInvolutionFrattini.quotientConjugation A R hAR ⟨w,hw⟩)) ∧
      (∀ a : A,
        (MulAut.fixedSubgroup (OddInvolutionFrattini.conjugation A R hAR a)).map
          (QuotientGroup.mk' (frattini R)) =
            MulAut.fixedSubgroup (OddInvolutionFrattini.quotientConjugation A R hAR a)) ∧
      (¬ IsCyclic R → ¬ IsCyclic (R ⧸ frattini R)) ∧
      (∀ a : A, OddInvolutionFrattini.quotientConjugation A R hAR a = 1 →
        R ≤ centralizer ({(a : G)} : Set G)) := by
  let A := W ⊔ zpowers t
  let := residualFourActor_elementary ht W hWt
  let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
  let R := OddInvolutionFrattini.R P₁ t
  have htA : t ∈ A := (show zpowers t ≤ A from le_sup_right) (mem_zpowers t)
  have hPp : IsPGroup p P₁ := P.isPGroup'.map _
  have hRp : IsPGroup p R := hPp.of_injective
    (inclusion (OddInvolutionFrattini.r_le P₁ (hAP htA))) (inclusion_injective _)
  have hRod : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact hp.pow
  have ha2 (a : A) : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 A) a
  refine ⟨commutator_mono (map_subtype_le _) le_rfl, hRp,
    OddInvolutionFrattini.repeated_commutator_of_isPGroup P₁ hPp hp (hAP htA) ht,
    OddInvolutionFrattini.inverts_frattini_quotient P₁ A hPp hAP htA ht, ?_, ?_,
    OddInvolutionFrattini.noncyclic_frattini_quotient, ?_⟩
  · intro w hw
    exact ⟨OddInvolutionFrattini.normalizes_Rw P₁ A hAP htA hw,
      OddInvolutionFrattini.rw_le P₁ t w,
      OddInvolutionFrattini.repeated_rw_commutator P₁ A hPp hp hAP htA hw ht,
      OddInvolutionFrattini.image_rw_eq_fixed P₁ A hPp hp hAP htA hw ht⟩
  · intro a
    exact OddInvolutionFrattini.fixed_frattini_map A R
      (OddInvolutionFrattini.normalizes_R P₁ A hAP htA) hRod a (ha2 a)
  · intro a hq
    exact OddInvolutionFrattini.centralizes_of_quotientConjugation_eq_one A R hRp hp
      (OddInvolutionFrattini.normalizes_R P₁ A hAP htA) a (ha2 a) hq

/-- At the minimal-counterexample boundary, choose the actual invariant Sylow
and discharge the normalization premise of the Frattini passage. The model
cyclicity arguments and rank contradiction are not hypotheses here. -/
public theorem residualFourActor_exists_frattini_action
    (h : MinimalCounterexample Z M) (ht : t ∈ Z) (htM : t ∉ M)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t) (hWt : W ≤ centralizer ({t} : Set G))
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    let A := W ⊔ zpowers t
    let := residualFourActor_elementary (h.disconnected.involutions t ht) W hWt
    Nat.card A = 8 ∧ ∃ P : Sylow p (residualOddCore M t),
      let P₁ := (P : Subgroup (residualOddCore M t)).map (residualOddCore M t).subtype
      ∃ hAP : A ≤ normalizer P₁,
        let R := OddInvolutionFrattini.R P₁ t
        let htA : t ∈ A := (show zpowers t ≤ A from le_sup_right) (mem_zpowers t)
        let hAR := OddInvolutionFrattini.normalizes_R P₁ A hAP htA
        R ≤ residualCommutator M t ∧ ⁅R, zpowers t⁆ = R ∧
          (∀ q : R ⧸ frattini R,
            OddInvolutionFrattini.quotientConjugation A R hAR ⟨t,htA⟩ q = q⁻¹) ∧
          (∀ (w : G) (hw : w ∈ A),
            ((OddInvolutionFrattini.Rw P₁ t w).subgroupOf R).map
              (QuotientGroup.mk' (frattini R)) =
                MulAut.fixedSubgroup
                  (OddInvolutionFrattini.quotientConjugation A R hAR ⟨w,hw⟩)) ∧
          (¬ IsCyclic R → ¬ IsCyclic (R ⧸ frattini R)) ∧
          (∀ a : A, OddInvolutionFrattini.quotientConjugation A R hAR a = 1 →
            R ≤ centralizer ({(a : G)} : Set G)) := by
  obtain ⟨hcard, P, hAP, _⟩ := residualFourActor_sylow_fixed_embedding
    h.disconnected ht htM W hW hWD hWt p
  obtain ⟨hRK, _, hrep, hinv, hfixed, _, hnoncyclic, htrivial⟩ :=
    residualFourSylow_frattini (h.disconnected.involutions t ht) W hWt hp P hAP
  exact ⟨hcard, P, hAP, hRK, hrep, hinv, fun w hw => (hfixed w hw).2.2.2,
    hnoncyclic, htrivial⟩

end BenderSuzuki.ZD
