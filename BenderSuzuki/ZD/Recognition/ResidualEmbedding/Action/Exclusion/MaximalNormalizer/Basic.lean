module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.FirstStage
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# Distinguished maximal normalizers: selection and the final Sylow argument

The admissible family keeps the original prime and distinguished involution
fixed, and requires the swapping involution to belong to the distinguished set.
Finite maximization is independent of the construction of an initial member.
Once the local ZJ argument supplies an admissible conjugate of
`Omega₁(Z(J(R)))`, maximality and the normalizer condition for p-groups force
that conjugate of `R` to be Sylow in the two-point stabilizer.

The structures below are explicit intermediate proof obligations. They do not
assert that the geometry, (7D), or the local normalizer argument has been proved.
In particular no oddness of the triple stabilizer or ambient strong embedding
is assumed. Source: GLS, Volume 4, Chapter 2, (7D) and the proof of Proposition
7.1 following Lemma 7.11. The normalizer-growth proof adapts the elementary
argument in `BenderSuzuki.SE.Section7Final`.
-/

noncomputable section

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The actual normalizer inside the two-point stabilizer. -/
@[expose] public def actionNormalizerInD (M : Subgroup G)
    (beta : G ⧸ M) (Q : Subgroup G) : Subgroup G :=
  theorem4bSection7D M beta ⊓ Subgroup.normalizer (Q : Set G)

/-- Conditions (a,b) of the source maximal choice, with `t ∈ Z`. -/
public structure ActionAdmissibleQ (d : ActionCounterexample Z M)
    (beta : G ⧸ M) where
  Q : Subgroup G
  hQp : IsPGroup d.p Q
  hQne : Q ≠ ⊥
  hQE : Q ≤ theorem4bSection7E M d.z beta
  hzNormQ : d.z ∈ Subgroup.normalizer (Q : Set G)
  t : G
  htZ : t ∈ Z
  htBase : t • (QuotientGroup.mk 1 : G ⧸ M) = beta
  htNormQ : t ∈ Subgroup.normalizer (Q : Set G)
  P₁ : Subgroup G
  hP₁sylow : theorem4bIsSylowSubgroupOf d.p P₁ (theorem4bSection7E M d.z beta)
  hP₁NormQ : P₁ ≤ Subgroup.normalizer (Q : Set G)
  htNormP₁ : t ∈ Subgroup.normalizer (P₁ : Set G)

/-- Finite maximization, conditional only on nonemptiness of the admissible
family. Every comparison uses exactly the original `p` and `z`. -/
public theorem action_exists_maximal_admissibleQ
    (d : ActionCounterexample Z M) (beta : G ⧸ M)
    (hne : Nonempty (ActionAdmissibleQ d beta)) :
    ∃ a : ActionAdmissibleQ d beta, ∀ b : ActionAdmissibleQ d beta,
      (Nat.card (actionNormalizerInD M beta b.Q)).factorization d.p ≤
        (Nat.card (actionNormalizerInD M beta a.Q)).factorization d.p := by
  classical
  obtain ⟨a₀⟩ := hne
  let S := {Q : Subgroup G // ∃ a : ActionAdmissibleQ d beta, Q = a.Q}
  let : Fintype S := Fintype.ofFinite S
  let q₀ : S := ⟨a₀.Q, ⟨a₀, rfl⟩⟩
  have hs : (Finset.univ : Finset S).Nonempty := ⟨q₀, by simp⟩
  let score : S → ℕ := fun q =>
    (Nat.card (actionNormalizerInD M beta q.1)).factorization d.p
  obtain ⟨q, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset S) score hs
  obtain ⟨a, hqa⟩ := q.2
  refine ⟨a, ?_⟩
  intro b
  have hb := hmax (⟨b.Q, ⟨b, rfl⟩⟩ : S) (by simp)
  simpa [score, hqa] using hb

/-- The input to the local normalizer argument. The triple bound is the
p-subgroup consequence of transitivity on distinguished triples; `sevenD`
concerns the commutator, not oddness of `E`. -/
public structure ActionMaximalNormalizerData (d : ActionCounterexample Z M)
    (beta : G ⧸ M) where
  chosen : ActionAdmissibleQ d beta
  maximal : ∀ b : ActionAdmissibleQ d beta,
    (Nat.card (actionNormalizerInD M beta b.Q)).factorization d.p ≤
      (Nat.card (actionNormalizerInD M beta chosen.Q)).factorization d.p
  R : Subgroup G
  hRsylow : theorem4bIsSylowSubgroupOf d.p R
    (actionNormalizerInD M beta chosen.Q)
  hP₁R : chosen.P₁ ≤ R
  htNormR : chosen.t ∈ Subgroup.normalizer (R : Set G)
  hP₁card_lt_R : Nat.card chosen.P₁ < Nat.card R
  sevenD : ∀ S : Subgroup G,
    theorem4bIsSylowSubgroupOf d.p S (theorem4bSection7E M d.z beta) →
      d.p ∣ Nat.card (⁅Subgroup.zpowers d.z, S⁆ : Subgroup G)
  triple_bound : ∀ w ∈ Z, ∀ gamma delta : G ⧸ M,
    w • gamma = gamma → gamma ≠ delta → ∀ P : Subgroup G,
    IsPGroup d.p P →
    P ≤ (MulAction.stabilizer G gamma ⊓ MulAction.stabilizer G delta) ⊓
      MulAction.stabilizer G (w • delta) →
    Nat.card P ≤ Nat.card chosen.P₁

/-- The normalizer used in Lemma 7.10 is proper: otherwise the nontrivial
subgroup `Q ≤ M` would be normal in the simple ambient group. -/
public theorem ActionAdmissibleQ.normalizer_ne_top
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (a : ActionAdmissibleQ d beta) :
    Subgroup.normalizer (a.Q : Set G) ≠ ⊤ := by
  intro htop
  have hnormal : a.Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases r.simple.eq_bot_or_eq_top_of_normal a.Q hnormal with hbot | hQtop
  · exact a.hQne hbot
  · have hQM : a.Q ≤ M := a.hQE.trans (inf_le_left.trans inf_le_left)
    exact h.proper (top_unique (hQtop ▸ hQM))

/-- Its distinguished swapping involution shows that `N_G(Q)` is not
contained in the base stabilizer. -/
public theorem ActionAdmissibleQ.normalizer_not_le
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (a : ActionAdmissibleQ d beta) (hne : beta ≠ QuotientGroup.mk 1) :
    ¬ Subgroup.normalizer (a.Q : Set G) ≤ M := by
  intro hle
  have htM := hle a.htNormQ
  have hfix : a.t • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1 := by
    apply MulAction.mem_stabilizer_iff.mp
    rwa [baseCoset_stabilizer M]
  exact hne (a.htBase.symm.trans hfix)

/-- The eligible local strong embedding is inside the distinguished closure
in `N_G(Q)`, never inside the whole ambient group. All eligibility conditions
are discharged using the admissible subgroup. -/
public theorem ActionAdmissibleQ.local_embedding
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (a : ActionAdmissibleQ d beta) (hne : beta ≠ QuotientGroup.mk 1) :
    let N := Subgroup.normalizer (a.Q : Set G)
    IsStronglyEmbedded ((M.comap N.subtype).comap
      (Subgroup.closure (N.subtype ⁻¹' Z)).subtype) := by
  exact r.local_embedding _ (a.normalizer_ne_top h r) (a.normalizer_not_le hne)
    ⟨d.z, d.hzZ, a.hzNormQ, d.hzM⟩

/-- Strict inequality in Proposition 7.9 excludes every `z`-invariant
Sylow subgroup of `D`, before the maximal-normalizer construction. -/
public theorem action_no_invariant_sylow_of_firstStage
    (h : IsProductDisconnected Z M) (hc : ActionCounting Z M)
    (d : ActionMaximalCounterexample Z M)
    (h64 : ActionCorollary64 d.data)
    (h72 : Theorem4bProposition72 d.data.toTheorem4bSixA)
    {beta : G ⧸ M} (hb : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1) :
    ¬ ∃ R : Subgroup G,
      theorem4bIsSylowSubgroupOf d.data.p R (theorem4bSection7D M beta) ∧
        d.data.z ∈ Subgroup.normalizer (R : Set G) := by
  intro hs
  have heq := (d.invariant_sylow_iff h hc hb hne).mp hs
  exact (ne_of_lt (d.invertedCard_lt_primeShare h hc h64 h72)) heq

/-- A proper p-subgroup of a Sylow subgroup gains p-part in its normalizer,
with all normalizers and Sylow subgroups relative to `D`. -/
public theorem action_factorization_lt_normalizer_of_not_sylow
    {p : ℕ} (hp : p.Prime) {P D : Subgroup G}
    (hPp : IsPGroup p P) (hPD : P ≤ D)
    (hnot : ¬ theorem4bIsSylowSubgroupOf p P D) :
    (Nat.card P).factorization p <
      (Nat.card (D ⊓ Subgroup.normalizer (P : Set G) : Subgroup G)).factorization p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let PD : Subgroup D := P.subgroupOf D
  have hPDp : IsPGroup p PD :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPD).symm
  obtain ⟨S, hPDleS⟩ := hPDp.exists_le_sylow
  have hPDltS : PD < (S : Subgroup D) := by
    refine lt_of_le_of_ne hPDleS ?_
    intro heq
    apply hnot
    refine ⟨S, ?_⟩
    rw [← heq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPD]
  have hlt := External.hkt_factorization_lt_ambient_normalizer_of_lt_sylow S hPDltS
  have hcardPD : Nat.card PD = Nat.card P := natCard_subgroupOf_eq P D hPD
  have hnorm : Subgroup.normalizer (PD : Set D) =
      (Subgroup.normalizer (P : Set G)).subgroupOf D :=
    (Subgroup.subgroupOf_normalizer_eq hPD).symm
  rw [hnorm] at hlt
  let ND : Subgroup D := (Subgroup.normalizer (P : Set G)).subgroupOf D
  have hmapND : ND.map D.subtype = Subgroup.normalizer (P : Set G) ⊓ D := by
    exact Subgroup.subgroupOf_map_subtype _ _
  have hcardMap : Nat.card (ND.map D.subtype) = Nat.card ND :=
    Subgroup.card_map_of_injective D.subtype_injective
  have hcardND : Nat.card ND =
      Nat.card (D ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) := by
    rw [hmapND, inf_comm] at hcardMap
    exact hcardMap.symm
  change (Nat.card PD).factorization p < (Nat.card ND).factorization p at hlt
  rwa [hcardPD, hcardND] at hlt

omit [Finite G] in
private theorem conjBy_eq_self_of_mem (H : Subgroup G) {g : G} (hg : g ∈ H) :
    H.conjBy g = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
  · intro hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg
    · simp [MulAut.conj_apply, mul_assoc]

/-- The last normalizer chain in the source. The local argument must supply
an admissible `Omega₁(Z(J(R^x)))`; the Sylow conclusion is proved here. -/
public theorem action_sylow_of_admissible_conjugate
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta)
    {x : G} (hx : x ∈ theorem4bSection7D M beta)
    (a : ActionAdmissibleQ d beta)
    (ha : a.Q = corollary64Z ⟨d.p, d.hp⟩ (q.R.conjBy x)) :
    theorem4bIsSylowSubgroupOf d.p (q.R.conjBy x) (theorem4bSection7D M beta) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let D := theorem4bSection7D M beta
  let Rx := q.R.conjBy x
  let NDR := D ⊓ Subgroup.normalizer (Rx : Set G)
  let NDQ := actionNormalizerInD M beta q.chosen.Q
  let NDA := actionNormalizerInD M beta a.Q
  obtain ⟨S, hS⟩ := q.hRsylow
  have hRp : IsPGroup d.p q.R := by
    rw [hS]
    exact S.isPGroup'.map _
  have hRD : q.R ≤ D := by
    rw [hS]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hRxp : IsPGroup d.p Rx := hRp.map (MulAut.conj x).toMonoidHom
  have hRxD : Rx ≤ D := by
    calc
      Rx ≤ D.conjBy x := Subgroup.map_mono hRD
      _ = D := conjBy_eq_self_of_mem D hx
  have hnorm : Subgroup.normalizer (Rx : Set G) ≤
      Subgroup.normalizer (a.Q : Set G) := by
    rw [ha]
    exact normalizer_le_normalizer_corollary64Z Rx
  have hle : NDR ≤ NDA := inf_le_inf_left D hnorm
  have hfac : (Nat.card NDR).factorization d.p ≤
      (Nat.card NDQ).factorization d.p :=
    (Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hle) Nat.card_pos.ne' Nat.card_pos.ne').trans
      (q.maximal a)
  have hcard : Nat.card q.R = Nat.card (S : Subgroup NDQ) := by
    rw [hS]
    exact Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (actionNormalizerInD M beta q.chosen.Q))
  have hRfac : (Nat.card q.R).factorization d.p =
      (Nat.card NDQ).factorization d.p := by
    rw [hcard]
    exact section8_factorization_card_sylow S
  have hRxcard : Nat.card Rx = Nat.card q.R :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  by_contra hnot
  have hgrowth := action_factorization_lt_normalizer_of_not_sylow d.hp hRxp hRxD hnot
  have hback : (Nat.card NDR).factorization d.p ≤ (Nat.card Rx).factorization d.p := by
    rw [hRxcard, hRfac]
    exact hfac
  exact (not_lt_of_ge hback) hgrowth

/-- Conditional final assembly. Construction of the admissible conjugate
remains the local normalizer/quotient/ZJ obligation, separate from the final
Sylow argument above. -/
public theorem actionFinalConfiguration_of_admissible_conjugate
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hb : beta ∈ d.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1)
    (htheta : corollary64Theta d.p (theorem4bSection7D M beta) = ⊥)
    (q : ActionMaximalNormalizerData d beta)
    (hconj : ∃ x ∈ theorem4bSection7E M d.z beta,
      ∃ a : ActionAdmissibleQ d beta,
        a.Q = corollary64Z ⟨d.p, d.hp⟩ (q.R.conjBy x)) :
    ActionFinalConfiguration d := by
  obtain ⟨x, hx, a, ha⟩ := hconj
  refine ⟨beta, hb, hne, htheta, q.R.conjBy x,
    action_sylow_of_admissible_conjugate d q hx.1 a ha, ?_⟩
  rw [← ha]
  exact a.hzNormQ

end BenderSuzuki.ZD
