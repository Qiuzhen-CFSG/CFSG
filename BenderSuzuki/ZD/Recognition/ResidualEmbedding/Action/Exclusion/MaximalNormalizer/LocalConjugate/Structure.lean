module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Lemma710
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.LocalConjugate.Quotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import BenderSuzuki.SE.InvolutionCore
public import BenderSuzuki.SE.PStability
public import BenderSuzuki.SE.Borel

/-!
# Structure of the distinguished local normalizer

For N = N_G(Q), this module uses exactly the distinguished closure L inside N
and the canonical quotient-defined subgroups M₁ and M₂. Lemma 7.10 forces
L to have two-rank at least two, so minimality supplies the full ZD structure.
Its odd core lies in M₁ and, by normality, fixes all three points defining E.
Local strong embedding eliminates the central involution factor and identifies
the actual quotient and Borel needed to place z in M₂.

Conjugation by R preserves the kernel and characteristic subgroup in (7F).
The resulting product M₂R is solvable with abelian Sylow two-subgroups.
Condition (7D) and local involution conjugacy identify its p-prime core with
theta(M₂); the quotient and Sylow intersections show that R is Sylow there.
The nontrivial normal subgroup Q supplies its nontrivial p-core.

Source: GLS, Volume 4, Chapter 2, Lemmas 7.10–7.11 and (7E)–(7G),
`refs/KGroup/GLS4/Chapter2.tex`, lines 1200–1257. The elementary quotient,
normalization and core arguments adapt `BenderSuzuki.SE.Section7Final` to
the distinguished local closure. The final theorem provides all inputs to
the independent ZJ factorization.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem sylow_le {X : Type*} [Group X] {p : ℕ} {P H : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P H) : P ≤ H := by
  obtain ⟨S, rfl⟩ := hP
  exact Subgroup.map_subtype_le _

private theorem sylow_isPGroup {X : Type*} [Group X] {p : ℕ} {P H : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P H) : IsPGroup p P := by
  obtain ⟨S, rfl⟩ := hP
  exact S.isPGroup'.map H.subtype

private theorem normal_rank_one_involution_central
    {N : Type*} [Group N] [Finite N] (L : Subgroup N) [L.Normal]
    (hr : ¬ TwoRankAtLeastTwo L) {z : N} (hz : IsInvolution z) (hzL : z ∈ L) :
    QuotientGroup.mk' (pPrimeCore 2 N) z ∈ Subgroup.center (N ⧸ pPrimeCore 2 N) := by
  let f := QuotientGroup.mk' (pPrimeCore 2 N)
  have hcore := pPrimeCore_map_subtype_le_pPrimeCore_of_normal (p := 2) L
  have hk : pPrimeCore 2 L ≤ (f.comp L.subtype).ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (x : N)).mpr
      (hcore (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  let ff := QuotientGroup.lift (pPrimeCore 2 L) (f.comp L.subtype) hk
  apply Subgroup.mem_center_iff.mpr
  intro g
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 N) g
  let zL : L := ⟨z, hzL⟩
  let vL : L := ⟨n * z * n⁻¹, (inferInstance : L.Normal).conj_mem z hzL n⟩
  have hv : IsInvolution vL := IsInvolution.subtype
    (IsInvolution.map_of_injective hz (MulAut.conj n).toMonoidHom (MulAut.conj n).injective) vL.property
  have he := involution_images_eq_of_not_twoRank hr hv (IsInvolution.subtype hz hzL)
  have hfe : f (n * z * n⁻¹) = f z := congrArg ff he
  have heq : f n * f z * (f n)⁻¹ = f z := by
    simpa only [map_mul, map_inv] using hfe
  exact (mul_inv_eq_iff_eq_mul.mp heq)

omit [Finite G] in
/-- The distinguished closure is normal inside its actual local normalizer. -/
public theorem actionLocalNCore_normal (h : IsProductDisconnected Z M) (Q : Subgroup G) :
    (actionLocalNCore Z Q).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro g _ z hz
  exact Subgroup.subset_closure (h.invariant (g : G) (z : G) hz)

/-- Lemma 7.10 forces an elementary four in the distinguished closure itself. -/
public theorem actionLocalNCore_twoRank (h : IsProductDisconnected Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    TwoRankAtLeastTwo (actionLocalNCore Z q.chosen.Q) := by
  by_contra hr
  apply action_lemma710_quotient_center h d hne q
  let N := Subgroup.normalizer (q.chosen.Q : Set G)
  let L := actionLocalNCore Z q.chosen.Q
  have : L.Normal := actionLocalNCore_normal h q.chosen.Q
  intro z hz
  exact normal_rank_one_involution_central L hr
    (IsInvolution.subtype (h.involutions z hz) z.property) (Subgroup.subset_closure hz)


/-- Minimality supplies every clause of ZD for the proper normalizer, and rank excludes its first alternative. -/
public theorem actionLocalNCore_structure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    let N := Subgroup.normalizer (q.chosen.Q : Set G)
    StructureConclusion (N.subtype ⁻¹' Z) (M.comap N.subtype) := by
  rcases h.conclusion_subgroup _ (q.chosen.normalizer_ne_top h.disconnected r)
      (q.chosen.normalizer_not_le hne)
      ⟨d.z, d.hzZ, q.chosen.hzNormQ, d.hzM⟩ with hr | hs
  · exact False.elim (hr (actionLocalNCore_twoRank h.disconnected d hne q))
  · exact hs

/-- The odd-core containment needed to identify the pullback kernel in (7F). -/
public theorem actionLocal_oddCore_le_M1
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    pPrimeCore 2 (actionLocalNCore Z q.chosen.Q) ≤ actionLocalM1 Z M q.chosen.Q := by
  obtain ⟨_, _, _, _, _, _, _, _, hO, _⟩ := actionLocalNCore_structure h r d hne q
  exact hO.trans inf_le_left

omit [Finite G] in
/-- The normalizer of Q normalizes the ambient image of its distinguished closure. -/
public theorem actionLocalNCore_normalizer
    (h : IsProductDisconnected Z M) (Q : Subgroup G) :
    let N := Subgroup.normalizer (Q : Set G)
    N ≤ Subgroup.normalizer ((actionLocalNCore Z Q).map N.subtype : Set G) := by
  let N := Subgroup.normalizer (Q : Set G)
  have : (actionLocalNCore Z Q).Normal := actionLocalNCore_normal h Q
  have hh := Subgroup.le_normalizer_map (H := actionLocalNCore Z Q) N.subtype
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hh

omit [Finite G] in
/-- Normality of the closure and characteristicity of its odd core give ambient normalization. -/
public theorem actionLocal_oddCore_normalizer
    (h : IsProductDisconnected Z M) (Q : Subgroup G) :
    let N := Subgroup.normalizer (Q : Set G)
    let L := actionLocalNCore Z Q
    N ≤ Subgroup.normalizer
      ((pPrimeCore 2 L).map (N.subtype.comp L.subtype) : Set G) := by
  let N := Subgroup.normalizer (Q : Set G)
  let L := actionLocalNCore Z Q
  have : L.Normal := actionLocalNCore_normal h Q
  have hnorm : N ≤ Subgroup.normalizer (L.map N.subtype : Set G) :=
    actionLocalNCore_normalizer h Q
  let e : L ≃* L.map N.subtype := L.equivMapOfInjective N.subtype N.subtype_injective
  have hO : (pPrimeCore 2 (L.map N.subtype)).map (L.map N.subtype).subtype =
      (pPrimeCore 2 L).map (N.subtype.comp L.subtype) := by
    rw [← pPrimeCore_map_iso 2 e, Subgroup.map_map]
    rfl
  change N ≤ Subgroup.normalizer
    ((pPrimeCore 2 L).map (N.subtype.comp L.subtype) : Set G)
  rw [← hO]
  exact hnorm.trans (External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
    (L.map N.subtype) (pPrimeCore 2 (L.map N.subtype)))

/-- (7E): the odd core fixes the base point, its image under t, and then its image under z. -/
public theorem actionLocal_oddCore_le_E
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    let N := Subgroup.normalizer (q.chosen.Q : Set G)
    let L := actionLocalNCore Z q.chosen.Q
    (pPrimeCore 2 L).map (N.subtype.comp L.subtype) ≤ theorem4bSection7E M d.z beta := by
  let N := Subgroup.normalizer (q.chosen.Q : Set G)
  let L := actionLocalNCore Z q.chosen.Q
  let O := (pPrimeCore 2 L).map (N.subtype.comp L.subtype)
  have hOM : O ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    exact actionLocal_oddCore_le_M1 h r d hne q hy
  have hObase : O ≤ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) := by
    simpa only [baseCoset_stabilizer] using hOM
  have hn : N ≤ Subgroup.normalizer (O : Set G) :=
    actionLocal_oddCore_normalizer h.disconnected q.chosen.Q
  have hObeta : O ≤ MulAction.stabilizer G beta := by
    rw [← q.chosen.htBase]
    exact theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      (hn q.chosen.htNormQ) hObase
  exact le_inf (le_inf hOM hObeta)
    (theorem4b_le_stabilizer_smul_of_le_stabilizer_of_mem_normalizer
      (hn q.chosen.hzNormQ) hObeta)

private theorem quotient_characteristic_comap_map_mulEquiv
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (U : Subgroup (G ⧸ N)) [U.Characteristic]
    (e : G ≃* G) (hN : N.map e.toMonoidHom = N) :
    (U.comap (QuotientGroup.mk' N)).map e.toMonoidHom =
      U.comap (QuotientGroup.mk' N) := by
  let : (N.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map (inferInstance : N.Normal) e.toMonoidHom e.surjective
  let eQ : (G ⧸ N) ≃* (G ⧸ N) :=
    (quotientMulEquivOfMulEquiv e N).trans
      (QuotientGroup.quotientMulEquivOfEq hN)
  have hUmap : U.map eQ.toMonoidHom = U :=
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : U.Characteristic) eQ
  have heQ_mk (x : G) :
      eQ ((QuotientGroup.mk' N) x) = (QuotientGroup.mk' N) (e x) := by
    change (QuotientGroup.quotientMulEquivOfEq hN)
        (quotientMulEquivOfMulEquiv e N (QuotientGroup.mk x)) =
      QuotientGroup.mk (e x)
    rw [quotientMulEquivOfMulEquiv_mk,
      QuotientGroup.quotientMulEquivOfEq_mk]
  have heQ_symm_mk (x : G) :
      eQ.symm ((QuotientGroup.mk' N) x) =
        (QuotientGroup.mk' N) (e.symm x) := by
    apply eQ.injective
    rw [eQ.apply_symm_apply, heQ_mk]
    simp
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyU : (QuotientGroup.mk' N) y ∈ U := hy
    have heU : eQ ((QuotientGroup.mk' N) y) ∈ U := by
      rw [← hUmap]
      exact Subgroup.mem_map_of_mem eQ.toMonoidHom hyU
    rw [heQ_mk] at heU
    exact heU
  · intro x hx
    have hxU : (QuotientGroup.mk' N) x ∈ U := hx
    have hesU : eQ.symm ((QuotientGroup.mk' N) x) ∈ U := by
      have hUmapSymm : U.map eQ.symm.toMonoidHom = U :=
        Subgroup.characteristic_iff_map_eq.mp
          (inferInstance : U.Characteristic) eQ.symm
      rw [← hUmapSymm]
      exact Subgroup.mem_map_of_mem eQ.symm.toMonoidHom hxU
    apply Subgroup.mem_map.mpr
    refine ⟨e.symm x, ?_, by simp⟩
    rw [heQ_symm_mk] at hesU
    exact hesU



omit [Finite G] in
/-- The canonical subgroup M₂ lies in the normalizer of Q. -/
public theorem actionLocalM2InG_le_normalizer (Q : Subgroup G) :
    actionLocalM2InG Z M Q ≤ Subgroup.normalizer (Q : Set G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
/-- The canonical subgroup M₂ lies in M. -/
public theorem actionLocalM2InG_le_M (Q : Subgroup G) : actionLocalM2InG Z M Q ≤ M := by
  rintro x ⟨n, ⟨l, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
  exact a.property

/-- Conjugation preserving M and the local closure preserves the kernel and the characteristic quotient subgroup in (7F). -/
public theorem actionLocalM2_normalizer (h : IsProductDisconnected Z M) (Q : Subgroup G) :
    M ⊓ Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (actionLocalM2InG Z M Q : Set G) := by
  let N := Subgroup.normalizer (Q : Set G)
  let L := actionLocalNCore Z Q
  let A := actionLocalM1 Z M Q
  let O1 := actionLocalO1 Z M Q
  let U := actionLocalM2Quotient Z M Q
  let B0 := actionLocalM2 Z M Q
  have : L.Normal := actionLocalNCore_normal h Q
  intro n hn
  let nN : N := ⟨n, hn.2⟩
  let eL : L ≃* L := L.normalizerMonoidHom ⟨nN, by
    rw [Subgroup.normalizer_eq_top (H := L)]; trivial⟩
  have heL (l : L) : ((eL l : N) : G) = n * ((l : N) : G) * n⁻¹ := rfl
  have hA : A.map eL.toMonoidHom = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro a ⟨b, hb, rfl⟩
      change ((eL b : N) : G) ∈ M
      rw [heL]
      exact M.mul_mem (M.mul_mem hn.1 hb) (M.inv_mem hn.1)
    · exact le_of_eq (Subgroup.card_map_of_injective (K := A)
        (f := eL.toMonoidHom) eL.injective).symm
  let eA : A ≃* A := (eL.subgroupMap A).trans (MulEquiv.subgroupCongr hA)
  have heA (a : A) : (eA a : L) = eL a := rfl
  have hO1 : O1.map eA.toMonoidHom = O1 := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro a ⟨b, hb, rfl⟩
      change (eA b : L) ∈ pPrimeCore 2 L
      rw [heA, ← pPrimeCore_map_iso 2 eL]
      exact Subgroup.mem_map_of_mem eL.toMonoidHom hb
    · rw [Subgroup.card_map_of_injective eA.injective]
  have hB0 : B0.map eA.toMonoidHom = B0 :=
    quotient_characteristic_comap_map_mulEquiv O1 U eA hO1
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨xN, ⟨xL, ⟨xA, hx, rfl⟩, rfl⟩, rfl⟩
  have hx' : eA xA ∈ B0 := by
    rw [← hB0]
    exact Subgroup.mem_map_of_mem eA.toMonoidHom hx
  have hh : n * (((xA : L) : N) : G) * n⁻¹ = (((eA xA : L) : N) : G) :=
    (heL xA).symm
  change n * (((xA : L) : N) : G) * n⁻¹ ∈ actionLocalM2InG Z M Q
  rw [hh]
  exact ⟨_, ⟨_, ⟨eA xA, hx', rfl⟩, rfl⟩, rfl⟩

/-- The selected R normalizes the actual quotient-defined subgroup M₂. -/
public theorem actionLocal_R_le_normalizer_M2 (h : IsProductDisconnected Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) :
    q.R ≤ Subgroup.normalizer (actionLocalM2InG Z M q.chosen.Q : Set G) := by
  have hR := sylow_le q.hRsylow
  exact (le_inf (hR.trans (inf_le_left.trans inf_le_left))
    (hR.trans inf_le_right)).trans (actionLocalM2_normalizer h q.chosen.Q)

/-- The normal p-subgroup Q of N_D(Q) lies in its selected Sylow subgroup R. -/
public theorem actionLocal_Q_le_R
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) : q.chosen.Q ≤ q.R := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let N := actionNormalizerInD M beta q.chosen.Q
  have hQN : q.chosen.Q ≤ N := le_inf (q.chosen.hQE.trans inf_le_left) Subgroup.le_normalizer
  let QN := q.chosen.Q.subgroupOf N
  have : QN.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr inf_le_right
  have hQNp : IsPGroup d.p QN :=
    q.chosen.hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  obtain ⟨R, hR⟩ := q.hRsylow
  have hQR : QN ≤ (R : Subgroup N) := hQNp.le_sylow_of_normal R
  rw [hR]
  rintro x hx
  exact ⟨⟨x, hQN hx⟩, hQR hx, rfl⟩

/-- The p-core of M₂R contains the nontrivial normal subgroup Q. -/
public theorem actionLocal_pCore_ne_bot
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) :
    pCore d.p ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R) ≠ ⊥ := by
  let H := actionLocalM2InG Z M q.chosen.Q ⊔ q.R
  have hQH : q.chosen.Q ≤ H := (actionLocal_Q_le_R q).trans le_sup_right
  have hHN : H ≤ Subgroup.normalizer (q.chosen.Q : Set G) :=
    sup_le (actionLocalM2InG_le_normalizer q.chosen.Q)
      ((sylow_le q.hRsylow).trans inf_le_right)
  let QH := q.chosen.Q.subgroupOf H
  have : QH.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHN
  have hQHp : IsPGroup d.p QH :=
    q.chosen.hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hQHcore : QH ≤ pCore d.p H := le_sSup ⟨inferInstance, hQHp⟩
  intro hc
  have hbot : QH = ⊥ := bot_unique (hc ▸ hQHcore)
  apply q.chosen.hQne
  rw [← Subgroup.map_subgroupOf_eq_of_le hQH]
  change QH.map H.subtype = ⊥
  rw [hbot, Subgroup.map_bot]


private theorem quotient_sup_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (B R : Subgroup G) [(B.subgroupOf (B ⊔ R)).Normal]
    (hRp : IsPGroup p R) :
    IsPGroup p (↥(B ⊔ R) ⧸ B.subgroupOf (B ⊔ R)) := by
  let H : Subgroup G := B ⊔ R
  let Bsub : Subgroup H := B.subgroupOf H
  let Rsub : Subgroup H := R.subgroupOf H
  have hBH : B ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  let : Bsub.Normal := by
    dsimp [Bsub, H]
    infer_instance
  have hsup : Bsub ⊔ Rsub = ⊤ := by
    apply top_unique
    intro h _hh
    have hxH : (h : G) ∈ H := h.property
    have hmapSup : (Bsub ⊔ Rsub).map H.subtype = H := by
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hBH,
        Subgroup.map_subgroupOf_eq_of_le hRH]
    have hxMap : (h : G) ∈ (Bsub ⊔ Rsub).map H.subtype := by
      rw [hmapSup]
      exact hxH
    rcases Subgroup.mem_map.mp hxMap with ⟨k, hk, hkEq⟩
    have : k = h := Subtype.ext hkEq
    rwa [this] at hk
  let qH : H →* H ⧸ Bsub := QuotientGroup.mk' Bsub
  let rToH : R →* H := Subgroup.inclusion hRH
  let f : R →* H ⧸ Bsub := qH.comp rToH
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective Bsub y
    have hh : h ∈ Bsub ⊔ Rsub := by
      rw [hsup]
      trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hh with
      ⟨b, hb, r, hr, hbr⟩
    let rr : R := ⟨((r : H) : G), hr⟩
    refine ⟨rr, ?_⟩
    change qH r = qH h
    have hqb : qH b = 1 := (QuotientGroup.eq_one_iff b).2 hb
    rw [← hbr, map_mul, hqb, one_mul]
  exact IsPGroup.of_surjective hRp f hf



/-- The canonical equivalence between the relative and ambient realizations of M₂. -/
@[expose] public def actionLocalM2_equiv (Q : Subgroup G) :
    actionLocalM2 Z M Q ≃* actionLocalM2InG Z M Q :=
  (((actionLocalM2 Z M Q).equivMapOfInjective (actionLocalM1 Z M Q).subtype
    (actionLocalM1 Z M Q).subtype_injective).trans
    (((actionLocalM2 Z M Q).map (actionLocalM1 Z M Q).subtype).equivMapOfInjective
      (actionLocalNCore Z Q).subtype (actionLocalNCore Z Q).subtype_injective)).trans
    ((((actionLocalM2 Z M Q).map (actionLocalM1 Z M Q).subtype).map
      (actionLocalNCore Z Q).subtype).equivMapOfInjective
        (Subgroup.normalizer (Q : Set G)).subtype
        (Subgroup.normalizer (Q : Set G)).subtype_injective)

/-- The pullback of the odd core has odd order. -/
public theorem actionLocalO1_odd (Q : Subgroup G) : Odd (Nat.card (actionLocalO1 Z M Q)) := by
  have hle : (actionLocalO1 Z M Q).map (actionLocalM1 Z M Q).subtype ≤
      pPrimeCore 2 (actionLocalNCore Z Q) := Subgroup.map_comap_le _ _
  have hc := (Nat.coprime_two_left.mp (pPrimeCore_coprime_card
    (p := 2) (G := actionLocalNCore Z Q))).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rwa [Subgroup.card_map_of_injective (actionLocalM1 Z M Q).subtype_injective] at hc

omit [Finite G] in
/-- The quotient kernel lies in its full preimage M₂. -/
public theorem actionLocalO1_le_M2 (Q : Subgroup G) : actionLocalO1 Z M Q ≤ actionLocalM2 Z M Q := by
  intro a ha
  change QuotientGroup.mk' (actionLocalO1 Z M Q) a ∈ actionLocalM2Quotient Z M Q
  have he : QuotientGroup.mk' (actionLocalO1 Z M Q) a = 1 :=
    (QuotientGroup.eq_one_iff a).mpr ha
  rw [he]
  exact Subgroup.one_mem _

omit [Finite G] in
/-- The right side of (7F) is a two-group. -/
public theorem actionLocalM2Quotient_isPGroup (Q : Subgroup G) :
    IsPGroup 2 (actionLocalM2Quotient Z M Q) :=
  (pCore_isPGroup.to_subgroup (omega₁ (G := pCore 2
    ((actionLocalM1 Z M Q) ⧸ actionLocalO1 Z M Q)) (p := 2))).map _

omit [Finite G] in
/-- The literal quotient of M₂ by the relative odd kernel is a two-group. -/
public theorem actionLocalM2_internal_quotient_isPGroup (Q : Subgroup G) :
    IsPGroup 2 (actionLocalM2 Z M Q ⧸
      (actionLocalO1 Z M Q).subgroupOf (actionLocalM2 Z M Q)) := by
  let B0 := actionLocalM2 Z M Q
  let O1 := actionLocalO1 Z M Q
  let qA := QuotientGroup.mk' O1
  have himage : IsPGroup 2 (B0.map qA) := by
    rw [show B0.map qA = actionLocalM2Quotient Z M Q from actionLocalM2_quotient_image Z M Q]
    exact actionLocalM2Quotient_isPGroup Q
  exact himage.of_equiv (quotientSubgroupRangeEquiv B0 O1).symm

/-- The odd-order theorem and the two-group quotient make M₂ solvable. -/
public theorem actionLocalM2_solvable (Q : Subgroup G) : Group.IsSolvable (actionLocalM2InG Z M Q) := by
  let B0 := actionLocalM2 Z M Q
  let O1 := actionLocalO1 Z M Q
  have hO1B0 : O1 ≤ B0 := actionLocalO1_le_M2 Q
  let : Group.IsSolvable O1 := odd_order_theorem O1 (actionLocalO1_odd Q)
  let : Group.IsSolvable (O1.subgroupOf B0) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hO1B0).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hO1B0).injective
  let : Group.IsNilpotent (B0 ⧸ O1.subgroupOf B0) :=
    (actionLocalM2_internal_quotient_isPGroup Q).isNilpotent
  let : Group.IsSolvable B0 := isSolvable_of_normal_subgroup_and_quotient (O1.subgroupOf B0)
  exact Group.isSolvable_of_surjective (f := (actionLocalM2_equiv Q).toMonoidHom)
    (actionLocalM2_equiv Q).surjective

/-- Local strong embedding makes the Omega subgroup of the quotient two-core abelian; lifting through the odd kernel preserves Sylow two-subgroups. -/
public theorem actionLocalM2_hasAbelianSylow
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    HasAbelianSylow 2 (actionLocalM2InG Z M q.chosen.Q) := by
  let Q := q.chosen.Q
  let A := actionLocalM1 Z M Q
  let O1 := actionLocalO1 Z M Q
  let U := actionLocalM2Quotient Z M Q
  let B0 := actionLocalM2 Z M Q
  let qA := QuotientGroup.mk' O1
  have hAstrong : IsStronglyEmbedded A := q.chosen.local_embedding h r hne
  have hUcomm : IsMulCommutative U :=
    omega₁_pCore_quotient_isMulCommutative_of_stronglyEmbedded
      hAstrong O1 (actionLocalO1_odd Q)
  have hquotComm : IsMulCommutative (B0 ⧸ O1.subgroupOf B0) := by
    let : IsMulCommutative (B0.map qA) := by
      rw [show B0.map qA = U from actionLocalM2_quotient_image Z M Q]
      exact hUcomm
    let e := quotientSubgroupRangeEquiv B0 O1
    refine ⟨⟨fun x y => e.injective ?_⟩⟩
    simpa using mul_comm' (e x) (e y)
  have hO1odd : Odd (Nat.card (O1.subgroupOf B0)) := by
    rw [natCard_subgroupOf_eq O1 B0 (actionLocalO1_le_M2 Q)]
    exact actionLocalO1_odd Q
  exact (hasAbelianSylowTwo_of_odd_normal_quotient_isMulCommutative
    (O1.subgroupOf B0) hO1odd hquotComm).of_mulEquiv (actionLocalM2_equiv Q)

private theorem actionLocalM2Hat_quotient_isPGroup (h : IsProductDisconnected Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) :
    let B := actionLocalM2InG Z M q.chosen.Q
    let H := B ⊔ q.R
    ∃ hn : (B.subgroupOf H).Normal, @IsPGroup d.p (H ⧸ B.subgroupOf H)
      (@QuotientGroup.Quotient.group H _ (B.subgroupOf H) hn) := by
  let B := actionLocalM2InG Z M q.chosen.Q
  have hn : (B.subgroupOf (B ⊔ q.R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (actionLocal_R_le_normalizer_M2 h q))
  let : (B.subgroupOf (B ⊔ q.R)).Normal := hn
  exact ⟨hn, quotient_sup_isPGroup B q.R (sylow_isPGroup q.hRsylow)⟩

/-- The normalized product M₂R is an extension of solvable M₂ by a p-group. -/
public theorem actionLocalM2Hat_solvable (h : IsProductDisconnected Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) :
    Group.IsSolvable ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let B := actionLocalM2InG Z M q.chosen.Q
  let H := B ⊔ q.R
  obtain ⟨hn, hquot⟩ := actionLocalM2Hat_quotient_isPGroup h q
  let : (B.subgroupOf H).Normal := hn
  let : Group.IsNilpotent (H ⧸ B.subgroupOf H) := hquot.isNilpotent
  let : Group.IsSolvable B := actionLocalM2_solvable q.chosen.Q
  let e := Subgroup.subgroupOfEquivOfLe (show B ≤ H from le_sup_left)
  let : Group.IsSolvable (B.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact isSolvable_of_normal_subgroup_and_quotient (B.subgroupOf H)

/-- The odd p-group quotient M₂R/M₂ preserves the abelian Sylow two-subgroups. -/
public theorem actionLocalM2Hat_hasAbelianSylow
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    HasAbelianSylow 2 ↥(actionLocalM2InG Z M q.chosen.Q ⊔ q.R) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let B := actionLocalM2InG Z M q.chosen.Q
  let H := B ⊔ q.R
  obtain ⟨hn, hquot⟩ := actionLocalM2Hat_quotient_isPGroup h q
  let : (B.subgroupOf H).Normal := hn
  have hodd : Odd (Nat.card (H ⧸ B.subgroupOf H)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hquot
    rw [hn]
    exact d.hpOdd.pow
  have hab := actionLocalM2_hasAbelianSylow h r hne q
  let e := Subgroup.subgroupOfEquivOfLe (show B ≤ H from le_sup_left)
  exact HasAbelianSylow.of_normal_odd_quotient (B.subgroupOf H) (hab.of_mulEquiv e.symm) hodd



omit [Finite G] in
/-- Every odd-order subgroup of M₂ maps trivially to the two-group quotient in (7F). -/
public theorem actionLocalM2_odd_subgroup_le_oddCore (Q T : Subgroup G)
    (hTB : T ≤ actionLocalM2InG Z M Q) (hTodd : Odd (Nat.card T)) :
    let N := Subgroup.normalizer (Q : Set G)
    let L := actionLocalNCore Z Q
    T ≤ (pPrimeCore 2 L).map (N.subtype.comp L.subtype) := by
  let N := Subgroup.normalizer (Q : Set G)
  let L := actionLocalNCore Z Q
  let A := actionLocalM1 Z M Q
  let B0 := actionLocalM2 Z M Q
  let O1 := actionLocalO1 Z M Q
  let f : A →* G := N.subtype.comp (L.subtype.comp A.subtype)
  have hf : Function.Injective f :=
    N.subtype_injective.comp (L.subtype_injective.comp A.subtype_injective)
  let K := T.comap f
  have hKB : K ≤ B0 := by
    intro a ha
    have hh : f a ∈ B0.map f := by
      simpa only [actionLocalM2InG, Subgroup.map_map] using hTB ha
    obtain ⟨b, hb, he⟩ := hh
    exact hf he ▸ hb
  have hKodd : Odd (Nat.card K) := by
    have hh := hTodd.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.map_comap_le f T))
    rwa [Subgroup.card_map_of_injective hf] at hh
  let qA := QuotientGroup.mk' O1
  have hle : K.map qA ≤ actionLocalM2Quotient Z M Q := by
    rw [← actionLocalM2_quotient_image Z M Q]
    exact Subgroup.map_mono hKB
  have himage2 : IsPGroup 2 (K.map qA) :=
    (actionLocalM2Quotient_isPGroup Q).of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have himageOdd : Odd (Nat.card (K.map qA)) :=
    hKodd.of_dvd_nat (Subgroup.card_map_dvd K qA)
  have hbot : K.map qA = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases himage2.card_eq_or_dvd with hc | hd
    · exact hc
    · exact False.elim (himageOdd.not_two_dvd_nat hd)
  have hKO : K ≤ O1 := by
    have hh := (Subgroup.map_eq_bot_iff K).mp hbot
    simpa only [qA, QuotientGroup.ker_mk'] using hh
  change T ≤ (pPrimeCore 2 L).map (N.subtype.comp L.subtype)
  intro x hx
  have hxB : x ∈ B0.map f := by
    simpa only [actionLocalM2InG, Subgroup.map_map] using hTB hx
  obtain ⟨a, _, rfl⟩ := hxB
  exact ⟨(a : L), hKO hx, rfl⟩

/-- The actual theta(M₂) lies in E, using its odd order and (7E). -/
public theorem actionLocal_theta_le_E
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    corollary64Theta d.p (actionLocalM2InG Z M q.chosen.Q) ≤ theorem4bSection7E M d.z beta :=
  (actionLocalM2_odd_subgroup_le_oddCore q.chosen.Q _
    ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
    (lemma75_theta_odd_card _ _)).trans (actionLocal_oddCore_le_E h r d hne q)

omit [Finite G] in
/-- Every element of M normalizing Q normalizes the ambient intersection M₁. -/
public theorem actionLocalM1_normalizer (h : IsProductDisconnected Z M) (Q : Subgroup G) :
    let N := Subgroup.normalizer (Q : Set G)
    let L := actionLocalNCore Z Q
    M ⊓ N ≤ Subgroup.normalizer ((actionLocalM1 Z M Q).map
      (N.subtype.comp L.subtype) : Set G) := by
  let N := Subgroup.normalizer (Q : Set G)
  let L := actionLocalNCore Z Q
  have he : (actionLocalM1 Z M Q).map (N.subtype.comp L.subtype) = M ⊓ L.map N.subtype := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨hl, ⟨l, l.property, rfl⟩⟩
    · rintro ⟨hxM, n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, hxM, rfl⟩
  dsimp only
  rw [he]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨M.le_normalizer hx.1, actionLocalNCore_normalizer h Q hx.2⟩

private theorem commutator_le_left_of_normalized
    {X : Type*} [Group X] {K P : Subgroup X}
    (hn : P ≤ Subgroup.normalizer (K : Set X)) : ⁅K, P⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro k hk p hp
  have hh := (Subgroup.mem_normalizer_iff.mp (hn hp) k⁻¹).mp (K.inv_mem hk)
  simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk hh

/-- (7D) excludes z from the p-prime core of M₁: that core is normalized by P₁ and would contain the prohibited commutator. -/
public theorem actionLocal_z_not_mem_pPrimeCore_M1 (h : IsProductDisconnected Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) :
    let N := Subgroup.normalizer (q.chosen.Q : Set G)
    let L := actionLocalNCore Z q.chosen.Q
    let A := actionLocalM1 Z M q.chosen.Q
    d.z ∉ (pPrimeCore d.p A).map (N.subtype.comp (L.subtype.comp A.subtype)) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let N := Subgroup.normalizer (q.chosen.Q : Set G)
  let L := actionLocalNCore Z q.chosen.Q
  let A := actionLocalM1 Z M q.chosen.Q
  let f := N.subtype.comp L.subtype
  let AX := A.map f
  let P := (pPrimeCore d.p A).map (f.comp A.subtype)
  have hf : Function.Injective f := N.subtype_injective.comp L.subtype_injective
  let e : A ≃* AX := A.equivMapOfInjective f hf
  have he : (pPrimeCore d.p AX).map AX.subtype = P := by
    rw [← pPrimeCore_map_iso d.p e, Subgroup.map_map]
    rfl
  have hP1MN : q.chosen.P₁ ≤ M ⊓ N := le_inf
    ((sylow_le q.chosen.hP₁sylow).trans (inf_le_left.trans inf_le_left)) q.chosen.hP₁NormQ
  have hn : q.chosen.P₁ ≤ Subgroup.normalizer (P : Set G) := by
    rw [← he]
    exact (hP1MN.trans (actionLocalM1_normalizer h q.chosen.Q)).trans
      (External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic AX (pPrimeCore d.p AX))
  change d.z ∉ P
  intro hz
  have hcomm : ⁅Subgroup.zpowers d.z, q.chosen.P₁⁆ ≤ P :=
    (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hz) le_rfl).trans
      (commutator_le_left_of_normalized hn)
  have hcop : Nat.Coprime d.p (Nat.card P) := by
    rw [show Nat.card P = Nat.card (pPrimeCore d.p A) from
      Subgroup.card_map_of_injective (hf.comp A.subtype_injective)]
    exact pPrimeCore_coprime_card
  exact (d.hp.coprime_iff_not_dvd.mp hcop)
    ((q.sevenD _ q.chosen.hP₁sylow).trans (Subgroup.card_dvd_of_le hcomm))

/-- Local strong embedding conjugates any involution of the normal p-prime core to z; the preceding exclusion therefore makes the core odd. -/
public theorem actionLocal_pPrimeCore_M1_odd
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    Odd (Nat.card (pPrimeCore d.p (actionLocalM1 Z M q.chosen.Q))) := by
  let N := Subgroup.normalizer (q.chosen.Q : Set G)
  let L := actionLocalNCore Z q.chosen.Q
  let A := actionLocalM1 Z M q.chosen.Q
  let zN : N := ⟨d.z, q.chosen.hzNormQ⟩
  let zL : L := ⟨zN, Subgroup.subset_closure d.hzZ⟩
  let zA : A := ⟨zL, d.hzM⟩
  have hz : zA ∉ pPrimeCore d.p A := by
    intro hz
    exact actionLocal_z_not_mem_pPrimeCore_M1 h q ⟨zA, hz, rfl⟩
  have hs : IsStronglyEmbedded A := q.chosen.local_embedding h r hne
  by_contra hodd
  have htwo : 2 ∣ Nat.card (pPrimeCore d.p A) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  have huL : IsInvolution ((u : A) : L) := by
    have ho : orderOf ((u : A) : L) = 2 := by simpa only [Subgroup.orderOf_coe] using hu
    exact (orderOf_eq_prime_iff.mp ho).symm
  have hzL : IsInvolution zL := IsInvolution.subtype
    (IsInvolution.subtype d.hz q.chosen.hzNormQ) zL.property
  obtain ⟨g, hg, hconj⟩ := hs.involutions_conjugate_in (u : A).property huL zA.property hzL
  have hmem : rightConjugateElem (u : A) (⟨g, hg⟩ : A) ∈ pPrimeCore d.p A := by
    simpa [rightConjugateElem] using
      (inferInstance : (pPrimeCore d.p A).Normal).conj_mem _ u.property (⟨g, hg⟩ : A)⁻¹
  have heq : rightConjugateElem (u : A) (⟨g, hg⟩ : A) = zA := Subtype.ext hconj
  exact hz (heq ▸ hmem)

private theorem subgroupOf_le_pPrimeCore_map
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K H : Subgroup G} (hKH : K ≤ H) [hKN : (K.subgroupOf H).Normal]
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p ↥H).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rw [hcard]
    exact hcop
  have hsub : K.subgroupOf H ≤ pPrimeCore p ↥H :=
    le_sSup ⟨hKN, hcop'⟩
  simpa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKH] using
    (Subgroup.map_mono (f := H.subtype) hsub)

private theorem pPrimeCore_sup_eq
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (B R : Subgroup G)
    (hRnorm : R ≤ Subgroup.normalizer (B : Set G))
    (hRp : IsPGroup p R) :
    (pPrimeCore p (↥(B ⊔ R))).map (B ⊔ R).subtype =
      (pPrimeCore p B).map B.subtype := by
  classical
  let H : Subgroup G := B ⊔ R
  have hBH : B ≤ H := by simp [H]
  have hHnormB : H ≤ Subgroup.normalizer (B : Set G) := by
    simpa [H] using (sup_le Subgroup.le_normalizer hRnorm)
  have hBnorm : (B.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hBH).2
    exact hHnormB
  let : (B.subgroupOf H).Normal := hBnorm
  have hquotP : IsPGroup p (↥H ⧸ B.subgroupOf H) := by
    simpa [H] using quotient_sup_isPGroup B R hRp
  let qH : H →* H ⧸ B.subgroupOf H := QuotientGroup.mk' (B.subgroupOf H)
  let OH : Subgroup H := pPrimeCore p H
  have hmapP : IsPGroup p (OH.map qH) := hquotP.to_subgroup (OH.map qH)
  have hmapCop : Nat.Coprime p (Nat.card (OH.map qH)) := by
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_map_dvd (H := OH) qH)
      (pPrimeCore_coprime_card (p := p) (G := H))
  have hmapCard : Nat.card (OH.map qH) = 1 := by
    rcases hmapP.card_eq_or_dvd with hcard | hpDvd
    · exact hcard
    · exact False.elim
        (((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hmapCop) hpDvd)
  have hmapBot : OH.map qH = ⊥ :=
    (Subgroup.card_eq_one (H := OH.map qH)).1 hmapCard
  have hOHleB : OH ≤ B.subgroupOf H := by
    have hker : OH ≤ qH.ker :=
      (Subgroup.map_eq_bot_iff (f := qH) (H := OH)).1 hmapBot
    simpa [qH, QuotientGroup.ker_mk'] using hker
  let OHX : Subgroup G := OH.map H.subtype
  let OBX : Subgroup G := (pPrimeCore p B).map B.subtype
  have hOHXleB : OHX ≤ B := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    change (y : G) ∈ B
    exact hOHleB hy
  have : OH.Characteristic := pPrimeCore_characteristic
  have hHnormOHX : H ≤ Subgroup.normalizer (OHX : Set G) := by
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := H) (K := OH))
  have : (OHX.subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOHXleB).2
    exact hBH.trans hHnormOHX
  have hOHXcop : Nat.Coprime p (Nat.card OHX) := by
    rw [show Nat.card OHX = Nat.card OH by
      simpa [OHX] using
        (Subgroup.card_map_of_injective (K := OH) (f := H.subtype)
          H.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := H)
  have hfirst : OHX ≤ OBX := by
    exact subgroupOf_le_pPrimeCore_map (p := p) hOHXleB hOHXcop
  have hOBXleH : OBX ≤ H := by
    intro x hx
    exact hBH (by
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact y.property)
  have : (pPrimeCore p B).Characteristic := pPrimeCore_characteristic
  have hHnormOBX : H ≤ Subgroup.normalizer (OBX : Set G) := by
    exact hHnormB.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := B) (K := pPrimeCore p B))
  have : (OBX.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hOBXleH).2
    exact hHnormOBX
  have hOBXcop : Nat.Coprime p (Nat.card OBX) := by
    rw [show Nat.card OBX = Nat.card (pPrimeCore p B) by
      simpa [OBX] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p B)
          (f := B.subtype) B.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := B)
  have hsecond : OBX ≤ OHX := by
    exact subgroupOf_le_pPrimeCore_map (p := p) hOBXleH hOBXcop
  exact le_antisymm (by simpa [OHX, OBX, H] using hfirst)
    (by simpa [OHX, OBX, H] using hsecond)

private theorem theta_eq_pPrimeCore_of_odd
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G)
    (hodd : Odd (Nat.card ((pPrimeCore p A).map A.subtype))) :
    corollary64Theta p A = (pPrimeCore p A).map A.subtype := by
  classical
  let PX : Subgroup G := (pPrimeCore p A).map A.subtype
  let O : Subgroup G := corollary64OddCore A
  let T : Subgroup G := corollary64Theta p A
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPXleA : PX ≤ A := by
    simpa [PX] using (Subgroup.map_subtype_le (pPrimeCore p A))
  have : (pPrimeCore p A).Characteristic := pPrimeCore_characteristic
  have hAnormPX : A ≤ Subgroup.normalizer (PX : Set G) := by
    exact Subgroup.le_normalizer.trans
      (section8_normalizer_map_subtype_le_of_characteristic
        (H := A) (K := pPrimeCore p A))
  have : (PX.subgroupOf A).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPXleA).2
    exact hAnormPX
  have hPXcop : Nat.Coprime p (Nat.card PX) := by
    rw [show Nat.card PX = Nat.card (pPrimeCore p A) by
      simpa [PX] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p A)
          (f := A.subtype) A.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := A)
  have hPXleO : PX ≤ O := by
    have hPXtwoCop : Nat.Coprime 2 (Nat.card PX) :=
      hodd.coprime_two_left
    simpa [PX, O, corollary64OddCore, twoPrimeCore] using
      (subgroupOf_le_pPrimeCore_map (p := 2) hPXleA hPXtwoCop)
  have hOleA : O ≤ A := by
    simpa [O, corollary64OddCore] using
      (Subgroup.map_subtype_le (twoPrimeCore A))
  have hOnormPX : O ≤ Subgroup.normalizer (PX : Set G) :=
    hOleA.trans hAnormPX
  have : (PX.subgroupOf O).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hPXleO).2
    exact hOnormPX
  have hPXleT : PX ≤ T := by
    simpa [T, corollary64Theta] using
      (subgroupOf_le_pPrimeCore_map (p := p) hPXleO hPXcop)
  have : (twoPrimeCore A).Characteristic := by
    simpa [twoPrimeCore] using
      (pPrimeCore_characteristic (p := 2) (G := A))
  have hAnormO : A ≤ Subgroup.normalizer (O : Set G) := by
    simpa [O, corollary64OddCore, twoPrimeCore] using
      (Subgroup.le_normalizer.trans
        (section8_normalizer_map_subtype_le_of_characteristic
          (H := A) (K := twoPrimeCore A)))
  have : (pPrimeCore p O).Characteristic := pPrimeCore_characteristic
  have hNormOnormT : Subgroup.normalizer (O : Set G) ≤
      Subgroup.normalizer (T : Set G) := by
    simpa [T, corollary64Theta] using
      (External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        O (pPrimeCore p O))
  have hAnormT : A ≤ Subgroup.normalizer (T : Set G) :=
    hAnormO.trans hNormOnormT
  have hTleO : T ≤ O := by
    simpa [T, O, corollary64Theta] using
      (Subgroup.map_subtype_le (pPrimeCore p O))
  have hTleA : T ≤ A := hTleO.trans hOleA
  have : (T.subgroupOf A).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTleA).2
    exact hAnormT
  have hTcop : Nat.Coprime p (Nat.card T) := by
    rw [show Nat.card T = Nat.card (pPrimeCore p O) by
      simpa [T, corollary64Theta] using
        (Subgroup.card_map_of_injective (K := pPrimeCore p O)
          (f := O.subtype) O.subtype_injective)]
    exact pPrimeCore_coprime_card (p := p) (G := O)
  have hTlePX : T ≤ PX := by
    exact subgroupOf_le_pPrimeCore_map (p := p) hTleA hTcop
  exact le_antisymm hTlePX hPXleT



/-- Relative normality (7G) puts the p-prime core of M₂ in the odd p-prime core of M₁. -/
public theorem actionLocal_pPrimeCore_M2_odd
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    Odd (Nat.card (pPrimeCore d.p (actionLocalM2InG Z M q.chosen.Q))) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let A := actionLocalM1 Z M q.chosen.Q
  let B0 := actionLocalM2 Z M q.chosen.Q
  have hh := (actionLocal_pPrimeCore_M1_odd h r hne q).of_dvd_nat
    (Subgroup.card_dvd_of_le (pPrimeCore_map_subtype_le_pPrimeCore_of_normal d.p B0))
  rw [Subgroup.card_map_of_injective B0.subtype_injective] at hh
  rw [← pPrimeCore_map_iso d.p (actionLocalM2_equiv q.chosen.Q),
    Subgroup.card_map_of_injective (actionLocalM2_equiv q.chosen.Q).injective]
  exact hh

/-- The source p-prime-core identity for the literal product M₂R and theta(M₂). -/
public theorem actionLocal_pPrimeCore_M2Hat_eq_theta
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    let B := actionLocalM2InG Z M q.chosen.Q
    let H := B ⊔ q.R
    (pPrimeCore d.p H).map H.subtype = corollary64Theta d.p B := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let B := actionLocalM2InG Z M q.chosen.Q
  have he := pPrimeCore_sup_eq B q.R (actionLocal_R_le_normalizer_M2 h q)
    (sylow_isPGroup q.hRsylow)
  have hodd : Odd (Nat.card ((pPrimeCore d.p B).map B.subtype)) := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact actionLocal_pPrimeCore_M2_odd h r hne q
  exact he.trans (theta_eq_pPrimeCore_of_odd B hodd).symm

private theorem sylow_maximal {X : Type*} [Group X] {p : ℕ} {P T E : Subgroup X}
    (hP : theorem4bIsSylowSubgroupOf p P E) (hT : IsPGroup p T)
    (hTE : T ≤ E) (hPT : P ≤ T) : T ≤ P := by
  obtain ⟨S, hS⟩ := hP
  have hSle : (S : Subgroup E) ≤ T.subgroupOf E := by
    intro x hx
    apply hPT
    rw [hS]
    exact ⟨x, hx, rfl⟩
  have hp : IsPGroup p (T.subgroupOf E) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTE).symm
  have he := S.is_maximal' hp hSle
  intro x hx
  rw [hS]
  refine ⟨⟨x, hTE hx⟩, ?_, rfl⟩
  rw [← he]
  exact hx

/-- R is Sylow in M₂R: the intersection of a p-overgroup of R with M₂ is odd, hence lies in E and then in P₁. -/
public theorem actionLocal_R_isSylow_M2Hat
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    theorem4bIsSylowSubgroupOf d.p q.R (actionLocalM2InG Z M q.chosen.Q ⊔ q.R) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  let B := actionLocalM2InG Z M q.chosen.Q
  let H := B ⊔ q.R
  let E := theorem4bSection7E M d.z beta
  have hRH : q.R ≤ H := le_sup_right
  have hRp := sylow_isPGroup q.hRsylow
  have hRHp : IsPGroup d.p (q.R.subgroupOf H) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  obtain ⟨S, hRS⟩ := hRHp.exists_le_sylow
  let SX := (S : Subgroup H).map H.subtype
  have hRpSX : q.R ≤ SX := by
    intro x hx
    exact ⟨⟨x, hRH hx⟩, hRS hx, rfl⟩
  have hSXp : IsPGroup d.p SX := S.isPGroup'.map H.subtype
  have hUE : SX ⊓ E ≤ q.chosen.P₁ :=
    sylow_maximal q.chosen.hP₁sylow (hSXp.to_inf_left (K := E)) inf_le_right
      (le_inf (q.hP₁R.trans hRpSX) (sylow_le q.chosen.hP₁sylow))
  have hT : SX ⊓ B ≤ q.R := by
    have hTodd : Odd (Nat.card (SX ⊓ B : Subgroup G)) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hSXp.to_inf_left (K := B))
      rw [hn]
      exact d.hpOdd.pow
    have hTE : SX ⊓ B ≤ E :=
      (actionLocalM2_odd_subgroup_le_oddCore q.chosen.Q _ inf_le_right hTodd).trans
        (actionLocal_oddCore_le_E h r d hne q)
    exact (le_inf inf_le_left hTE).trans (hUE.trans q.hP₁R)
  have : (B.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (show B ≤ H from le_sup_left)).mpr
      (sup_le Subgroup.le_normalizer (actionLocal_R_le_normalizer_M2 h.disconnected q))
  have hsup : B.subgroupOf H ⊔ q.R.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (show B ≤ H from le_sup_left),
      Subgroup.map_subgroupOf_eq_of_le hRH, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hSXle : SX ≤ q.R := by
    rintro x ⟨s, hs, rfl⟩
    have hmem : s ∈ B.subgroupOf H ⊔ q.R.subgroupOf H := hsup ▸ Subgroup.mem_top s
    obtain ⟨b, hb, v, hv, hbv⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have hbS : (b : G) ∈ SX := by
      have he : (b : G) = (s : G) * (v : G)⁻¹ := by
        rw [← hbv]
        simp
      rw [he]
      exact SX.mul_mem ⟨s, hs, rfl⟩ (SX.inv_mem (hRpSX hv))
    have hbR := hT ⟨hbS, hb⟩
    rw [← hbv]
    exact q.R.mul_mem hbR hv
  exact ⟨S, le_antisymm hRpSX hSXle⟩



/-- The central square-one factor of the full ZD conclusion vanishes by local strong embedding, leaving the actual simple Bender quotient and its Borel. -/
public theorem actionLocalNCore_borel
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    let L := actionLocalNCore Z q.chosen.Q
    let A := actionLocalM1 Z M q.chosen.Q
    IsSimpleBenderGroup (L ⧸ pPrimeCore 2 L) ∧
      IsBorelSubgroup (A.map (QuotientGroup.mk' (pPrimeCore 2 L))) := by
  let N := Subgroup.normalizer (q.chosen.Q : Set G)
  let L := actionLocalNCore Z q.chosen.Q
  let A := actionLocalM1 Z M q.chosen.Q
  let O := pPrimeCore 2 L
  let Q := L ⧸ O
  let f := QuotientGroup.mk' O
  let X := commutator Q
  have hstruct := actionLocalNCore_structure h r d hne q
  change ∃ u : L, u ∈ A ∧ u ^ 2 = 1 ∧
    commutator L ⊔ Subgroup.zpowers u = ⊤ ∧ X ⊔ Subgroup.zpowers (f u) = ⊤ ∧
    Disjoint X (Subgroup.zpowers (f u)) ∧
    (∀ x ∈ X, ∀ v ∈ Subgroup.zpowers (f u), Commute x v) ∧
    IsSimpleBenderGroup X ∧ O ≤ A ⊓ commutator L ∧
    IsBorelSubgroup (((A ⊓ commutator L).map f).subgroupOf X) ∧
    (∀ z : L, ((z : N) : G) ∈ Z → (f u)⁻¹ * f z ∈ X ∧ f z ≠ f u) at hstruct
  obtain ⟨u, huA, hu2, hgenL, hgenQ, _hdis, hcomm, hmodel, hOA, hB, _hW⟩ := hstruct
  have hO : O ≤ A := hOA.trans inf_le_left
  have hs : IsStronglyEmbedded A := q.chosen.local_embedding h.disconnected r hne
  have hc : f u ∈ Subgroup.center Q := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hy : y ∈ X ⊔ Subgroup.zpowers (f u) := hgenQ ▸ Subgroup.mem_top y
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have haC := hcomm a ha (f u) (Subgroup.mem_zpowers (f u))
    obtain ⟨n, rfl⟩ := hb
    exact (haC.mul_left ((Commute.refl (f u)).zpow_left n)).eq
  have hu1 : u = 1 := by
    by_contra hune
    have hu : IsInvolution u := ⟨hune, hu2⟩
    apply hs.ne_top
    apply top_unique
    intro g _
    have hgu : IsInvolution ((MulAut.conj g) u) :=
      IsInvolution.map_of_injective hu (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have hf : f u = f ((MulAut.conj g) u) := by
      have hcommute := Subgroup.mem_center_iff.mp hc (f g)
      change f u = f (g * u * g⁻¹)
      rw [map_mul, map_mul, map_inv, hcommute, mul_inv_cancel_right]
    have hkcop : Nat.Coprime 2 (Nat.card f.ker) := by
      simpa only [f, QuotientGroup.ker_mk'] using (pPrimeCore_coprime_card (p := 2) (G := L))
    obtain ⟨k, hk⟩ := Subgroup.involutions_same_image_conj_ker f hkcop
      (orderOf_eq_prime hu.sq_eq_one hu.ne_one) (orderOf_eq_prime hgu.sq_eq_one hgu.ne_one) hf
    have hkA : (k : L) ∈ A := hO (by
      simpa only [f, QuotientGroup.ker_mk'] using k.property)
    have hguA : (MulAut.conj g) u ∈ A := by
      rw [← hk]
      exact A.mul_mem (A.mul_mem hkA huA) (A.inv_mem hkA)
    have hginv : g⁻¹ ∈ A := hs.mem_of_involution_mem_rightConjugate hguA
      (by simpa [rightConjugateElem, MulAut.conj_apply] using
        (rightConjugateElem_mem_rightConjugate (g := g⁻¹) huA)) hgu
    simpa using A.inv_mem hginv
  have hL : commutator L = ⊤ := by simpa [hu1] using hgenL
  have hX : X = ⊤ := by simpa [f, hu1] using hgenQ
  let e : X ≃* Q := MulEquiv.ofBijective X.subtype
    ⟨Subtype.val_injective, fun y => ⟨⟨y, hX ▸ Subgroup.mem_top y⟩, rfl⟩⟩
  refine ⟨hmodel.map_mulEquiv e, ?_⟩
  have hb := hB.map_mulEquiv e
  have he : (((A ⊓ commutator L).map f).subgroupOf X).map e.toMonoidHom = A.map f := by
    rw [hL, inf_top_eq]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hX ▸ Subgroup.mem_top y⟩, hy, rfl⟩
  rw [he] at hb
  exact hb

/-- The distinguished involution belongs to the normal Sylow two-subgroup of the Borel quotient, hence to the preimage in (7F). -/
public theorem actionLocal_z_mem_M2
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    d.z ∈ actionLocalM2InG Z M q.chosen.Q := by
  let N := Subgroup.normalizer (q.chosen.Q : Set G)
  let L := actionLocalNCore Z q.chosen.Q
  let A := actionLocalM1 Z M q.chosen.Q
  let O := pPrimeCore 2 L
  let O1 := actionLocalO1 Z M q.chosen.Q
  let qA := QuotientGroup.mk' O1
  let f := QuotientGroup.mk' O
  let zN : N := ⟨d.z, q.chosen.hzNormQ⟩
  let zL : L := ⟨zN, Subgroup.subset_closure d.hzZ⟩
  let zA : A := ⟨zL, d.hzM⟩
  have hzA : IsInvolution zA := IsInvolution.subtype
    (IsInvolution.subtype (IsInvolution.subtype d.hz q.chosen.hzNormQ) zL.property) d.hzM
  obtain ⟨hmodel, hborel⟩ := actionLocalNCore_borel h r d hne q
  obtain ⟨S, hSn, _hregular⟩ := simpleBender_borel_normalSylow_regular hborel hmodel
  let : (S : Subgroup (A.map f)).Normal := hSn
  let e : (A ⧸ O1) ≃* A.map f := quotientSubgroupRangeEquiv A O
  let T := (S : Subgroup (A.map f)).map e.symm.toMonoidHom
  have : T.Normal := Subgroup.Normal.map hSn e.symm.toMonoidHom e.symm.surjective
  have hTp : IsPGroup 2 T := S.isPGroup'.map e.symm.toMonoidHom
  have hTcore : T ≤ pCore 2 (A ⧸ O1) := le_sSup ⟨inferInstance, hTp⟩
  have hcyc := ((isPGroup_zpowers_of_involution hzA).map qA).map e.toMonoidHom
  have hcycle : ((Subgroup.zpowers zA).map qA).map e.toMonoidHom ≤ (S : Subgroup (A.map f)) := by
    have hh := hcyc.inf_normalizer_sylow S
    change ((Subgroup.zpowers zA).map qA).map e.toMonoidHom ⊓
      Subgroup.normalizer ((S : Subgroup (A.map f)) : Set (A.map f)) =
        ((Subgroup.zpowers zA).map qA).map e.toMonoidHom ⊓ (S : Subgroup (A.map f)) at hh
    rw [Subgroup.normalizer_eq_top (H := (S : Subgroup (A.map f))), inf_top_eq] at hh
    exact hh.le.trans inf_le_right
  have hqzS : e (qA zA) ∈ (S : Subgroup (A.map f)) :=
    hcycle (Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_map_of_mem qA (Subgroup.mem_zpowers zA)))
  have hqzT : qA zA ∈ T := ⟨e (qA zA), hqzS, e.symm_apply_apply _⟩
  let P := pCore 2 (A ⧸ O1)
  let zP : P := ⟨qA zA, hTcore hqzT⟩
  have hzP : zP ^ 2 = 1 := by
    apply Subtype.ext
    change (qA zA) ^ 2 = 1
    rw [← map_pow, hzA.sq_eq_one, map_one]
  have homega : zP ∈ omega₁ (G := P) (p := 2) := by
    apply Subgroup.subset_closure
    change zP ^ (2 ^ 1) = 1
    simpa only [pow_one] using hzP
  have hzB0 : zA ∈ actionLocalM2 Z M q.chosen.Q := ⟨zP, homega, rfl⟩
  exact ⟨zN, ⟨zL, ⟨zA, hzB0, rfl⟩, rfl⟩, rfl⟩



/-- The Sylow subgroup P₁ of E is precisely R ∩ E. -/
public theorem actionLocal_R_inf_E
    {d : ActionCounterexample Z M} {beta : G ⧸ M}
    (q : ActionMaximalNormalizerData d beta) :
    q.R ⊓ theorem4bSection7E M d.z beta = q.chosen.P₁ := by
  apply le_antisymm
  · exact sylow_maximal q.chosen.hP₁sylow (sylow_isPGroup q.hRsylow).to_inf_left
      inf_le_right (le_inf q.hP₁R (sylow_le q.chosen.hP₁sylow))
  · exact le_inf q.hP₁R (sylow_le q.chosen.hP₁sylow)

/-- All canonical local inputs to Lemma 7.11, with the induction, normalization, quotient and Sylow premises discharged. -/
public theorem actionLocal_structure
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1) (q : ActionMaximalNormalizerData d beta) :
    let N := Subgroup.normalizer (q.chosen.Q : Set G)
    let L := actionLocalNCore Z q.chosen.Q
    let A := actionLocalM1 Z M q.chosen.Q
    let B := actionLocalM2InG Z M q.chosen.Q
    let H := B ⊔ q.R
    pPrimeCore 2 L ≤ A ∧
    (pPrimeCore 2 L).map (N.subtype.comp L.subtype) ≤ theorem4bSection7E M d.z beta ∧
    d.z ∈ B ∧ corollary64Theta d.p B ≤ theorem4bSection7E M d.z beta ∧
    Group.IsSolvable H ∧ HasAbelianSylow 2 H ∧
    theorem4bIsSylowSubgroupOf d.p q.R H ∧ pCore d.p H ≠ ⊥ ∧
    (pPrimeCore d.p H).map H.subtype = corollary64Theta d.p B := by
  exact ⟨actionLocal_oddCore_le_M1 h r d hne q, actionLocal_oddCore_le_E h r d hne q,
    actionLocal_z_mem_M2 h r d hne q, actionLocal_theta_le_E h r d hne q,
    actionLocalM2Hat_solvable h.disconnected q,
    actionLocalM2Hat_hasAbelianSylow h.disconnected r hne q,
    actionLocal_R_isSylow_M2Hat h r d hne q, actionLocal_pCore_ne_bot q,
    actionLocal_pPrimeCore_M2Hat_eq_theta h.disconnected r hne q⟩


end BenderSuzuki.ZD
