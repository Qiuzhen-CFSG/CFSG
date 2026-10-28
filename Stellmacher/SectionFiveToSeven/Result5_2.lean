module

public import Stellmacher.SectionFiveToSeven.FiveTwoInitialReductions
public import Stellmacher.SectionFiveToSeven.FiveTwoResidualBaumannCommutator
public import Stellmacher.SectionFiveToSeven.FiveTwoCentralizerConjugateAlignment
public import Stellmacher.SectionFiveToSeven.FiveTwoMinimalBad
public import Stellmacher.SectionFiveToSeven.FiveTwoCoreNotCentralizer
public import Stellmacher.SectionThree.SubnormalCoreCenter
public import Stellmacher.SectionThree.SubnormalOddQuotient
public import Stellmacher.SectionThree.OmegaNormalClosureElementary
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.SectionFiveToSeven.FiveTwoQuotientNormalizer
public import Stellmacher.SectionFiveToSeven.FiveTwoQuotientCorePullback
public import Stellmacher.SectionFiveToSeven.FiveTwoQuotientCoreImage
public import Stellmacher.SectionFiveToSeven.FiveTwoSourceQuotientBridge
public import Stellmacher.SectionFiveToSeven.FiveTwoThompsonNoncontainment
public import Theory.GroupTheory.SylowNormalCoprimeSupplement

/-!
# Stellmacher (5.2): subnormality in two-local overgroups

This module proves Stellmacher's Lemma (5.2).  For a subgroup \`K\` of a
member \`P ∈ ℘*(C_H(Ω₁(Z(S₀))),S₀)\` satisfying \`K=[K,B(S₀)]\`, it shows
that \`K\` is subnormal in every two-local overgroup of \`B(S₀)K\`, assuming
those local overgroups are solvable and of characteristic two type.

The proof follows the source's maximal-counterexample argument.  Initial
reductions put \`K\` subnormal in \`O²(P)\` and establish the two-subgroup
normalizer property.  A minimal bad overgroup is aligned with a conjugate
Sylow subgroup containing its two-core, the two-core of \`K\`, and the
Baumann subgroup.  The normal closure of the aligned omega-center is
therefore elementary abelian.  Assertion (3.5) and the effective quadratic
action argument show that \`O₂(K)\` is not in its centralizer.

Inside the minimal bad group, the corrected odd Fitting-factor argument puts
the quotient two-core in the aligned Sylow image; the normal-closure pullback
then kills it.  Thompson noncontainment and the source-specific form of (2.2)
force the image of \`K\` to have trivial two-core, contradicting the preceding
noncontainment.  Private transport lemmas keep the ambient and intrinsic
subgroup incarnations explicit.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (5.2), pp. 28–29; see
\`refs/latex/stellmacher-n-group.tex\`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem twoCoreIn_le_52assembly
    {G : Type u} [Group G] (P : Subgroup G) :
    twoCoreIn P ≤ P :=
  Subgroup.map_subtype_le _

private theorem twoCoreIn_isPGroup_52assembly
    {G : Type u} [Group G] (P : Subgroup G) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

private theorem twoCoreIn_normal_subgroupOf_52assembly
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreIn,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

private theorem le_normalizer_twoCoreIn_52assembly
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le_52assembly P)).mp
    (twoCoreIn_normal_subgroupOf_52assembly P)

private theorem normalizer_le_normalizer_map_subtype_of_characteristic_52assembly
    {G : Type u} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, hg⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := by
    change xH ∈ Subgroup.comap
      (Subgroup.normalizerMonoidHom H gH).toMonoidHom K
    rw [hfix]
    exact hxK
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

private theorem normalizer_le_normalizer_twoCoreIn_52assembly
    {G : Type u} [Group G] (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (twoCoreIn K : Set G) := by
  exact normalizer_le_normalizer_map_subtype_of_characteristic_52assembly
    K (pCore 2 K)

private theorem le_normalizer_sup_52assembly
    {G : Type u} [Group G] (D A B : Subgroup G)
    (hDA : D ≤ Subgroup.normalizer (A : Set G))
    (hDB : D ≤ Subgroup.normalizer (B : Set G)) :
    D ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDA hd),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hDB hd)]

private theorem middle_le_sup_sup_52assembly
    {G : Type u} [Group G] (A B C : Subgroup G) :
    B ≤ A ⊔ (B ⊔ C) := by
  exact (show B ≤ B ⊔ C from le_sup_left).trans
    (show B ⊔ C ≤ A ⊔ (B ⊔ C) from le_sup_right)

private theorem map_internal_ambient_52assembly
    {G : Type u} [Group G] (L : Subgroup G) (P : Subgroup L)
    (K : Subgroup P) :
    let eP : P ≃* P.map L.subtype :=
      P.equivMapOfInjective L.subtype L.subtype_injective
    (K.map eP.toMonoidHom).map (P.map L.subtype).subtype =
      (K.map P.subtype).map L.subtype := by
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem twoCoreIn_map_subtype_52assembly
    {G : Type u} [Group G] (L : Subgroup G) (P : Subgroup L) :
    twoCoreIn (P.map L.subtype) = (twoCoreIn P).map L.subtype := by
  let eP : P ≃* P.map L.subtype :=
    P.equivMapOfInjective L.subtype L.subtype_injective
  have hcore : (pCore 2 P).map eP.toMonoidHom =
      pCore 2 (P.map L.subtype) := pCore_map_iso 2 eP
  unfold twoCoreIn
  rw [← hcore, map_internal_ambient_52assembly]

private theorem twoCoreIn_subgroupOf_map_subtype_52assembly
    {G : Type u} [Group G] (A M : Subgroup G) (hAM : A ≤ M) :
    (twoCoreIn (A.subgroupOf M)).map M.subtype = twoCoreIn A := by
  rw [← twoCoreIn_map_subtype_52assembly M (A.subgroupOf M),
    Subgroup.map_subgroupOf_eq_of_le hAM]

private theorem quotient_pCore_isPGroup_of_equiv_52assembly
    {G G' : Type u} [Group G] [Group G'] [Finite G] [Finite G']
    (p r : ℕ) [Fact r.Prime] (e : G ≃* G')
    (h : IsPGroup r (G ⧸ pCore p G)) :
    IsPGroup r (G' ⧸ pCore p G') := by
  rw [IsPGroup.iff_card] at h ⊢
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← Subgroup.index_eq_card]
  calc
    (pCore p G').index = ((pCore p G).map e.toMonoidHom).index := by
      rw [pCore_map_iso p e]
    _ = (pCore p G).index := Subgroup.index_map_equiv (pCore p G) e
    _ = Nat.card (G ⧸ pCore p G) := Subgroup.index_eq_card (pCore p G)
    _ = r ^ n := hn

private theorem baumannIn_map_subtype_52assembly
    {G : Type u} [Group G] (M : Subgroup G) (S : Subgroup M) :
    (baumannIn S).map M.subtype = baumannIn (S.map M.subtype) := by
  change (S ⊓ Subgroup.centralizer
      (Stellmacher.omegaOneCenterAmbient
        (Stellmacher.elementaryAbelianMaxJ S) : Set M)).map M.subtype =
    S.map M.subtype ⊓ Subgroup.centralizer
      (Stellmacher.omegaOneCenterAmbient
        (Stellmacher.elementaryAbelianMaxJ (S.map M.subtype)) : Set G)
  let f : M →* G := M.subtype
  let J : Subgroup M := Stellmacher.elementaryAbelianMaxJ S
  let W : Subgroup M := Stellmacher.omegaOneCenterAmbient J
  have hJmap : J.map f =
      Stellmacher.elementaryAbelianMaxJ (S.map f) := by
    exact (Stellmacher.elementaryAbelianMaxJ_map_injective
      f M.subtype_injective S).symm
  have hWmap : W.map f = Stellmacher.omegaOneCenterAmbient
      (Stellmacher.elementaryAbelianMaxJ (S.map f)) := by
    rw [← hJmap]
    exact (Stellmacher.omegaOneCenterAmbient_map_injective
      f M.subtype_injective J).symm
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem f hs.1, ?_⟩
    change f s ∈ Subgroup.centralizer
      (Stellmacher.omegaOneCenterAmbient
        (Stellmacher.elementaryAbelianMaxJ (S.map f)) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ W.map f := by rw [hWmap]; exact hy
    obtain ⟨w, hw, rfl⟩ := hy'
    exact congrArg f (Subgroup.mem_centralizer_iff.mp hs.2 w hw)
  · rintro ⟨hxS, hxcent⟩
    obtain ⟨s, hsS, hsx⟩ := hxS
    subst x
    refine ⟨s, ⟨hsS, ?_⟩, rfl⟩
    change s ∈ Subgroup.centralizer (W : Set M)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    apply M.subtype_injective
    have hw' : f w ∈ Stellmacher.omegaOneCenterAmbient
        (Stellmacher.elementaryAbelianMaxJ (S.map f)) := by
      rw [← hWmap]
      exact ⟨w, hw, rfl⟩
    have hwset : f w ∈ (Stellmacher.omegaOneCenterAmbient
        (Stellmacher.elementaryAbelianMaxJ (S.map f)) : Set G) := hw'
    exact Subgroup.mem_centralizer_iff.mp hxcent (f w) (by
      simpa only [f] using hwset)

private theorem isSubnormal_subgroupOf_of_map_subtype_52assembly
    {G : Type u} [Group G]
    (M : Subgroup G) (X : Subgroup M) (A : Subgroup G)
    (_hAM : A ≤ M) (_hAMX : A.subgroupOf M ≤ X)
    (hsub : SubnormalIn A (X.map M.subtype)) :
    ((A.subgroupOf M).subgroupOf X).IsSubnormal := by
  let Xamb : Subgroup G := X.map M.subtype
  let eX : X ≃* Xamb :=
    X.equivMapOfInjective M.subtype M.subtype_injective
  have hc := hsub.2.comap eX.toMonoidHom
  have heq : (A.subgroupOf Xamb).comap eX.toMonoidHom =
      (A.subgroupOf M).subgroupOf X := by
    ext x
    change ((x : M) : G) ∈ A ↔ (x : M) ∈ A.subgroupOf M
    rfl
  rw [heq] at hc
  exact hc

private theorem sectionThreeHypotheses_of_pstar_52assembly
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G)) :
    Stellmacher.SectionThree.Hypotheses G (S : Subgroup G) := by
  have hcoreP_le_S : twoCoreIn P ≤ (S : Subgroup G) := by
    obtain ⟨_, T, hT⟩ := hP.1.1.2.1
    rw [← hT]
    exact Subgroup.map_mono
      ((pCore_isPGroup (G := P) (p := 2)).le_sylow_of_normal T)
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    intro hbot
    exact hP.1.1.2.2.1
      (le_bot_iff.mp (hcoreP_le_S.trans (le_of_eq hbot)))
  let _ : Nontrivial (S : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  obtain ⟨n, hn, hcard⟩ := S.isPGroup'.nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card G) := by
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card (S : Subgroup G) by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)).trans
    exact Subgroup.card_subgroup_dvd_card (S : Subgroup G)
  exact ⟨heven, hSne, S.isPGroup'⟩

private theorem centralizer_map_equiv_52assembly
    {G : Type u} [Group G] (A : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (A : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (A.map e.toMonoidHom : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Subgroup.centralizer (A : Set G) at hx
    change e x ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G)
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨a, ha, rfl⟩
    simpa using congrArg e (hx a ha)
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change y ∈ Subgroup.centralizer (A.map e.toMonoidHom : Set G) at hy
    change e.symm y ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro a ha
    apply e.injective
    simpa using hy (e a) ⟨a, ha, rfl⟩

private theorem subnormalIn_restrict_52assembly
    {G : Type u} [Group G] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hsub : SubnormalIn A C) :
    SubnormalIn A B := by
  let BC : Subgroup C := B.subgroupOf C
  let e : BC ≃* B := Subgroup.subgroupOfEquivOfLe hBC
  have hsubBC :
      ((A.subgroupOf C).subgroupOf BC).IsSubnormal := hsub.2.subgroupOf
  have hmapped := Subgroup.IsSubnormal.map
    (f := e.toMonoidHom) e.surjective hsubBC
  have hmap : ((A.subgroupOf C).subgroupOf BC).map e.toMonoidHom =
      A.subgroupOf B := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      let xC : C := ⟨a, hBC (hAB ha)⟩
      let xBC : BC := ⟨xC, hAB ha⟩
      exact ⟨xBC, ha, rfl⟩
  rw [hmap] at hmapped
  exact ⟨hAB, hmapped⟩

private theorem subnormalIn_trans_52assembly
    {G : Type u} [Group G] {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (hsubAB : SubnormalIn A B) (hsubBC : SubnormalIn B C) :
    SubnormalIn A C := by
  let BC : Subgroup C := B.subgroupOf C
  let e : B ≃* BC := (Subgroup.subgroupOfEquivOfLe hBC).symm
  have hmapped := Subgroup.IsSubnormal.map
    (f := e.toMonoidHom) e.surjective hsubAB.2
  have hmap : (A.subgroupOf B).map e.toMonoidHom =
      (A.subgroupOf C).subgroupOf BC := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ha
      exact ⟨⟨a, hAB ha⟩, ha, rfl⟩
  rw [hmap] at hmapped
  exact ⟨hAB.trans hBC,
    Subgroup.IsSubnormal.trans
      (Subgroup.subgroupOf_mono C hAB) hmapped hsubBC.2⟩

private theorem exists_twoSubgroup_for_alignment_52assembly
    {G : Type u} [Group G] [Finite G]
    (S0 : Sylow 2 G) (K M : Subgroup G)
    (hM : FiveTwoMinimalBadData (baumannIn (S0 : Subgroup G)) K M)
    (hcomm : K = ⁅K, baumannIn (S0 : Subgroup G)⁆)
    (hnorm : ∀ D : Subgroup G, IsPGroup 2 D →
      baumannIn (S0 : Subgroup G) ⊔ K ≤
        Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.normalizer (K : Set G)) :
    ∃ Q : Subgroup G,
      IsPGroup 2 Q ∧
      Q ≤ Subgroup.normalizer (K : Set G) ∧
      baumannIn (S0 : Subgroup G) ≤ Q ∧
      Q = twoCoreIn M ⊔ (twoCoreIn K ⊔ baumannIn (S0 : Subgroup G)) := by
  let B : Subgroup G := baumannIn (S0 : Subgroup G)
  let OM : Subgroup G := twoCoreIn M
  let OK : Subgroup G := twoCoreIn K
  have hBp : IsPGroup 2 B := S0.isPGroup'.to_le inf_le_left
  have hOMp : IsPGroup 2 OM := twoCoreIn_isPGroup_52assembly M
  have hOKp : IsPGroup 2 OK := twoCoreIn_isPGroup_52assembly K
  have hMnormOM : M ≤ Subgroup.normalizer (OM : Set G) :=
    le_normalizer_twoCoreIn_52assembly M
  have hOMnormK : OM ≤ Subgroup.normalizer (K : Set G) :=
    hnorm OM hOMp (hM.sup_le.trans hMnormOM)
  have hBnormK : B ≤ Subgroup.normalizer (K : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    simpa [B] using hcomm.symm.le
  have hBnormOK : B ≤ Subgroup.normalizer (OK : Set G) :=
    hBnormK.trans (normalizer_le_normalizer_twoCoreIn_52assembly K)
  have hOKBtwo : IsPGroup 2 (OK ⊔ B : Subgroup G) :=
    hOKp.to_sup_of_normal_left' hBp hBnormOK
  have hBnormOM : B ≤ Subgroup.normalizer (OM : Set G) :=
    le_sup_left.trans hM.sup_le |>.trans hMnormOM
  have hOMBtwo : IsPGroup 2 (OM ⊔ B : Subgroup G) :=
    hOMp.to_sup_of_normal_left' hBp hBnormOM
  have hOMnormB : OM ≤ Subgroup.normalizer (B : Set G) :=
    le_sup_left.trans (Stellmacher.twoSubgroup_le_normalizer_baumann
      S0 (OM ⊔ B) hOMBtwo (by
        change B ≤ OM ⊔ B
        exact le_sup_right))
  have hOMnormOK : OM ≤ Subgroup.normalizer (OK : Set G) :=
    hOMnormK.trans (normalizer_le_normalizer_twoCoreIn_52assembly K)
  have hOMnormOKB : OM ≤
      Subgroup.normalizer ((OK ⊔ B : Subgroup G) : Set G) :=
    le_normalizer_sup_52assembly OM OK B hOMnormOK hOMnormB
  let Q : Subgroup G := OM ⊔ (OK ⊔ B)
  have hQp : IsPGroup 2 Q :=
    hOMp.to_sup_of_normal_right' hOKBtwo hOMnormOKB
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) := by
    exact sup_le hOMnormK (sup_le
      (twoCoreIn_le_52assembly K |>.trans K.le_normalizer) hBnormK)
  refine ⟨Q, hQp, hQNK, le_sup_right.trans le_sup_right, ?_⟩
  rfl

private theorem exists_alignment_52assembly
    {G : Type u} [Group G] [Finite G]
    (S0 : Sylow 2 G) (P K M : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup G) : Set G))
      (S0 : Subgroup G))
    (hKP : K ≤ P)
    (hlocal : ∀ X : Subgroup G,
      IsTwoLocal X → baumannIn (S0 : Subgroup G) ≤ X →
        Group.IsSolvable X ∧ Stellmacher.IsCharacteristicTwoType X)
    (hcomm : K = ⁅K, baumannIn (S0 : Subgroup G)⁆)
    (hKne : K ≠ ⊥)
    (hlarger : K ≠ twoResidualIn P →
      ∀ X : Subgroup G, IsTwoLocal X →
        baumannIn (S0 : Subgroup G) ⊔ twoResidualIn P ≤ X →
        SubnormalIn (twoResidualIn P) X)
    (hnorm : ∀ D : Subgroup G, IsPGroup 2 D →
      baumannIn (S0 : Subgroup G) ⊔ K ≤
        Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.normalizer (K : Set G))
    (hM : FiveTwoMinimalBadData (baumannIn (S0 : Subgroup G)) K M) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧
      twoCoreIn M ≤ T ∧
      twoCoreIn K ≤ T ∧
      baumannIn (S0 : Subgroup G) ≤ T ∧
      IsSylowTwoIn
        (T ⊓ Subgroup.normalizer (K : Set G))
        (Subgroup.normalizer (K : Set G)) ∧
      SubnormalIn K (Subgroup.centralizer
        (Stellmacher.omegaOneCenterAmbient T : Set G)) := by
  let B : Subgroup G := baumannIn (S0 : Subgroup G)
  obtain ⟨Q, hQp, hQNK, hBQ, hQeq⟩ :=
    exists_twoSubgroup_for_alignment_52assembly S0 K M hM hcomm hnorm
  have hOMQ : twoCoreIn M ≤ Q := by
    rw [hQeq]
    exact le_sup_left
  have hOKQ : twoCoreIn K ≤ Q := by
    rw [hQeq]
    exact middle_le_sup_sup_52assembly (twoCoreIn M) (twoCoreIn K)
      (baumannIn (S0 : Subgroup G))
  obtain ⟨h, _hhB, hQT, hSylow, hKsub⟩ :=
    five_two_exists_centralizer_conjugate_containing S0 P K Q hP hKP hlocal
      hcomm hKne hlarger hQp hQNK (by simpa [B] using hBQ)
  let e : G ≃* G := MulAut.conj h
  let T : Subgroup G := (S0 : Subgroup G).map e.toMonoidHom
  have hQT' : Q ≤ T := by simpa [T, e] using hQT
  have hOMT : twoCoreIn M ≤ T := hOMQ.trans hQT'
  have hOKT : twoCoreIn K ≤ T := hOKQ.trans hQT'
  have hBT : B ≤ T := hBQ.trans hQT'
  have hOmegaMap :
      (Stellmacher.omegaOneCenterAmbient (S0 : Subgroup G)).map e.toMonoidHom =
        Stellmacher.omegaOneCenterAmbient T := by
    simpa [T] using
      (Stellmacher.omegaOneCenterAmbient_map_injective
        e.toMonoidHom e.injective (S0 : Subgroup G)).symm
  have hCentMap :
      (Subgroup.centralizer
        (Stellmacher.omegaOneCenterAmbient (S0 : Subgroup G) : Set G)).map
          e.toMonoidHom =
        Subgroup.centralizer
          (Stellmacher.omegaOneCenterAmbient T : Set G) := by
    rw [centralizer_map_equiv_52assembly, hOmegaMap]
  refine ⟨T, S0.isPGroup'.map e.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hOMT
  · exact hOKT
  · simpa [B] using hBT
  · simpa [T, e] using hSylow
  · rw [← hCentMap]
    simpa only [omegaOneCenter, Stellmacher.omegaOneCenterAmbient] using hKsub

private theorem exists_aligned_minimal_bad_52assembly
    {G : Type u} [Group G] [Finite G]
    (S0 : Sylow 2 G) (P K U : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S0 : Subgroup G) : Set G))
      (S0 : Subgroup G))
    (hKP : K ≤ P)
    (hlocal : ∀ X : Subgroup G,
      IsTwoLocal X → baumannIn (S0 : Subgroup G) ≤ X →
        Group.IsSolvable X ∧ Stellmacher.IsCharacteristicTwoType X)
    (hcomm : K = ⁅K, baumannIn (S0 : Subgroup G)⁆)
    (hKne : K ≠ ⊥)
    (hlarger : K ≠ twoResidualIn P →
      ∀ X : Subgroup G, IsTwoLocal X →
        baumannIn (S0 : Subgroup G) ⊔ twoResidualIn P ≤ X →
        SubnormalIn (twoResidualIn P) X)
    (hnorm : ∀ D : Subgroup G, IsPGroup 2 D →
      baumannIn (S0 : Subgroup G) ⊔ K ≤
        Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.normalizer (K : Set G))
    (hUlocal : IsTwoLocal U)
    (hBKU : baumannIn (S0 : Subgroup G) ⊔ K ≤ U)
    (hbad : ¬ SubnormalIn K U) :
    ∃ M T : Subgroup G,
      FiveTwoMinimalBadData (baumannIn (S0 : Subgroup G)) K M ∧
      IsPGroup 2 T ∧
      twoCoreIn M ≤ T ∧
      twoCoreIn K ≤ T ∧
      baumannIn (S0 : Subgroup G) ≤ T ∧
      IsSylowTwoIn
        (T ⊓ Subgroup.normalizer (K : Set G))
        (Subgroup.normalizer (K : Set G)) ∧
      SubnormalIn K (Subgroup.centralizer
        (Stellmacher.omegaOneCenterAmbient T : Set G)) := by
  obtain ⟨M, hM⟩ := exists_five_two_minimal_bad
    (baumannIn (S0 : Subgroup G)) K U hUlocal hBKU hbad hlocal
  obtain ⟨T, hTtwo, hOMT, hOKT, hBT, hSylow, hKsub⟩ :=
    exists_alignment_52assembly S0 P K M hP hKP hlocal hcomm hKne
      hlarger hnorm hM
  exact ⟨M, T, hM, hTtwo, hOMT, hOKT, hBT, hSylow, hKsub⟩

/-- **Stellmacher (5.2).**  The subnormality conclusion for a subgroup `K`
of a member of `𝒫*(C,S₀)`. -/
public theorem lemma_five_two
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H)
    (Z0 B0 C P K : Subgroup H)
    (hZ0 : Z0 = omegaOneCenter (S0 : Subgroup H))
    (hB0 : B0 = baumannIn (S0 : Subgroup H))
    (hC : C = Subgroup.centralizer (Z0 : Set H))
    (hP : P ∈ PStarFamily C (S0 : Subgroup H))
    (hK : K ≤ P)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U → B0 ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U)
    (hcomm : K = ⁅K, B0⁆) :
    ∀ U : Subgroup H, IsTwoLocal U →
      B0 ⊔ K ≤ U → SubnormalIn K U := by
  subst Z0
  subst B0
  subst C
  let S : Subgroup H := (S0 : Subgroup H)
  let B : Subgroup H := baumannIn S
  let R : Subgroup H := twoResidualIn P
  let C : Subgroup H := Subgroup.centralizer (omegaOneCenter S : Set H)
  let μ : Subgroup H → ℕ := fun A ↦ Nat.card H - Nat.card A
  have main : ∀ A : Subgroup H, A ≤ P → A = ⁅A, B⁆ →
      ∀ U : Subgroup H, IsTwoLocal U →
        B ⊔ A ≤ U → SubnormalIn A U := by
    intro A
    induction A using (measure μ).wf.induction with
    | h A ih =>
      intro hAP hAcomm U hUlocal hBAU
      obtain ⟨hsolv, hRsubC, hAsubR, hnorm⟩ :=
        five_two_initial_reductions S0 P A (by simpa [S, C] using hP)
          hAP (by simpa [S, B] using hlocal) (by simpa [B] using hAcomm)
      by_contra hbad
      have hAne : A ≠ ⊥ := by
        intro hbot
        subst A
        apply hbad
        refine ⟨bot_le, ?_⟩
        simpa only [Subgroup.bot_subgroupOf] using
          (Subgroup.IsSubnormal.bot : (⊥ : Subgroup U).IsSubnormal)
      have hRP : R ≤ P := Subgroup.map_subtype_le _
      have hlarger : A ≠ R →
          ∀ X : Subgroup H, IsTwoLocal X →
            B ⊔ R ≤ X → SubnormalIn R X := by
        intro hAneR X hXlocal hBRX
        have hAltR : A < R := lt_of_le_of_ne hAsubR.1 hAneR
        have hcardlt : Nat.card A < Nat.card R := by
          have hset : (A : Set H) ⊂ (R : Set H) := hAltR
          simpa using Set.Finite.card_lt_card (Set.toFinite (R : Set H)) hset
        have hRcard : Nat.card R ≤ Nat.card H := Subgroup.card_le_card_group R
        have hμ : μ R < μ A := by
          dsimp [μ]
          omega
        have hRcomm : R = ⁅R, B⁆ := by
          symm
          simpa [S, B, R] using
            five_two_residual_baumann_commutator S0 P A
              (by simpa [S, C] using hP) hsolv hAP
              (by simpa [B] using hAcomm) hAne
        exact ih R hμ hRP hRcomm X hXlocal hBRX
      obtain ⟨M, T0, hM, hT0p, hOMT0, hOAT0, hBT0, hSylow, hAsubZh⟩ :=
        exists_aligned_minimal_bad_52assembly S0 P A U
          (by simpa [S, C] using hP) hAP
          (by simpa [S, B] using hlocal) (by simpa [B] using hAcomm)
          hAne (by simpa [B, R] using hlarger) (by simpa [B] using hnorm)
          hUlocal (by simpa [B] using hBAU) hbad
      let OM : Subgroup H := twoCoreIn M
      let OA : Subgroup H := twoCoreIn A
      have hBp : IsPGroup 2 B := S0.isPGroup'.to_le inf_le_left
      let Zhat : Subgroup H := Stellmacher.omegaOneCenterAmbient T0
      have hZhatOM : Zhat ≤ OM := by
        intro z hz
        have hz' : z ∈ Stellmacher.omegaOneCenterAmbient T0 := hz
        obtain ⟨_, _, hzcent⟩ :=
          (Stellmacher.mem_omegaOneCenterAmbient_iff T0 z).mp hz'
        apply hM.centralizer_core_le
        rw [Subgroup.mem_centralizer_iff]
        intro o ho
        exact hzcent o (hOMT0 ho)
      have hZhatM : Zhat ≤ M := hZhatOM.trans (twoCoreIn_le_52assembly M)
      have hOMnormalM : (OM.subgroupOf M).Normal :=
        twoCoreIn_normal_subgroupOf_52assembly M
      let VM : Subgroup M := Subgroup.normalClosure (Zhat.subgroupOf M : Set M)
      have hVMelem : IsElementaryAbelian 2 VM := by
        simpa [VM, Zhat] using
          (Stellmacher.SectionThree.omegaOneCenter_normalClosure_isElementaryAbelian
            T0 M OM (twoCoreIn_le_52assembly M) hOMT0 hOMnormalM (by
              simpa [Zhat] using hZhatOM))
      let V : Subgroup H := VM.map M.subtype
      have hVMle : V ≤ M := Subgroup.map_subtype_le VM
      have hVnormalM : (V.subgroupOf M).Normal := by
        simpa [V, subgroupOf_map_subtype_eq] using
          (inferInstance : VM.Normal)
      have hVelem : IsElementaryAbelian 2 V := by
        let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        let _ : IsElementaryAbelian 2 VM := hVMelem
        exact IsElementaryAbelian.map M.subtype
      have hZhatV : Zhat ≤ V := by
        intro z hz
        refine ⟨⟨z, hZhatM hz⟩, ?_, rfl⟩
        exact Subgroup.subset_normalClosure hz
      let Cfull : Subgroup H := Subgroup.centralizer (V : Set H)
      have hCfullZh : Cfull ≤ Subgroup.centralizer (Zhat : Set H) := by
        change Subgroup.centralizer (V : Set H) ≤ _
        exact Subgroup.centralizer_le hZhatV
      let C0 : Subgroup M := Subgroup.centralizer (VM : Set M)
      let C0amb : Subgroup H := C0.map M.subtype
      have hC0amb : C0amb = M ⊓ Cfull := by
        ext x
        constructor
        · rintro ⟨xm, hxm, rfl⟩
          refine ⟨xm.property, ?_⟩
          change (xm : H) ∈ Subgroup.centralizer (V : Set H)
          rw [Subgroup.mem_centralizer_iff]
          rintro _ ⟨v, hv, rfl⟩
          exact congrArg (fun y : M ↦ (y : H))
            (Subgroup.mem_centralizer_iff.mp hxm v hv)
        · rintro ⟨hxM, hxcent⟩
          let xm : M := ⟨x, hxM⟩
          refine ⟨xm, ?_, rfl⟩
          change xm ∈ Subgroup.centralizer (VM : Set M)
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          apply M.subtype_injective
          exact Subgroup.mem_centralizer_iff.mp hxcent (v : H)
            (Subgroup.mem_map_of_mem M.subtype hv)
      have hAnCfull : ¬ A ≤ Cfull := by
        intro hACfull
        have hAM : A ≤ M := le_sup_right.trans hM.sup_le
        have hAC0amb : A ≤ C0amb := by
          rw [hC0amb]
          exact le_inf hAM hACfull
        have hC0ambZh : C0amb ≤ Subgroup.centralizer (Zhat : Set H) := by
          rw [hC0amb]
          exact inf_le_right.trans hCfullZh
        have hAsubC0amb : SubnormalIn A C0amb :=
          subnormalIn_restrict_52assembly hAC0amb hC0ambZh hAsubZh
        have hC0ambM : C0amb ≤ M := by
          rw [hC0amb]
          exact inf_le_left
        have hC0normalM : (C0amb.subgroupOf M).Normal := by
          simpa [C0amb, subgroupOf_map_subtype_eq] using
            (inferInstance : C0.Normal)
        have hC0subM : SubnormalIn C0amb M :=
          ⟨hC0ambM, hC0normalM.isSubnormal⟩
        exact hM.not_subnormal
          (subnormalIn_trans_52assembly hAC0amb hC0ambM hAsubC0amb hC0subM)
      have hthree : Stellmacher.SectionThree.Hypotheses H S := by
        simpa [S] using sectionThreeHypotheses_of_pstar_52assembly S0 P
          (by simpa [S, C] using hP)
      have hPset : P ∈ Stellmacher.SectionThree.PSet (⊤ : Subgroup H) S := by
        rw [← pFamily_iff_pSet]
        exact ⟨⟨le_top, hP.1.1.2⟩, hP.1.2⟩
      have hOmega : ⁅Stellmacher.omegaOneCenterAmbient S,
          Stellmacher.twoResidualAmbient P⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        exact (Subgroup.map_subtype_le _).trans (by
          simpa [S, C, omegaOneCenter,
            Stellmacher.omegaOneCenterAmbient] using hP.1.1.1)
      have hcenterComm :
          ⁅(Subgroup.center (twoCoreIn A)).map (twoCoreIn A).subtype, A⁆ = ⊥ := by
        change ⁅(Subgroup.center (Stellmacher.twoCoreAmbient A)).map
          (Stellmacher.twoCoreAmbient A).subtype, A⁆ = ⊥
        exact
          Stellmacher.SectionThree.subnormal_twoCore_center_centralizes_of_residual_omega_central
            S hthree P hPset hsolv hOmega A ⟨hAsubR.1, hAsubR.2⟩
      have hcoreNotAmbient : ¬ twoCoreIn A ≤ Cfull :=
        five_two_twoCore_not_le_centralizer B A M V Cfull hM.sup_le hVMle
          hVnormalM hVelem hBp rfl hAnCfull (by simpa [B] using hnorm)
          hcenterComm hAcomm.symm
      have hAM : A ≤ M := le_sup_right.trans hM.sup_le
      have hBM : B ≤ M := le_sup_left.trans hM.sup_le
      let KM : Subgroup M := A.subgroupOf M
      let BM : Subgroup M := B.subgroupOf M
      let Tamb : Subgroup H := T0 ⊓ M
      let TM : Subgroup M := Tamb.subgroupOf M
      let ZM : Subgroup M := Zhat.subgroupOf M
      have hKMmap : KM.map M.subtype = A := by
        simpa [KM] using Subgroup.map_subgroupOf_eq_of_le hAM
      have hBMmap : BM.map M.subtype = B := by
        simpa [BM] using Subgroup.map_subgroupOf_eq_of_le hBM
      have hcoreKMmap : (twoCoreIn KM).map M.subtype = twoCoreIn A := by
        simpa [KM] using
          twoCoreIn_subgroupOf_map_subtype_52assembly A M hAM
      have hcoreNotM : ¬ twoCoreIn KM ≤ C0 := by
        intro hle
        apply hcoreNotAmbient
        have hm := Subgroup.map_mono (f := M.subtype) hle
        rw [hcoreKMmap] at hm
        exact hm.trans (by
          change C0amb ≤ Cfull
          rw [hC0amb]
          exact inf_le_right)
      have hBMT : BM ≤ TM := by
        intro b hb
        exact ⟨hBT0 hb, b.property⟩
      have hcoreKMT : twoCoreIn KM ≤ TM := by
        intro x hx
        have hxA : (x : H) ∈ twoCoreIn A := by
          rw [← hcoreKMmap]
          exact Subgroup.mem_map_of_mem M.subtype hx
        exact ⟨hOAT0 hxA, x.property⟩
      have hTtwo : IsPGroup 2 TM := by
        have hTambTwo : IsPGroup 2 Tamb := hT0p.to_le inf_le_left
        exact hTambTwo.of_equiv
          (Subgroup.subgroupOfEquivOfLe (show Tamb ≤ M from inf_le_right)).symm
      have hKMT : twoCoreIn KM ⊔ BM ≤ TM := sup_le hcoreKMT hBMT
      have hcommM : KM = ⁅KM, BM⁆ := by
        apply Subgroup.map_injective M.subtype_injective
        rw [Subgroup.map_commutator, hKMmap, hBMmap]
        exact hAcomm
      have hBnormKM : BM ≤ Subgroup.normalizer (KM : Set M) := by
        apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
        exact hcommM.symm.le
      have hVMnormal : VM.Normal := inferInstance
      let _ : VM.Normal := hVMnormal
      have hC0normal : C0.Normal := by
        dsimp only [C0]
        infer_instance
      let _ : C0.Normal := hC0normal
      have hVcore : VM ≤ pCore 2 M := by
        let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        let _ : IsElementaryAbelian 2 VM := hVMelem
        exact le_sSup ⟨hVMnormal, IsElementaryAbelian.isPGroup 2 VM⟩
      have hcoreCentralZ : pCore 2 M ≤
          Subgroup.centralizer (ZM : Set M) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hz' : (z : H) ∈ Stellmacher.omegaOneCenterAmbient T0 := hz
        obtain ⟨_, _, hzcent⟩ :=
          (Stellmacher.mem_omegaOneCenterAmbient_iff T0 (z : H)).mp hz'
        apply M.subtype_injective
        exact (hzcent (x : H) (hOMT0
          (Subgroup.mem_map_of_mem M.subtype hx))).symm
      have hcoreCommZ : ⁅pCore 2 M, ZM⁆ ≤ (⊥ : Subgroup M) :=
        le_bot_iff.mpr
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcoreCentralZ)
      have hcoreCommV : ⁅pCore 2 M, VM⁆ ≤ (⊥ : Subgroup M) := by
        change ⁅pCore 2 M, Subgroup.normalClosure (ZM : Set M)⁆ ≤ ⊥
        exact Subgroup.commutator_normalClosure_le_of_normal
          (pCore 2 M) ZM ⊥ hcoreCommZ
      have hcoreC0 : pCore 2 M ≤ C0 := by
        change pCore 2 M ≤ Subgroup.centralizer (VM : Set M)
        apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        exact le_bot_iff.mp hcoreCommV
      have hcoreMne : pCore 2 M ≠ ⊥ := by
        intro hbot
        apply hM.core_ne
        change (pCore 2 M).map M.subtype = ⊥
        rw [hbot, Subgroup.map_bot]
      have hMeven : Even (Nat.card M) := by
        let _ : Nontrivial (pCore 2 M) :=
          (Subgroup.nontrivial_iff_ne_bot (pCore 2 M)).2 hcoreMne
        obtain ⟨n, hn, hcard⟩ :=
          (pCore_isPGroup (G := M) (p := 2)).nontrivial_iff_card.mp inferInstance
        apply even_iff_two_dvd.mpr
        apply (show 2 ∣ Nat.card (pCore 2 M) by
          rw [hcard]
          exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)).trans
        exact Subgroup.card_subgroup_dvd_card (pCore 2 M)
      have hcentralCoreM : Subgroup.centralizer (pCore 2 M : Set M) ≤
          pCore 2 M := by
        intro x hx
        have hxamb : (x : H) ∈ Subgroup.centralizer (OM : Set H) := by
          rw [Subgroup.mem_centralizer_iff]
          rintro _ ⟨y, hy, rfl⟩
          exact congrArg (fun z : M ↦ (z : H))
            (Subgroup.mem_centralizer_iff.mp hx y hy)
        obtain ⟨y, hy, hyx⟩ := hM.centralizer_core_le hxamb
        have hyeq : y = x := M.subtype_injective hyx
        simpa [hyeq] using hy
      have hMsection : Stellmacher.SectionTwo.Hypotheses M :=
        ⟨hM.solvable, hMeven, hcentralCoreM⟩
      obtain ⟨SM, hTMSM⟩ := hTtwo.exists_le_sylow
      let SMamb : Subgroup H := (SM : Subgroup M).map M.subtype
      have hBMSM : BM ≤ (SM : Subgroup M) := hBMT.trans hTMSM
      have hBSMamb : B ≤ SMamb := by
        rw [← hBMmap]
        exact Subgroup.map_mono hBMSM
      have hSMambTwo : IsPGroup 2 SMamb := SM.isPGroup'.map M.subtype
      obtain ⟨_hJamb, hBaumannAmb⟩ :=
        Stellmacher.twoSubgroup_thompson_baumann_eq S0 SMamb hSMambTwo (by
          simpa [B, baumannIn, omegaOneCenter,
            Stellmacher.omegaOneCenterAmbient] using hBSMamb)
      have hBaumannMap :
          (baumannIn (SM : Subgroup M)).map M.subtype = baumannIn SMamb := by
        simpa [SMamb] using
          baumannIn_map_subtype_52assembly M (SM : Subgroup M)
      have hBnative : BM = baumannIn (SM : Subgroup M) := by
        apply Subgroup.map_injective M.subtype_injective
        rw [hBMmap, hBaumannMap]
        simpa [B, S, baumannIn, omegaOneCenter,
          Stellmacher.omegaOneCenterAmbient] using hBaumannAmb.symm
      have hVSM : VM ≤ (SM : Subgroup M) :=
        hVcore.trans (fitting_pCore_le_sylow SM)
      have hBsource : BM = (SM : Subgroup M) ⊓
          Subgroup.centralizer
            (Stellmacher.omegaOneCenterAmbient
              (Stellmacher.elementaryAbelianMaxJ (SM : Subgroup M)) : Set M) := by
        simpa only [baumannIn, omegaOneCenter,
          Stellmacher.omegaOneCenterAmbient] using hBnative
      have hJnot : ¬ Stellmacher.elementaryAbelianMaxJ (SM : Subgroup M) ≤ C0 :=
        five_two_thompson_not_le_centralizer (SM : Subgroup M) VM C0 BM KM
          hVMelem hVSM rfl hBsource hcoreNotM hcommM.symm
      have hcommBaumann : KM = ⁅KM, baumannIn (SM : Subgroup M)⁆ := by
        simpa [hBnative] using hcommM
      have hWnormKM := five_two_quotient_twoCore_le_normalizer
        SM C0 KM hcommBaumann
      obtain ⟨r, hrprime, hrne, hAodd⟩ :=
        Stellmacher.SectionThree.subnormal_quotient_twoCore_is_odd_pGroup
          S hthree P hPset hsolv A ⟨hAsubR.1, hAsubR.2⟩
      have hKModd : IsPGroup r (KM ⧸ pCore 2 KM) := by
        let _ : Fact r.Prime := ⟨hrprime⟩
        let eKM : KM ≃* A := Subgroup.subgroupOfEquivOfLe hAM
        exact quotient_pCore_isPGroup_of_equiv_52assembly 2 r eKM.symm hAodd
      let KCM : Subgroup M := KM ⊔ C0
      have hKCMmap : KCM.map M.subtype = A ⊔ C0amb := by
        rw [show KCM = KM ⊔ C0 by rfl, Subgroup.map_sup, hKMmap]
      have hAsubKCamb : SubnormalIn A (A ⊔ C0amb) := by
        apply subnormalIn_restrict_52assembly le_sup_left
          (sup_le hAsubZh.1 (by
            change C0amb ≤ Subgroup.centralizer (Zhat : Set H)
            rw [hC0amb]
            exact inf_le_right.trans hCfullZh)) hAsubZh
      have hKsubKC : (KM.subgroupOf (KM ⊔ C0)).IsSubnormal := by
        apply isSubnormal_subgroupOf_of_map_subtype_52assembly
          M KCM A hAM (by
            change KM ≤ KCM
            exact le_sup_left)
        rw [hKCMmap]
        exact hAsubKCamb
      have hproperM : ∀ X : Subgroup M,
          (BM ⊔ KM) ⊔ pCore 2 M ≤ X → X < ⊤ →
            (KM.subgroupOf X).IsSubnormal := by
        intro X hle hlt
        let Xamb : Subgroup H := X.map M.subtype
        have hXambLeM : Xamb ≤ M := Subgroup.map_subtype_le X
        have hXambNeM : Xamb ≠ M := by
          intro heq
          have hXtop : X = ⊤ := by
            apply Subgroup.map_injective M.subtype_injective
            have heq' : X.map M.subtype = M := by simpa [Xamb] using heq
            rw [heq', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
          exact (ne_of_lt hlt) hXtop
        have hXambLtM : Xamb < M := lt_of_le_of_ne hXambLeM hXambNeM
        have hcontain : (B ⊔ A) ⊔ twoCoreIn M ≤ Xamb := by
          have hm := Subgroup.map_mono (f := M.subtype) hle
          simpa [Xamb, Subgroup.map_sup, hBMmap, hKMmap, twoCoreIn] using hm
        have hsub := hM.proper_subnormal Xamb hcontain hXambLtM
        have hKMX : KM ≤ X := by
          exact le_sup_right.trans (le_sup_left.trans hle)
        exact isSubnormal_subgroupOf_of_map_subtype_52assembly
          M X A hAM hKMX (by simpa [Xamb] using hsub)
      have hTcentralZ : TM ≤ Subgroup.centralizer (ZM : Set M) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hz' : (z : H) ∈ Stellmacher.omegaOneCenterAmbient T0 := hz
        obtain ⟨_, _, hzcent⟩ :=
          (Stellmacher.mem_omegaOneCenterAmbient_iff T0 (z : H)).mp hz'
        apply M.subtype_injective
        exact (hzcent (x : H) hx.1).symm
      have hWimage : pCore 2 (M ⧸ C0) ≤
          TM.map (QuotientGroup.mk' C0) :=
        five_two_quotient_twoCore_le_sylow_image C0 KM BM TM hM.solvable
          hcoreC0 hKsubKC hcoreNotM hproperM
          ⟨r, hrprime, hrne, hKModd⟩ hBnormKM hWnormKM hTtwo hKMT
      have hWbot : pCore 2 (M ⧸ C0) = ⊥ :=
        quotient_twoCore_eq_bot_of_le_seed_centralizer
          ZM VM C0 TM rfl rfl hTcentralZ hWimage
      have hendpoint := five_two_source_local_quotient_endpoint
        SM VM C0 BM KM hVMelem hVcore rfl hMsection hWbot
          hBsource hJnot hcommM
      let q : M →* M ⧸ C0 := QuotientGroup.mk' C0
      let Kbar : Subgroup (M ⧸ C0) := KM.map q
      have hKbarCoreBot : pCore 2 Kbar = ⊥ := by
        simpa [q, Kbar] using hendpoint.2
      let fK : KM →* Kbar :=
        (q.comp KM.subtype).codRestrict Kbar (fun x ↦
          Subgroup.mem_map_of_mem q x.property)
      have hfKsurj : Function.Surjective fK := by
        rintro ⟨y, hy⟩
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      have hcoreMap : (pCore 2 KM).map fK ≤ pCore 2 Kbar := by
        exact le_sSup ⟨Subgroup.Normal.map (H := pCore 2 KM)
          inferInstance fK hfKsurj, (pCore_isPGroup (G := KM) (p := 2)).map fK⟩
      have hcoreKer : twoCoreIn KM ≤ C0 := by
        rintro x ⟨k, hk, hkx⟩
        have hy : fK k ∈ (pCore 2 KM).map fK :=
          Subgroup.mem_map_of_mem fK hk
        have hybot : fK k ∈ (⊥ : Subgroup Kbar) := by
          rw [← hKbarCoreBot]
          exact hcoreMap hy
        have hyone : fK k = 1 := by simpa using hybot
        have hqone : q (k : M) = 1 := congrArg Subtype.val hyone
        have hxker : x ∈ q.ker := by
          rw [MonoidHom.mem_ker]
          rw [← hkx]
          exact hqone
        simpa [q, QuotientGroup.ker_mk'] using hxker
      exact hcoreNotM hcoreKer
  simpa [B, S] using main K hK hcomm

end Stellmacher.SectionsFiveToSeven
