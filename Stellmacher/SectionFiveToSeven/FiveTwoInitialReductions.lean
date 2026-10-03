module

public import Stellmacher.SectionFiveToSeven.PFamilyBridge
public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.BaumannTwoOvergroupNormalizer
public import Stellmacher.SectionThree.ResidualSubgroupSubnormal
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# Initial reductions for Stellmacher (5.2)

This module assembles the first two assertions in the proof of Stellmacher
(5.2).  For a subgroup `K ≤ P` satisfying `[K,B(S₀)] = K`, every
2-subgroup normalized by `K B(S₀)` normalizes `K`.  Moreover `P` is
solvable, `O²(P)` is subnormal in the omega-center centralizer, and `K` is
subnormal in `O²(P)`.

The normalizer assertion combines weak closure of the Baumann subgroup with
the generic full-commutator normalizer transfer.  The commutator equality also
puts `K` in every normal subgroup of `P` having 2-group quotient, hence in
`O²(P)`.  Stellmacher (3.3)(a) then makes `K O₂(P)` subnormal in `P`;
the normalizer assertion makes `K` normal in that product, and restriction of
the resulting chain gives `K ◁◁ O²(P)`.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), proof of (5.2), p. 28, assertions (1)--(2).
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open BenderSuzuki.External

universe u

private theorem normal_subgroupOf_subgroupOf_52
    {G : Type u} [Group G] {H K L : Subgroup G}
    (hHK : H ≤ K) (_hKL : K ≤ L)
    (hN : (H.subgroupOf K).Normal) :
    ((H.subgroupOf L).subgroupOf (K.subgroupOf L)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono L hHK)]
  intro h k hh hk
  exact (Subgroup.normal_subgroupOf_iff hHK).mp hN
    (h : G) (k : G) hh hk

private theorem twoCoreIn_normal_subgroupOf_52
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreIn,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

private theorem le_normalizer_twoCoreIn_52
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreIn P : Set G) := by
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
      (twoCoreIn_normal_subgroupOf_52 P)

private theorem pstar_member_solvable_52
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G))
    (hlocal : ∀ U : Subgroup G,
      IsTwoLocal U → baumannIn (S : Subgroup G) ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U) :
    Group.IsSolvable P := by
  let N := Subgroup.normalizer (twoCoreIn P : Set G)
  have hNlocal : IsTwoLocal N := by
    exact ⟨twoCoreIn P, hP.1.1.2.2.1,
      (pCore_isPGroup (p := 2) (G := P)).map P.subtype, rfl⟩
  have hPN : P ≤ N := le_normalizer_twoCoreIn_52 P
  have hBS : baumannIn (S : Subgroup G) ≤ (S : Subgroup G) := inf_le_left
  have hSN : (S : Subgroup G) ≤ N := hP.1.1.2.1.1.trans hPN
  have hBN : baumannIn (S : Subgroup G) ≤ N := hBS.trans hSN
  let _ : Group.IsSolvable N := (hlocal N hNlocal hBN).1
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hPN) (Subgroup.inclusion_injective hPN)

private theorem fullCommutator_le_twoResidualIn_52
    {G : Type u} [Group G] [Finite G]
    (P K B : Subgroup G) (hKP : K ≤ P) (hBP : B ≤ P)
    (hcomm : ⁅K, B⁆ = K) :
    K ≤ twoResidualIn P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let KP : Subgroup P := K.subgroupOf P
  let BP : Subgroup P := B.subgroupOf P
  have hKPmap : KP.map P.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKP
  have hBPmap : BP.map P.subtype = B :=
    Subgroup.map_subgroupOf_eq_of_le hBP
  have hcommP : ⁅KP, BP⁆ = KP := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, hKPmap, hBPmap, hcomm]
  unfold twoResidualIn twoResidualAmbient
  intro x hx
  refine ⟨⟨x, hKP hx⟩, ?_, rfl⟩
  unfold twoResidualSubgroup
  apply (Subgroup.mem_sInf).2
  intro N hN
  have hNnormal : N.Normal := hN.1
  let _ : N.Normal := hNnormal
  obtain ⟨n, hn⟩ := hN.2
  have hquot : IsPGroup 2 (P ⧸ N) := by
    rw [IsPGroup.iff_card]
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  exact Subgroup.le_normal_of_quotient_isPGroup_of_eq_commutator
    KP BP N hquot hcommP hx

private theorem fiveTwoNormalizerProperty
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (K : Subgroup G)
    (hcomm : K = ⁅K, baumannIn (S : Subgroup G)⁆) :
    ∀ D : Subgroup G, IsPGroup 2 D →
      baumannIn (S : Subgroup G) ⊔ K ≤
        Subgroup.normalizer (D : Set G) →
      D ≤ Subgroup.normalizer (K : Set G) := by
  let B : Subgroup G := baumannIn (S : Subgroup G)
  have hBS : B ≤ (S : Subgroup G) := inf_le_left
  have hBp : IsPGroup 2 B := S.isPGroup'.to_le hBS
  intro D hDp hBKnormD
  have hBnormD : B ≤ Subgroup.normalizer (D : Set G) :=
    le_sup_left.trans hBKnormD
  have hDBp : IsPGroup 2 ↑(D ⊔ B) :=
    hDp.to_sup_of_normal_left' hBp hBnormD
  have hDnormB : D ≤ Subgroup.normalizer (B : Set G) := by
    have hDBnormB : D ⊔ B ≤ Subgroup.normalizer (B : Set G) := by
      simpa [B, baumannIn, omegaOneCenter,
        Stellmacher.omegaOneCenterAmbient] using
        (Stellmacher.twoSubgroup_le_normalizer_baumann S (D ⊔ B) hDBp (by
          simp only [B, baumannIn, omegaOneCenter,
            Stellmacher.omegaOneCenterAmbient]
          exact le_sup_right))
    exact le_sup_left.trans hDBnormB
  exact Subgroup.twoSubgroup_le_normalizer_of_full_commutator
    K B D hBp hDp (by simpa [B, sup_comm] using hBKnormD)
      hDnormB hcomm.symm

private theorem sectionThreeHypotheses_of_pstar_52
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

/-! The first two reductions in the proof of Stellmacher (5.2). -/
public theorem five_two_initial_reductions
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P K : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G))
    (hK : K ≤ P)
    (hlocal : ∀ U : Subgroup G,
      IsTwoLocal U → baumannIn (S : Subgroup G) ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U)
    (hcomm : K = ⁅K, baumannIn (S : Subgroup G)⁆) :
    Group.IsSolvable P ∧
      SubnormalIn (twoResidualIn P)
        (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G)) ∧
      SubnormalIn K (twoResidualIn P) ∧
      ∀ D : Subgroup G, IsPGroup 2 D →
        baumannIn (S : Subgroup G) ⊔ K ≤
          Subgroup.normalizer (D : Set G) →
        D ≤ Subgroup.normalizer (K : Set G) := by
  let S0 : Subgroup G := (S : Subgroup G)
  let B : Subgroup G := baumannIn S0
  let R : Subgroup G := twoResidualIn P
  let O : Subgroup G := twoCoreIn P
  have hsolv : Group.IsSolvable P := pstar_member_solvable_52 S P hP hlocal
  have hSP : S0 ≤ P := hP.1.1.2.1.1
  have hBP : B ≤ P := (inf_le_left : B ≤ S0).trans hSP
  have hKR : K ≤ R :=
    fullCommutator_le_twoResidualIn_52 P K B hK hBP hcomm.symm
  have hthree : Stellmacher.SectionThree.Hypotheses G S0 :=
    sectionThreeHypotheses_of_pstar_52 S P hP
  have hPset : P ∈ Stellmacher.SectionThree.PSet (⊤ : Subgroup G) S0 := by
    rw [← pFamily_iff_pSet]
    exact ⟨⟨le_top, hP.1.1.2⟩, hP.1.2⟩
  have hJsubP : Stellmacher.IsSubnormalIn (K ⊔ O) P := by
    simpa [S0, R, O, twoResidualIn, twoCoreIn,
      Stellmacher.twoCoreAmbient] using
      (Stellmacher.SectionThree.subgroup_sup_twoCore_subnormal_of_le_twoResidual
        S0 hthree P hPset hsolv K (by simpa [R, twoResidualIn] using hKR))
  have hBKnO : B ⊔ K ≤ Subgroup.normalizer (O : Set G) :=
    (sup_le hBP hK).trans (le_normalizer_twoCoreIn_52 P)
  have hOnK : O ≤ Subgroup.normalizer (K : Set G) :=
    fiveTwoNormalizerProperty S K hcomm O
      ((pCore_isPGroup (G := P) (p := 2)).map P.subtype)
      (by simpa [B] using hBKnO)
  have hKnormalJ : (K.subgroupOf (K ⊔ O)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    exact sup_le K.le_normalizer hOnK
  have hKsubP : (K.subgroupOf P).IsSubnormal := by
    exact Subgroup.IsSubnormal.step (K.subgroupOf P)
      ((K ⊔ O).subgroupOf P)
      (by intro k hk; exact (show K ≤ K ⊔ O from le_sup_left) hk)
      hJsubP.2
      (normal_subgroupOf_subgroupOf_52 le_sup_left hJsubP.1 hKnormalJ)
  have hRP : R ≤ P := Subgroup.map_subtype_le (twoResidualSubgroup P)
  let RP : Subgroup P := R.subgroupOf P
  let e : RP ≃* R := Subgroup.subgroupOfEquivOfLe hRP
  have hsubRP : ((K.subgroupOf P).subgroupOf RP).IsSubnormal :=
    hKsubP.subgroupOf
  have hmapped := Subgroup.IsSubnormal.map
    (f := e.toMonoidHom) e.surjective hsubRP
  have hmap : ((K.subgroupOf P).subgroupOf RP).map e.toMonoidHom =
      K.subgroupOf R := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hr
      let xP : P := ⟨r, hRP r.property⟩
      let xRP : RP := ⟨xP, r.property⟩
      exact ⟨xRP, hr, rfl⟩
  rw [hmap] at hmapped
  refine ⟨hsolv,
    pstar_residual_subnormal_in_omegaCentralizer S P hP,
    ⟨hKR, hmapped⟩, ?_⟩
  simpa [B] using fiveTwoNormalizerProperty S K hcomm

end Stellmacher.SectionsFiveToSeven
