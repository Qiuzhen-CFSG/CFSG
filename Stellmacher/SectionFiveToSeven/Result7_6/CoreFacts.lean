module

public import Stellmacher.SectionFiveToSeven.Result7_5

/-!
# Residual and 2-core identities for the first critical edge

The residual 2-core of a local group is its residual intersected with its
2-core. Normality and the maximality of the 2-core prove both containments.
The companion facts transport normality, recover the local group from its
residual and Sylow subgroup, and control their commutators. These are the
local algebraic reductions used in Stellmacher (7.6).

Source: B. Stellmacher, Journal of Algebra 190 (1997), Lemma (7.6),
pp. 35–36; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven.SevenSix

open CosetGraphContext

universe u v

public theorem twoCoreIn_le
    {G : Type u} [Group G] (P : Subgroup G) :
    twoCoreIn P ≤ P := by
  rintro x ⟨y, hy, rfl⟩
  exact y.2

public theorem twoCoreIn_normal
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreIn P).subgroupOf P).Normal := by
  rw [twoCoreIn, subgroupOf_map_subtype_eq]
  infer_instance

public theorem twoResidualIn_le
    {G : Type u} [Group G] (P : Subgroup G) :
    twoResidualIn P ≤ P := by
  rintro x ⟨y, hy, rfl⟩
  exact y.2

public theorem stabilizer_le_normalizer_q
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (q Gamma d : Set G) := by
  rw [q, Gamma.twoCoreAt_def]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 (stabilizer Gamma d)))).mp
      (twoCoreIn_normal _)

public theorem twoResidualIn_normal
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoResidualIn P).subgroupOf P).Normal := by
  rw [twoResidualIn, twoResidualAmbient, subgroupOf_map_subtype_eq]
  unfold twoResidualSubgroup
  rw [sInf_eq_iInf]
  exact Subgroup.normal_iInf_normal (fun N ↦
    Subgroup.normal_iInf_normal (fun hN ↦ hN.1))

private theorem twoResidualSubgroup_eq_hktPResidual
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualSubgroup P = BenderSuzuki.External.hktPResidual 2 P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRnormal : (BenderSuzuki.External.hktPResidual 2 P).Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : (BenderSuzuki.External.hktPResidual 2 P).Normal := hRnormal
  apply le_antisymm
  · rw [twoResidualSubgroup]
    apply sInf_le
    refine ⟨hRnormal, ?_⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
      (BenderSuzuki.External.hktPResidual_quotient_isPGroup
        (q := 2) (Q := P))
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let _ : N.Normal := hN.1
    apply BenderSuzuki.External.hktPResidual_le N hN.1 ?_ hx
    rw [IsPGroup.iff_card]
    obtain ⟨n, hn⟩ := hN.2
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩

public theorem twoResidualIn_sup_sylow
    {G : Type u} [Group G] [Finite G]
    {W P : Subgroup G} (hWP : IsSylowTwoIn W P) :
    twoResidualIn P ⊔ W = P := by
  classical
  obtain ⟨hWleP, T, hTmap⟩ := hWP
  let R : Subgroup P := BenderSuzuki.External.hktPResidual 2 P
  have hRnormal : R.Normal :=
    BenderSuzuki.External.hktPResidual_normal
  let _ : R.Normal := hRnormal
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRTtop : R ⊔ (T : Subgroup P) = ⊤ := by
    let qR : P →* P ⧸ R := QuotientGroup.mk' R
    have hquotR : IsPGroup 2 (P ⧸ R) :=
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
    let Tbar : Sylow 2 (P ⧸ R) :=
      T.mapSurjective (QuotientGroup.mk'_surjective R)
    have hTbarTop : (Tbar : Subgroup (P ⧸ R)) = ⊤ := by
      symm
      exact Tbar.is_maximal' (hquotR.to_subgroup ⊤) le_top
    have hmapT : (T : Subgroup P).map qR = ⊤ := by
      simpa [Tbar, qR] using hTbarTop
    rw [sup_comm]
    calc
      (T : Subgroup P) ⊔ R = (T : Subgroup P) ⊔ qR.ker := by
        rw [QuotientGroup.ker_mk']
      _ = ((T : Subgroup P).map qR).comap qR :=
        (Subgroup.comap_map_eq qR (T : Subgroup P)).symm
      _ = ⊤ := by rw [hmapT]; simp
  have hmapTop : ((R ⊔ (T : Subgroup P)).map P.subtype) = P := by
    rw [hRTtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [Subgroup.map_sup, hTmap] at hmapTop
  change (twoResidualSubgroup P).map P.subtype ⊔ W = P
  rw [twoResidualSubgroup_eq_hktPResidual]
  exact hmapTop

private theorem twoCoreIn_isPGroup
    {G : Type u} [Group G] (P : Subgroup G) :
    IsPGroup 2 (twoCoreIn P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

private theorem normal_pSubgroup_le_twoCoreIn
    {G : Type u} [Group G]
    (Q P : Subgroup G) (hQP : Q ≤ P)
    (hQp : IsPGroup 2 Q) (hQnormal : (Q.subgroupOf P).Normal) :
    Q ≤ twoCoreIn P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle
    _ = twoCoreIn P := rfl

public theorem twoCoreIn_normal_of_normal
    {G : Type u} [Group G] (A P : Subgroup G)
    (hAP : A ≤ P) (hAnormal : (A.subgroupOf P).Normal) :
    ((twoCoreIn A).subgroupOf P).Normal := by
  let AP : Subgroup P := A.subgroupOf P
  let f : A ≃* AP := (Subgroup.subgroupOfEquivOfLe hAP).symm
  have hcore : (pCore 2 A).map f.toMonoidHom = pCore 2 AP :=
    pCore_map_iso 2 f
  have hRleP : twoCoreIn A ≤ P := (twoCoreIn_le A).trans hAP
  have heq : (twoCoreIn A).subgroupOf P =
      (pCore 2 AP).map AP.subtype := by
    apply Subgroup.map_injective (f := P.subtype) P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hRleP, ← hcore,
      Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [heq]
  let _ : AP.Normal := by simpa [AP] using hAnormal
  let _ : (pCore 2 AP).Characteristic := pCore_characteristic
  exact ConjAct.normal_of_characteristic_of_normal

public theorem residual_core_eq_inter_core
    {G : Type u} [Group G] (P : Subgroup G) :
    twoCoreIn (twoResidualIn P) =
      twoResidualIn P ⊓ twoCoreIn P := by
  let E := twoResidualIn P
  let Q := twoCoreIn P
  let R := twoCoreIn E
  have hEleP : E ≤ P := twoResidualIn_le P
  have hQleP : Q ≤ P := twoCoreIn_le P
  have hEnormalP : (E.subgroupOf P).Normal := twoResidualIn_normal P
  have hQnormalP : (Q.subgroupOf P).Normal := twoCoreIn_normal P
  have hRnormalP : (R.subgroupOf P).Normal :=
    twoCoreIn_normal_of_normal E P hEleP hEnormalP
  have hRleP : R ≤ P := (twoCoreIn_le E).trans hEleP
  have hRleQ : R ≤ Q :=
    normal_pSubgroup_le_twoCoreIn R P hRleP
      (twoCoreIn_isPGroup E) hRnormalP
  have hE_normalizes_Q : E ≤ Subgroup.normalizer (Q : Set G) :=
    hEleP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hQleP).mp hQnormalP)
  have hEQnormalE : ((E ⊓ Q).subgroupOf E).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    exact (le_inf Subgroup.le_normalizer hE_normalizes_Q).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hEQp : IsPGroup 2 ↥(E ⊓ Q) :=
    IsPGroup.to_le (twoCoreIn_isPGroup P) inf_le_right
  have hEQleR : E ⊓ Q ≤ R :=
    normal_pSubgroup_le_twoCoreIn (E ⊓ Q) E inf_le_left hEQp hEQnormalE
  exact le_antisymm (le_inf (twoCoreIn_le E) hRleQ) hEQleR

public theorem residual_commutator_core_le
    {G : Type u} [Group G] (P : Subgroup G) :
    ⁅twoResidualIn P, twoCoreIn P⁆ ≤
      twoCoreIn (twoResidualIn P) := by
  have hEleP : twoResidualIn P ≤ P := twoResidualIn_le P
  have hQleP : twoCoreIn P ≤ P := twoCoreIn_le P
  have hEnormalP : ((twoResidualIn P).subgroupOf P).Normal :=
    twoResidualIn_normal P
  have hQnormalP : ((twoCoreIn P).subgroupOf P).Normal :=
    twoCoreIn_normal P
  have hPnormE : P ≤ Subgroup.normalizer (twoResidualIn P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEleP).mp hEnormalP
  have hPnormQ : P ≤ Subgroup.normalizer (twoCoreIn P : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQleP).mp hQnormalP
  have hcomm : ⁅twoResidualIn P, twoCoreIn P⁆ ≤
      twoResidualIn P ⊓ twoCoreIn P :=
    le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hQleP.trans hPnormE))
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hEleP.trans hPnormQ))
  exact hcomm.trans (le_of_eq (residual_core_eq_inter_core P).symm)

public theorem commutator_le_conjugateClosure
    {G : Type u} [Group G] (E R A : Subgroup G)
    (hE : E ≤ A) :
    ⁅E, R⁆ ≤ conjugateClosure R A := by
  rw [Subgroup.commutator_le]
  intro g hg r hr
  have hconj : g * r * g⁻¹ ∈ conjugateClosure R A := by
    apply Subgroup.subset_closure
    exact ⟨⟨g, hE hg⟩, ⟨r, hr⟩, rfl⟩
  have hr' : r ∈ conjugateClosure R A := by
    apply Subgroup.subset_closure
    exact ⟨⟨1, A.one_mem⟩, ⟨r, hr⟩, by simp⟩
  exact (conjugateClosure R A).mul_mem hconj
    ((conjugateClosure R A).inv_mem hr')

public theorem residual_le_conjugateClosure_of_commutator_eq
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (cp : CriticalPath Γ)
    (hcomm : ⁅e Γ cp.a, twoCoreIn (e Γ cp.firstStep)⁆ = e Γ cp.a) :
    e Γ cp.a ≤ conjugateClosure (twoCoreIn (e Γ cp.firstStep))
      (stabilizer Γ cp.a) := by
  rw [← hcomm]
  apply commutator_le_conjugateClosure
  change Γ.twoResidualAt cp.a ≤ Γ.vertexStabilizer cp.a
  rw [Γ.twoResidualAt_def]
  exact twoResidualIn_le _

end Stellmacher.SectionsFiveToSeven.SevenSix

