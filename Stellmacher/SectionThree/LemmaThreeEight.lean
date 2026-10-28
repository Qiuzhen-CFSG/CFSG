module

public import Stellmacher.SectionThree.LemmaThreeEightDefs
public import Stellmacher.SectionThree.LemmaThreeSeven
public import Theory.GroupAction.MinimalNormal

/-!
# Stellmacher (3.8): the normal series attached to two local subgroups

For two solvable members `P₁,P₂ ∈ 𝒫(S)` generating `H`, let `N` be maximal
normal in `H` subject to neither `O²(Pᵢ)` lying in `N`.  This module constructs
the source's normal series `Q ≤ N ≤ H₀ ≤ H₁ ≤ H`.  Result (3.4) shows that
`Q = S ∩ N` lies in both local 2-cores and is normal in both generators;
maximality of `N` then proves that it is the largest subgroup of `S` normal in
`H`.  A finite minimal-subgroup argument constructs `H₀/N`, and adjoining at
most one residual gives the normal subgroup `H₁` with `H = S H₁`.

Source: `refs/latex/stellmacher-n-group.tex`, statement and proof (3.8),
journal p. 23.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionThree

open BenderSuzuki.External

universe u

private theorem twoResidualAmbient_eq_map_hktPResidual_local
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualAmbient P = (hktPResidual 2 P).map P.subtype := by
  have heq : twoResidualSubgroup P = hktPResidual 2 P := by
    apply le_antisymm
    · have hnormal : (hktPResidual 2 P).Normal := hktPResidual_normal
      let _ : (hktPResidual 2 P).Normal := hnormal
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
        (hktPResidual_quotient_isPGroup (Q := P) (q := 2))
      apply sInf_le
      refine ⟨hnormal, n, ?_⟩
      simpa [Subgroup.index_eq_card] using hn
    · apply le_sInf
      intro N hN
      have hnormal : N.Normal := hN.1
      let _ : N.Normal := hnormal
      obtain ⟨n, hn⟩ := hN.2
      apply hktPResidual_le N hnormal
      rw [IsPGroup.iff_card]
      exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  simp [twoResidualAmbient, heq]

private theorem twoResidual_sup_sylowImage_local
    {G : Type u} [Group G] [Finite G]
    {S P : Subgroup G} (hSylow : IsSylowSubgroupIn S P) :
    twoResidualAmbient P ⊔ S = P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hSylow
  let R : Subgroup P := hktPResidual 2 P
  let _ : R.Normal := hktPResidual_normal
  let q : P →* P ⧸ R := QuotientGroup.mk' R
  have hquot : IsPGroup 2 (P ⧸ R) := hktPResidual_quotient_isPGroup
  let Tbar : Sylow 2 (P ⧸ R) :=
    T.mapSurjective (QuotientGroup.mk'_surjective R)
  have hTbarTop : (Tbar : Subgroup (P ⧸ R)) = ⊤ := by
    exact (Tbar.3 (hquot.to_subgroup ⊤) le_top).symm
  have hsup : R ⊔ (T : Subgroup P) = ⊤ := by
    calc
      R ⊔ (T : Subgroup P) = q.ker ⊔ (T : Subgroup P) := by
        simp [q, QuotientGroup.ker_mk']
      _ = (T : Subgroup P) ⊔ q.ker := by rw [sup_comm]
      _ = ((T : Subgroup P).map q).comap q :=
        (Subgroup.comap_map_eq (f := q) (H := (T : Subgroup P))).symm
      _ = ⊤ := by
        rw [show (T : Subgroup P).map q = ⊤ by
          simpa [Tbar] using hTbarTop, Subgroup.comap_top]
  have hmapped := congrArg (fun K : Subgroup P => K.map P.subtype) hsup
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmapped
  rw [twoResidualAmbient_eq_map_hktPResidual_local, ← hT]
  exact hmapped

private theorem hktPResidual_le_ker_of_isPGroup_local
    {A B : Type u} [Group A] [Group B]
    [Finite A] [Finite B] (f : A →* B) (hB : IsPGroup 2 B) :
    hktPResidual 2 A ≤ f.ker := by
  have hrange2 : IsPGroup 2 f.range := hB.to_subgroup f.range
  have hquot2 : IsPGroup 2 (A ⧸ f.ker) :=
    hrange2.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact hktPResidual_le f.ker inferInstance hquot2

private theorem quotient_sup_isPGroup_of_right_local
    {G : Type u} [Group G] [Finite G]
    (D S : Subgroup G)
    [hN : (D.subgroupOf (D ⊔ S)).Normal]
    (hS2 : IsPGroup 2 S) :
    IsPGroup 2 (↑(D ⊔ S : Subgroup G) ⧸ D.subgroupOf (D ⊔ S)) := by
  classical
  let E : Subgroup G := D ⊔ S
  let N : Subgroup E := D.subgroupOf E
  let q : E →* E ⧸ N := QuotientGroup.mk' N
  let Sint : Subgroup E := S.subgroupOf E
  have hSint2 : IsPGroup 2 Sint :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hsup : N ⊔ Sint = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self E
  have hmapN : N.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := N)).2
    simp [q, QuotientGroup.ker_mk']
  have hmapS : Sint.map q = ⊤ := by
    have hmapped := congrArg (fun K : Subgroup E ↦ K.map q) hsup
    rw [Subgroup.map_sup, hmapN] at hmapped
    have htop : (⊤ : Subgroup E).map q = ⊤ := by
      simpa [MonoidHom.range_eq_map] using
        (MonoidHom.range_eq_top.mpr
          (QuotientGroup.mk'_surjective N) : q.range = ⊤)
    simpa [htop] using hmapped
  have htop2 : IsPGroup 2 (⊤ : Subgroup (E ⧸ N)) := by
    rw [← hmapS]
    exact hSint2.map q
  exact htop2.of_equiv Subgroup.topEquiv

private theorem twoResidualAmbient_le_left_of_le_sup_local
    {G : Type u} [Group G] [Finite G]
    (D S P : Subgroup G)
    (hDnormal : (D.subgroupOf (D ⊔ S)).Normal)
    (hS2 : IsPGroup 2 S) (hP : P ≤ D ⊔ S) :
    twoResidualAmbient P ≤ D := by
  classical
  let _ : (D.subgroupOf (D ⊔ S)).Normal := hDnormal
  let q : ↑(D ⊔ S : Subgroup G) →*
      ↑(D ⊔ S : Subgroup G) ⧸ D.subgroupOf (D ⊔ S) :=
    QuotientGroup.mk' (D.subgroupOf (D ⊔ S))
  have hquot2 : IsPGroup 2
      (↑(D ⊔ S) ⧸ D.subgroupOf (D ⊔ S)) :=
    quotient_sup_isPGroup_of_right_local D S hS2
  let i : P →* ↑(D ⊔ S : Subgroup G) := Subgroup.inclusion hP
  let f := q.comp i
  have hRker : hktPResidual 2 P ≤ f.ker :=
    hktPResidual_le_ker_of_isPGroup_local f hquot2
  rw [twoResidualAmbient_eq_map_hktPResidual_local]
  rintro _ ⟨x, hx, rfl⟩
  have hfx : f x = 1 := MonoidHom.mem_ker.mp (hRker hx)
  have hxi : i x ∈ D.subgroupOf (D ⊔ S) :=
    (QuotientGroup.eq_one_iff (N := D.subgroupOf (D ⊔ S))
      (x := i x)).mp hfx
  exact hxi

private theorem twoResidualAmbient_normal_in_self_local
    {G : Type u} [Group G] (P : Subgroup G) :
    (twoResidualAmbient P).subgroupOf P ≤ ⊤ ∧
      ((twoResidualAmbient P).subgroupOf P).Normal := by
  have hnormal : (twoResidualSubgroup P).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal (fun N =>
      Subgroup.normal_iInf_normal (fun hN => hN.1))
  constructor
  · exact le_top
  · unfold twoResidualAmbient
    rw [subgroupOf_map_subtype_eq]
    exact hnormal

private theorem normal_restrict_local
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAB : A ≤ B) (hBH : B ≤ H) (hA : (A.subgroupOf H).Normal) :
    (A.subgroupOf B).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hAB]
  intro a b ha hb
  exact (Subgroup.normal_subgroupOf_iff (hAB.trans hBH)).mp hA
    a b ha (hBH hb)

private theorem le_of_isSylowSubgroupIn_local
    {G : Type u} [Group G] {S P : Subgroup G}
    (hSylow : IsSylowSubgroupIn S P) : S ≤ P := by
  obtain ⟨T, hT⟩ := hSylow
  rw [← hT]
  exact Subgroup.map_subtype_le (T : Subgroup P)

private theorem twoCoreAmbient_le_of_isSylowSubgroupIn_local
    {G : Type u} [Group G] {S P : Subgroup G}
    (hSylow : IsSylowSubgroupIn S P) : twoCoreAmbient P ≤ S := by
  obtain ⟨T, hT⟩ := hSylow
  unfold twoCoreAmbient
  rw [← hT]
  exact Subgroup.map_mono
    (IsPGroup.le_sylow_of_normal
      (pCore_isPGroup (G := P) (p := 2)) T)

private theorem twoCoreAmbient_normal_in_self_local
    {G : Type u} [Group G] (P : Subgroup G) :
    ((twoCoreAmbient P).subgroupOf P).Normal := by
  unfold twoCoreAmbient
  rw [subgroupOf_map_subtype_eq]
  exact pCore_normal

private theorem sup_residual_normal_local
    {G : Type u} [Group G]
    {A R₁ R₂ P₁ P₂ S H : Subgroup G}
    (hAH : A ≤ H) (hAnormal : (A.subgroupOf H).Normal)
    (hP₁H : P₁ ≤ H)
    (hR₁P₁ : R₁ ≤ P₁) (hR₁normal : (R₁.subgroupOf P₁).Normal)
    (hSP₁ : S ≤ P₁) (hR₂A : R₂ ≤ A)
    (hP₂eq : R₂ ⊔ S = P₂) (hH : H = P₁ ⊔ P₂) :
    ((A ⊔ R₁).subgroupOf H).Normal := by
  have hR₁H : R₁ ≤ H := hR₁P₁.trans hP₁H
  have hjoinH : A ⊔ R₁ ≤ H := sup_le hAH hR₁H
  have hP₁normA : P₁ ≤ Subgroup.normalizer (A : Set G) :=
    hP₁H.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAnormal)
  have hP₁normR₁ : P₁ ≤ Subgroup.normalizer (R₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR₁P₁).mp hR₁normal
  have hP₁normJoin : P₁ ≤ Subgroup.normalizer ((A ⊔ R₁ : Subgroup G) : Set G) :=
    (le_inf hP₁normA hP₁normR₁).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup A R₁)
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer hjoinH).mpr
  rw [hH]
  apply sup_le hP₁normJoin
  rw [← hP₂eq]
  apply sup_le
  · exact hR₂A.trans le_sup_left |>.trans (A ⊔ R₁).le_normalizer
  · exact hSP₁.trans hP₁normJoin

public theorem lemma_three_eight
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H N : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hN : N ≤ H ∧ (N.subgroupOf H).Normal ∧
      ¬ twoResidualAmbient P₁ ≤ N ∧
      ¬ twoResidualAmbient P₂ ≤ N ∧
      ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
        (N'.subgroupOf H).Normal →
        (¬ twoResidualAmbient P₁ ≤ N' ∧
          ¬ twoResidualAmbient P₂ ≤ N') → N' = N)
    (hsolv₁ : Group.IsSolvable P₁)
    (hsolv₂ : Group.IsSolvable P₂) :
    ∃ Q H₀ H₁ : Subgroup G,
      LemmaThreeEightConclusion S P₁ P₂ H N Q H₀ H₁ := by
  classical
  let R₁ : Subgroup G := twoResidualAmbient P₁
  let R₂ : Subgroup G := twoResidualAmbient P₂
  let Q : Subgroup G := S ⊓ N
  have hS2 : IsPGroup 2 S := h.nontrivial_two_subgroup.2
  have hSylow₁ : IsSylowSubgroupIn S P₁ := hP₁.1.2.1
  have hSylow₂ : IsSylowSubgroupIn S P₂ := hP₂.1.2.1
  have hSP₁ : S ≤ P₁ := le_of_isSylowSubgroupIn_local hSylow₁
  have hSP₂ : S ≤ P₂ := le_of_isSylowSubgroupIn_local hSylow₂
  have hP₁H : P₁ ≤ H := by rw [hH]; exact le_sup_left
  have hP₂H : P₂ ≤ H := by rw [hH]; exact le_sup_right
  have hSH : S ≤ H := hSP₁.trans hP₁H
  have hR₁P₁ : R₁ ≤ P₁ := by
    exact Subgroup.map_subtype_le (twoResidualSubgroup P₁)
  have hR₂P₂ : R₂ ≤ P₂ := by
    exact Subgroup.map_subtype_le (twoResidualSubgroup P₂)
  have hR₁H : R₁ ≤ H := hR₁P₁.trans hP₁H
  have hR₂H : R₂ ≤ H := hR₂P₂.trans hP₂H
  have hR₁S : R₁ ⊔ S = P₁ := by
    simpa [R₁] using twoResidual_sup_sylowImage_local hSylow₁
  have hR₂S : R₂ ⊔ S = P₂ := by
    simpa [R₂] using twoResidual_sup_sylowImage_local hSylow₂
  have hHnormN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN.1).mp hN.2.1
  have hQleS : Q ≤ S := inf_le_left
  have hQleN : Q ≤ N := inf_le_right
  have hQnormalS : (Q.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hQleS).mpr
    intro q s hq hs
    refine ⟨S.mul_mem (S.mul_mem hs hq.1) (S.inv_mem hs), ?_⟩
    exact (Subgroup.normal_subgroupOf_iff hN.1).mp hN.2.1
      q s hq.2 (hSH hs)
  have hcommR₁QleN : ⁅R₁, Q⁆ ≤ N := by
    exact (Subgroup.commutator_mono le_rfl hQleN).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp
        (hR₁H.trans hHnormN))
  have hcommR₂QleN : ⁅R₂, Q⁆ ≤ N := by
    exact (Subgroup.commutator_mono le_rfl hQleN).trans
      ((Subgroup.le_normalizer_iff_commutator_le_right).mp
        (hR₂H.trans hHnormN))
  have hQcore₁ : Q ≤ twoCoreAmbient P₁ := by
    rcases lemma_three_four S h P₁ hP₁ Q ⟨hQleS, hQnormalS⟩ hsolv₁ with
      hcore | hcomm
    · exact hcore
    · exfalso
      apply hN.2.2.1
      change R₁ ≤ N
      have hcomm' : ⁅R₁, Q⁆ = R₁ := by simpa [R₁] using hcomm
      rw [← hcomm']
      exact hcommR₁QleN
  have hQcore₂ : Q ≤ twoCoreAmbient P₂ := by
    rcases lemma_three_four S h P₂ hP₂ Q ⟨hQleS, hQnormalS⟩ hsolv₂ with
      hcore | hcomm
    · exact hcore
    · exfalso
      apply hN.2.2.2.1
      change R₂ ≤ N
      have hcomm' : ⁅R₂, Q⁆ = R₂ := by simpa [R₂] using hcomm
      rw [← hcomm']
      exact hcommR₂QleN
  have hcore₁S : twoCoreAmbient P₁ ≤ S :=
    twoCoreAmbient_le_of_isSylowSubgroupIn_local hSylow₁
  have hcore₂S : twoCoreAmbient P₂ ≤ S :=
    twoCoreAmbient_le_of_isSylowSubgroupIn_local hSylow₂
  have hQeq₁ : Q = twoCoreAmbient P₁ ⊓ N := by
    apply le_antisymm (le_inf hQcore₁ hQleN)
    intro x hx
    exact ⟨hcore₁S hx.1, hx.2⟩
  have hQeq₂ : Q = twoCoreAmbient P₂ ⊓ N := by
    apply le_antisymm (le_inf hQcore₂ hQleN)
    intro x hx
    exact ⟨hcore₂S hx.1, hx.2⟩
  have hQnormalP₁ : (Q.subgroupOf P₁).Normal := by
    have hQP₁ : Q ≤ P₁ := hQleS.trans hSP₁
    apply (Subgroup.normal_subgroupOf_iff hQP₁).mpr
    intro q p hq hp
    have hq' : q ∈ twoCoreAmbient P₁ ⊓ N := hQeq₁ ▸ hq
    rw [hQeq₁]
    constructor
    · exact (Subgroup.normal_subgroupOf_iff
        (show twoCoreAmbient P₁ ≤ P₁ from hcore₁S.trans hSP₁)).mp
          (twoCoreAmbient_normal_in_self_local P₁) q p hq'.1 hp
    · exact (Subgroup.normal_subgroupOf_iff hN.1).mp hN.2.1
        q p hq'.2 (hP₁H hp)
  have hQnormalP₂ : (Q.subgroupOf P₂).Normal := by
    have hQP₂ : Q ≤ P₂ := hQleS.trans hSP₂
    apply (Subgroup.normal_subgroupOf_iff hQP₂).mpr
    intro q p hq hp
    have hq' : q ∈ twoCoreAmbient P₂ ⊓ N := hQeq₂ ▸ hq
    rw [hQeq₂]
    constructor
    · exact (Subgroup.normal_subgroupOf_iff
        (show twoCoreAmbient P₂ ≤ P₂ from hcore₂S.trans hSP₂)).mp
          (twoCoreAmbient_normal_in_self_local P₂) q p hq'.1 hp
    · exact (Subgroup.normal_subgroupOf_iff hN.1).mp hN.2.1
        q p hq'.2 (hP₂H hp)
  have hQH : Q ≤ H := hQleS.trans hSH
  have hQnormalH : (Q.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr
    rw [hH]
    exact sup_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (hQleS.trans hSP₁)).mp hQnormalP₁)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (hQleS.trans hSP₂)).mp hQnormalP₂)
  have hQlargest : ∀ K : Subgroup G, K ≤ S → K ≤ H →
      (K.subgroupOf H).Normal → K ≤ Q := by
    intro K hKS hKH hKnormal
    have hNKH : N ⊔ K ≤ H := sup_le hN.1 hKH
    have hNKnormal : ((N ⊔ K).subgroupOf H).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer hNKH).mpr
      exact (le_inf hHnormN
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKnormal)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup N K)
    have hNKS : N ⊔ K ≤ N ⊔ S :=
      sup_le le_sup_left (hKS.trans le_sup_right)
    have hNnormalNS : (N.subgroupOf (N ⊔ S)).Normal := by
      exact normal_restrict_local le_sup_left (sup_le hN.1 hSH) hN.2.1
    have hR₁notNK : ¬ R₁ ≤ N ⊔ K := by
      intro hR₁NK
      apply hN.2.2.1
      have hP₁NS : P₁ ≤ N ⊔ S := by
        rw [← hR₁S]
        exact sup_le (hR₁NK.trans hNKS) le_sup_right
      exact twoResidualAmbient_le_left_of_le_sup_local
        N S P₁ hNnormalNS hS2 hP₁NS
    have hR₂notNK : ¬ R₂ ≤ N ⊔ K := by
      intro hR₂NK
      apply hN.2.2.2.1
      have hP₂NS : P₂ ≤ N ⊔ S := by
        rw [← hR₂S]
        exact sup_le (hR₂NK.trans hNKS) le_sup_right
      exact twoResidualAmbient_le_left_of_le_sup_local
        N S P₂ hNnormalNS hS2 hP₂NS
    have hNKeq : N ⊔ K = N :=
      hN.2.2.2.2 (N ⊔ K) le_sup_left hNKH hNKnormal
        ⟨hR₁notNK, hR₂notNK⟩
    exact le_inf hKS (by rw [← hNKeq]; exact le_sup_right)
  have hHneN : H ≠ N := by
    intro hHN
    apply hN.2.2.1
    simpa [hHN] using hR₁H
  let F₀ : Subgroup G → Prop := fun K =>
    N ≤ K ∧ K ≤ H ∧ K ≠ N ∧ (K.subgroupOf H).Normal
  have hF₀H : F₀ H := by
    refine ⟨hN.1, le_rfl, hHneN, ?_⟩
    simp
  obtain ⟨H₀, hF₀, _hH₀leH, hH₀min⟩ :=
    exists_minimal_subgroup_of_mem_le F₀ H hF₀H
  have hNH₀ : N ≤ H₀ := hF₀.1
  have hH₀H : H₀ ≤ H := hF₀.2.1
  have hH₀neN : H₀ ≠ N := hF₀.2.2.1
  have hH₀normalH : (H₀.subgroupOf H).Normal := hF₀.2.2.2
  have hMinimal : IsMinimalNormalOver N H H₀ := by
    refine ⟨hNH₀, hH₀H, hH₀neN, hH₀normalH, ?_⟩
    intro K hNK hKH hKnormal hKH₀
    by_cases hKN : K = N
    · exact Or.inl hKN
    · exact Or.inr (hH₀min K ⟨hNK, hKH, hKN, hKnormal⟩ hKH₀)
  have hResidualH₀ : R₁ ≤ H₀ ∨ R₂ ≤ H₀ := by
    by_cases hR₁H₀ : R₁ ≤ H₀
    · exact Or.inl hR₁H₀
    · right
      by_contra hR₂H₀
      exact hH₀neN
        (hN.2.2.2.2 H₀ hNH₀ hH₀H hH₀normalH ⟨hR₁H₀, hR₂H₀⟩)
  have hR₁normalP₁ : (R₁.subgroupOf P₁).Normal := by
    simpa [R₁] using (twoResidualAmbient_normal_in_self_local P₁).2
  have hR₂normalP₂ : (R₂.subgroupOf P₂).Normal := by
    simpa [R₂] using (twoResidualAmbient_normal_in_self_local P₂).2
  have hHsup_of (K : Subgroup G) (hR₁K : R₁ ≤ K) (hR₂K : R₂ ≤ K)
      (hKH : K ≤ H) : H = S ⊔ K := by
    apply le_antisymm
    · rw [hH]
      apply sup_le
      · rw [← hR₁S]
        exact sup_le (hR₁K.trans le_sup_right) le_sup_left
      · rw [← hR₂S]
        exact sup_le (hR₂K.trans le_sup_right) le_sup_left
    · exact sup_le hSH hKH
  have hproduct_of (K : Subgroup G) (hKH : K ≤ H)
      (hKnormal : (K.subgroupOf H).Normal)
      (hHsup : H = S ⊔ K) : (H : Set G) = (S : Set G) * (K : Set G) := by
    have hSnormK : S ≤ Subgroup.normalizer (K : Set G) :=
      hSH.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hKnormal)
    calc
      (H : Set G) = ((S ⊔ K : Subgroup G) : Set G) :=
        congrArg (fun L : Subgroup G => (L : Set G)) hHsup
      _ = (S : Set G) * (K : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right S K hSnormK
  by_cases hR₁H₀ : R₁ ≤ H₀
  · by_cases hR₂H₀ : R₂ ≤ H₀
    · have hHsupH₀ : H = S ⊔ H₀ :=
        hHsup_of H₀ hR₁H₀ hR₂H₀ hH₀H
      refine ⟨Q, H₀, H₀, ?_⟩
      refine
        { chain := ⟨hQleN, hNH₀, le_rfl, hH₀H⟩
          normal_series := ?_
          part_a := ?_
          part_b := ?_
          part_c := Or.inl rfl
          part_d := hproduct_of H₀ hH₀H hH₀normalH hHsupH₀ }
      · exact
          ⟨normal_restrict_local hQleN hN.1 hQnormalH,
            normal_restrict_local hNH₀ hH₀H hN.2.1,
            by simp,
            hH₀normalH⟩
      · exact ⟨rfl, hQnormalH, hQlargest⟩
      · exact ⟨hMinimal, by simpa [R₁, R₂] using hResidualH₀⟩
    · let H₁ : Subgroup G := H₀ ⊔ R₂
      have hH₁H : H₁ ≤ H := sup_le hH₀H hR₂H
      have hH₀H₁ : H₀ ≤ H₁ := le_sup_left
      have hH₁normalH : (H₁.subgroupOf H).Normal := by
        simpa [H₁] using sup_residual_normal_local
          hH₀H hH₀normalH hP₂H hR₂P₂ hR₂normalP₂ hSP₂ hR₁H₀
          hR₁S (by simpa [sup_comm] using hH)
      have hR₁H₁ : R₁ ≤ H₁ := hR₁H₀.trans hH₀H₁
      have hR₂H₁ : R₂ ≤ H₁ := le_sup_right
      have hHsupH₁ : H = S ⊔ H₁ :=
        hHsup_of H₁ hR₁H₁ hR₂H₁ hH₁H
      refine ⟨Q, H₀, H₁, ?_⟩
      refine
        { chain := ⟨hQleN, hNH₀, hH₀H₁, hH₁H⟩
          normal_series := ?_
          part_a := ?_
          part_b := ?_
          part_c := ?_
          part_d := hproduct_of H₁ hH₁H hH₁normalH hHsupH₁ }
      · exact
          ⟨normal_restrict_local hQleN hN.1 hQnormalH,
            normal_restrict_local hNH₀ hH₀H hN.2.1,
            normal_restrict_local hH₀H₁ hH₁H hH₀normalH,
            hH₁normalH⟩
      · exact ⟨rfl, hQnormalH, hQlargest⟩
      · exact ⟨hMinimal, by simpa [R₁, R₂] using hResidualH₀⟩
      · exact Or.inr (Or.inr ⟨rfl, by simpa [R₂] using hR₂H₀⟩)
  · have hR₂H₀ : R₂ ≤ H₀ := hResidualH₀.resolve_left hR₁H₀
    let H₁ : Subgroup G := H₀ ⊔ R₁
    have hH₁H : H₁ ≤ H := sup_le hH₀H hR₁H
    have hH₀H₁ : H₀ ≤ H₁ := le_sup_left
    have hH₁normalH : (H₁.subgroupOf H).Normal := by
      simpa [H₁] using sup_residual_normal_local
        hH₀H hH₀normalH hP₁H hR₁P₁ hR₁normalP₁ hSP₁ hR₂H₀
        hR₂S hH
    have hR₁H₁ : R₁ ≤ H₁ := le_sup_right
    have hR₂H₁ : R₂ ≤ H₁ := hR₂H₀.trans hH₀H₁
    have hHsupH₁ : H = S ⊔ H₁ :=
      hHsup_of H₁ hR₁H₁ hR₂H₁ hH₁H
    refine ⟨Q, H₀, H₁, ?_⟩
    refine
      { chain := ⟨hQleN, hNH₀, hH₀H₁, hH₁H⟩
        normal_series := ?_
        part_a := ?_
        part_b := ?_
        part_c := ?_
        part_d := hproduct_of H₁ hH₁H hH₁normalH hHsupH₁ }
    · exact
        ⟨normal_restrict_local hQleN hN.1 hQnormalH,
          normal_restrict_local hNH₀ hH₀H hN.2.1,
          normal_restrict_local hH₀H₁ hH₁H hH₀normalH,
          hH₁normalH⟩
    · exact ⟨rfl, hQnormalH, hQlargest⟩
    · exact ⟨hMinimal, by simpa [R₁, R₂] using hResidualH₀⟩
    · exact Or.inr (Or.inl ⟨rfl, by simpa [R₁] using hR₁H₀⟩)

end Stellmacher.SectionThree
