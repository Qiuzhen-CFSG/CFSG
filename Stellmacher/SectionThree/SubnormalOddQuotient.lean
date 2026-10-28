module

public import Stellmacher.SectionThree.SubnormalCoreCenter

/-!
# Odd-prime quotient of a subnormal subgroup of the two-residual

Let `P ∈ ℘(S)` be solvable and let `K` be subnormal in `O²(P)`.  This
module proves that `K / O₂(K)` is a group of odd-prime power order, the
consequence of Stellmacher (3.3)(a) used in the proof of (5.2).

Part (a) of (3.3) makes the image of `O²(P)` modulo `O₂(P)` an odd-prime
group.  Restricting this quotient map to `K` gives a subgroup of that image.
Subnormal monotonicity of the ambient `2`-core puts `O₂(K)` in `O₂(P)`;
conversely, the kernel of the restricted map is a normal `2`-subgroup of `K`
and hence lies in `O₂(K)`.  The kernel is therefore exactly `O₂(K)`, and
the first isomorphism theorem transfers the odd-prime group structure to the
desired quotient.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.3)(a), pp. 21–22, as used in Lemma (5.2), p. 29; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

open BenderSuzuki.External

universe u

private theorem twoResidualSubgroup_eq_hktPResidual_local
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualSubgroup P = hktPResidual 2 P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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

private theorem three_three_part_a_local
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      IsPGroup p
        (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))) := by
  rcases hP.2 with ⟨B, hBmax, hSB, hBuniq⟩
  have hSP : S ≤ P := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le (T : Subgroup P)
  have hSsubB : S.subgroupOf P ≤ B := by
    intro s hs
    have hsS : (s : G) ∈ S := hs
    obtain ⟨b, hb, hbs⟩ := hSB hsS
    have hbeq : b = s := P.subtype_injective hbs
    simpa [← hbeq] using hb
  let P₀ : Subgroup P := B.normalCore
  have hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀ := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact (@Subgroup.normal_le_normalCore P _ B N hN).2 hNB
  have h33 := lemma_three_three S h P hP B P₀
    ⟨hBmax, hSsubB, by
      intro B' hB'max hSB'
      apply hBuniq B' hB'max
      intro s hs
      exact Subgroup.mem_map.mpr
        ⟨⟨s, hSP hs⟩, hSB' (show (⟨s, hSP hs⟩ : P) ∈
          S.subgroupOf P from hs), rfl⟩⟩ hP₀ hsolv
  exact h33.part_a

private theorem twoResidualAmbient_normal_subgroupOf_local
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    ((twoResidualAmbient P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoResidualAmbient,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective,
    twoResidualSubgroup_eq_hktPResidual_local]
  exact hktPResidual_normal

/-- If `K` is subnormal in the two-residual of a solvable member of
`PSet ⊤ S`, then `K / O₂(K)` is an odd-prime group. -/
public theorem subnormal_quotient_twoCore_is_odd_pGroup
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (K : Subgroup G)
    (hKsub : IsSubnormalIn K (twoResidualAmbient P)) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p (K ⧸ pCore 2 K) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := twoResidualAmbient P
  have hRP : R ≤ P := Subgroup.map_subtype_le _
  have hKP : K ≤ P := hKsub.1.trans hRP
  let O : Subgroup P := pCore 2 P
  let q : P →* P ⧸ O := QuotientGroup.mk' O
  let qR : R →* P ⧸ O := q.comp (Subgroup.inclusion hRP)
  let qK : K →* P ⧸ O := q.comp (Subgroup.inclusion hKP)
  obtain ⟨p, hp, hpodd, hres⟩ := three_three_part_a_local S h P hP hsolv
  let _ : Fact p.Prime := ⟨hp⟩
  have hRsub : R.subgroupOf P = twoResidualSubgroup P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hRP]
    rfl
  have hqRrange : qR.range =
      twoResidualAmbient (⊤ : Subgroup (P ⧸ O)) := by
    change (q.comp (Subgroup.inclusion hRP)).range = _
    rw [MonoidHom.range_comp]
    have hrange : (Subgroup.inclusion hRP).range = R.subgroupOf P := by
      ext x
      simp
    rw [hrange, hRsub, twoResidualSubgroup_eq_hktPResidual_local,
      map_hktPResidual_quotient 2 O,
      ← twoResidualAmbient_top_eq_hktPResidual]
  have hqRp : IsPGroup p qR.range := by
    rw [hqRrange]
    simpa [O] using hres
  have hqKle : qK.range ≤ qR.range := by
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, hKsub.1 k.property⟩, rfl⟩
  have hqKp : IsPGroup p qK.range := hqRp.to_le hqKle

  have hRnormalP : (R.subgroupOf P).Normal :=
    twoResidualAmbient_normal_subgroupOf_local P
  have hcoreKR : (pCore 2 K).map K.subtype ≤
      (pCore 2 R).map R.subtype :=
    pCoreAmbient_mono_of_isSubnormalIn K R 2 hKsub.1 hKsub.2
  have hcoreRP : (pCore 2 R).map R.subtype ≤
      (pCore 2 P).map P.subtype :=
    pCoreAmbient_mono_of_isSubnormalIn R P 2 hRP hRnormalP.isSubnormal
  have hcoreKP : (pCore 2 K).map K.subtype ≤
      (pCore 2 P).map P.subtype := hcoreKR.trans hcoreRP
  have hcore_le_ker : pCore 2 K ≤ qK.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    apply (QuotientGroup.eq_one_iff (N := O) _).2
    have hkamb : (k : G) ∈ (pCore 2 K).map K.subtype :=
      Subgroup.mem_map_of_mem K.subtype hk
    obtain ⟨x, hx, hxk⟩ := hcoreKP hkamb
    have hx_eq : x = Subgroup.inclusion hKP k := by
      apply P.subtype_injective
      exact hxk
    change Subgroup.inclusion hKP k ∈ pCore 2 P
    rw [← hx_eq]
    exact hx

  have hker_normal : qK.ker.Normal := inferInstance
  have hker_two : IsPGroup 2 qK.ker := by
    have hcomap : IsPGroup 2
        (O.comap (Subgroup.inclusion hKP)) :=
      (pCore_isPGroup (p := 2) (G := P)).comap_of_injective
        (Subgroup.inclusion hKP) (Subgroup.inclusion_injective hKP)
    have hker_eq : qK.ker = O.comap (Subgroup.inclusion hKP) := by
      ext k
      simp [qK, q, MonoidHom.mem_ker]
    rw [hker_eq]
    exact hcomap
  have hker_le_core : qK.ker ≤ pCore 2 K :=
    le_sSup ⟨hker_normal, hker_two⟩
  have hker : qK.ker = pCore 2 K :=
    le_antisymm hker_le_core hcore_le_ker
  have hpne : p ≠ 2 := by
    rintro rfl
    obtain ⟨n, hn⟩ := hpodd
    omega
  refine ⟨p, hp, hpne, ?_⟩
  have hquotKer : IsPGroup p (K ⧸ qK.ker) :=
    hqKp.of_equiv (QuotientGroup.quotientKerEquivRange qK).symm
  exact hquotKer.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

end Stellmacher.SectionThree
