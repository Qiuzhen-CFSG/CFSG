module

public import Stellmacher.SectionThree.LemmaThreeThree

/-!
# Subnormality of residual subgroups modulo the 2-core

Let `P ∈ PSet ⊤ S` be solvable. If `K` lies in `O²(P)`, then
`K O₂(P)` is subnormal in `P`. This is the consequence of Stellmacher (3.3)
used in the second paragraph of the proof of (5.2).

Indeed, modulo `O₂(P)`, part (a) of (3.3) says that the 2-residual is an
odd-prime group. The image of `K O₂(P)` lies in that residual, hence is
subnormal there because finite prime-power groups are nilpotent. The residual
is normal in the quotient, and pulling the resulting subnormal chain back to
`P` gives the claim.

Source: `refs/latex/stellmacher-n-group.tex`, statement (3.3)(a) and its use
in the proof of (5.2), journal page 28.
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

private theorem isSubnormal_of_normalizerCondition_local
    {G : Type u} [Group G] [Finite G]
    (hNC : NormalizerCondition G) (H : Subgroup G) : H.IsSubnormal := by
  classical
  let pred : ℕ → Prop := fun n ↦ ∀ H : Subgroup G, H.index = n → H.IsSubnormal
  have hpred : ∀ n, pred n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih H hn
    by_cases htop : H = ⊤
    · rw [htop]
      exact Subgroup.IsSubnormal.top (G := G)
    · let N := Subgroup.normalizer (H : Set G)
      have hHltN : H < N := hNC H (lt_top_iff_ne_top.mpr htop)
      have hle : H ≤ N := le_of_lt hHltN
      have hN : (H.subgroupOf N).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 le_rfl
      have hind : N.index < H.index := by
        have hrel : H.relIndex N * N.index = H.index :=
          Subgroup.relIndex_mul_index hle
        have hrel_ge : 2 ≤ H.relIndex N := by
          have hne_top : H.subgroupOf N ≠ ⊤ := by
            intro htopN
            have hNleH : N ≤ H :=
              (Subgroup.subgroupOf_eq_top (H := H) (K := N)).1 htopN
            exact (ne_of_lt hHltN) (le_antisymm hle hNleH)
          exact Subgroup.one_lt_index_of_ne_top hne_top
        have hindN : 1 ≤ N.index := Nat.succ_le_of_lt
          (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N)))
        calc
          N.index < 2 * N.index := by omega
          _ ≤ H.relIndex N * N.index := Nat.mul_le_mul_right N.index hrel_ge
          _ = H.index := hrel
      exact Subgroup.IsSubnormal.step H N hle
        (ih N.index (by simpa [hn] using hind) N rfl) hN
  exact hpred H.index H rfl

private theorem isSubnormal_of_isNilpotent_local
    {G : Type u} [Group G] [Finite G]
    (hG : Group.IsNilpotent G) (H : Subgroup G) : H.IsSubnormal := by
  let _ : Group.IsNilpotent G := hG
  exact isSubnormal_of_normalizerCondition_local
    Group.normalizerCondition_of_isNilpotent H

/-- A subgroup of the 2-residual, enlarged by the 2-core, is subnormal in a
solvable member of the local `PSet`. -/
public theorem subgroup_sup_twoCore_subnormal_of_le_twoResidual
    {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P)
    (K : Subgroup G) (hKR : K ≤ twoResidualAmbient P) :
    IsSubnormalIn (K ⊔ twoCoreAmbient P) P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKP : K ≤ P := hKR.trans (Subgroup.map_subtype_le _)
  let O : Subgroup P := pCore 2 P
  let R : Subgroup P := hktPResidual 2 P
  let J : Subgroup P := K.subgroupOf P ⊔ O
  let q : P →* P ⧸ O := QuotientGroup.mk' O
  have hKintR : K.subgroupOf P ≤ R := by
    change K.subgroupOf P ≤ hktPResidual 2 P
    rw [← twoResidualSubgroup_eq_hktPResidual_local P]
    intro k hk
    obtain ⟨r, hr, hrk⟩ :=
      (show (k : G) ∈ twoResidualAmbient P from hKR hk)
    have heq : r = k := P.subtype_injective hrk
    simpa [← heq] using hr
  have hJR : J.map q ≤ twoResidualAmbient (⊤ : Subgroup (P ⧸ O)) := by
    have hOmap : O.map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (f := q) (H := O)).2
      simp [q, QuotientGroup.ker_mk']
    rw [twoResidualAmbient_top_eq_hktPResidual,
      ← map_hktPResidual_quotient 2 O]
    change (K.subgroupOf P ⊔ O).map q ≤ R.map q
    rw [Subgroup.map_sup, hOmap, sup_bot_eq]
    exact Subgroup.map_mono hKintR
  obtain ⟨p, hp, _hpodd, hRp⟩ :=
    three_three_part_a_local S h P hP hsolv
  let _ : Fact p.Prime := ⟨hp⟩
  have hJsubR : ((J.map q).subgroupOf
      (twoResidualAmbient (⊤ : Subgroup (P ⧸ O)))).IsSubnormal := by
    exact isSubnormal_of_isNilpotent_local hRp.isNilpotent _
  have hRnormal : (twoResidualAmbient (⊤ : Subgroup (P ⧸ O))).Normal := by
    rw [twoResidualAmbient_top_eq_hktPResidual]
    exact hktPResidual_normal
  have hJmapSub : (J.map q).IsSubnormal :=
    Subgroup.IsSubnormal.trans hJR hJsubR hRnormal.isSubnormal
  have hJsub : J.IsSubnormal := by
    have hcomap := hJmapSub.comap q
    rw [Subgroup.comap_map_eq_self] at hcomap
    · exact hcomap
    · simp [q, J, O, QuotientGroup.ker_mk']
  refine ⟨sup_le hKP (Subgroup.map_subtype_le _), ?_⟩
  have hsubeq : (K ⊔ twoCoreAmbient P).subgroupOf P = J := by
    unfold twoCoreAmbient
    rw [Subgroup.subgroupOf_sup hKP (Subgroup.map_subtype_le _),
      subgroupOf_map_subtype_eq]
  rwa [hsubeq]

end Stellmacher.SectionThree
