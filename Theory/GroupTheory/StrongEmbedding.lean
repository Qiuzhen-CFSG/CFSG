module

public import Theory.Comparator.Defs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Sylow

/-!
# A normalizer criterion for strong embedding

This module proves the standard finite-group criterion used in the second
paragraph of Stellmacher (5.1): if a proper subgroup containing a nontrivial
Sylow `2`-subgroup is not strongly embedded, then some nontrivial subgroup of
that Sylow subgroup has a normalizer not contained in the proper subgroup.

The proof first transports the normalizer hypothesis from subgroups of the
chosen Sylow subgroup to all nontrivial `2`-subgroups of `M`, using Sylow
conjugacy within `M`, and then to conjugates of `M`.  If `M ∩ Mᵍ` contained an
involution, choose a Sylow subgroup `Q` of that intersection containing it and
an ambient Sylow subgroup `P` containing `Q`.  The normalizer condition in the
finite `2`-group `P` forces `Q = P`; Sylow conjugacy within `M` then implies
`g ∈ M`, a contradiction.

Source: Stellmacher, *On the theorem of Glauberman and Thompson*, proof of
Theorem 5.1, second paragraph; formalization source
`refs/latex/stellmacher-n-group.tex`, lines 1088--1092.
-/

@[expose] public section

open scoped Pointwise

private theorem normalizer_le_of_normalizers_le_on_sylow
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (M : Subgroup H) (hSM : (S : Subgroup H) ≤ M)
    (hall : ∀ Q : Subgroup H, Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ (S : Subgroup H) →
      Subgroup.normalizer (Q : Set H) ≤ M) :
    ∀ Q : Subgroup H, Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ M →
      Subgroup.normalizer (Q : Set H) ≤ M := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro Q hQne hQp hQM
  let QM : Subgroup M := Q.subgroupOf M
  have hQMp : IsPGroup 2 QM := by
    exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  obtain ⟨P, hQMP⟩ := hQMp.exists_le_sylow
  let SM : Sylow 2 M := S.subtype hSM
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P SM
  let f : H →* H := (MulAut.conj (m : H)).toMonoidHom
  let R : Subgroup H := Q.map f
  have hm_subgroup : MulAut.conj m • (P : Subgroup M) = (SM : Subgroup M) := by
    simpa only [Sylow.coe_subgroup_smul] using
      congrArg (fun T : Sylow 2 M => (T : Subgroup M)) hm
  have hQconj_le : MulAut.conj m • QM ≤ (SM : Subgroup M) := by
    apply le_trans _ hm_subgroup.le
    gcongr
  have hRle : R ≤ (S : Subgroup H) := by
    intro r hr
    have hRM : R ≤ M := by
      change MulAut.conj (m : H) • Q ≤ M
      exact Subgroup.conj_smul_le_of_le hQM m
    have hrsub : (⟨r, hRM hr⟩ : M) ∈ R.subgroupOf M := hr
    have hsubeq : R.subgroupOf M = MulAut.conj m • QM := by
      change (MulAut.conj (m : H) • Q).subgroupOf M =
        MulAut.conj m • Q.subgroupOf M
      exact (Subgroup.conj_smul_subgroupOf hQM m).symm
    rw [hsubeq] at hrsub
    exact hQconj_le hrsub
  have hRp : IsPGroup 2 R := hQp.map f
  have hRne : R ≠ ⊥ := by
    intro hRbot
    apply hQne
    exact (Subgroup.map_eq_bot_iff_of_injective Q
      (MulAut.conj (m : H)).injective).mp hRbot
  intro x hx
  have hfxnorm : f x ∈ Subgroup.normalizer (R : Set H) := by
    apply Subgroup.le_normalizer_map (H := Q) f
    exact ⟨x, hx, rfl⟩
  have hfxM : f x ∈ M := hall R hRne hRp hRle hfxnorm
  have hxM : (m : H)⁻¹ * f x * (m : H) ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem m.property) hfxM) m.property
  simpa [f, mul_assoc] using hxM

private theorem normalizer_le_conjugate_of_normalizer_le
    {H : Type*} [Group H]
    (M : Subgroup H)
    (hnorm : ∀ Q : Subgroup H, Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ M →
      Subgroup.normalizer (Q : Set H) ≤ M)
    (g : H) :
    ∀ Q : Subgroup H, Q ≠ ⊥ → IsPGroup 2 Q →
      Q ≤ M.map (MulAut.conj g).toMonoidHom →
      Subgroup.normalizer (Q : Set H) ≤
        M.map (MulAut.conj g).toMonoidHom := by
  intro Q hQne hQp hQconj
  let f : H →* H := (MulAut.conj g⁻¹).toMonoidHom
  let Qpre : Subgroup H := Q.map f
  have hQpreM : Qpre ≤ M := by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    rcases hQconj hq with ⟨m, hm, hmq⟩
    refine hmq ▸ ?_
    simpa [f, mul_assoc] using hm
  have hQprep : IsPGroup 2 Qpre := hQp.map f
  have hQprene : Qpre ≠ ⊥ := by
    intro hbot
    apply hQne
    exact (Subgroup.map_eq_bot_iff_of_injective Q
      (MulAut.conj g⁻¹).injective).mp hbot
  intro x hx
  have hfxnorm : f x ∈ Subgroup.normalizer (Qpre : Set H) := by
    apply Subgroup.le_normalizer_map (H := Q) f
    exact ⟨x, hx, rfl⟩
  have hfxM : f x ∈ M := hnorm Qpre hQprene hQprep hQpreM hfxnorm
  refine ⟨f x, hfxM, ?_⟩
  simp [f, mul_assoc]

/-- If a proper subgroup containing a nontrivial Sylow `2`-subgroup is not strongly
embedded, one of the nontrivial `2`-subgroups of that Sylow subgroup has a normalizer
not contained in the proper subgroup. -/
public theorem exists_twoSubgroup_le_sylow_normalizer_not_le_of_not_stronglyEmbedded
    {H : Type*} [Group H] [Finite H]
    (S : Sylow 2 H) (hSne : (S : Subgroup H) ≠ ⊥)
    (M : Subgroup H) (hMproper : M ≠ ⊤) (hSM : (S : Subgroup H) ≤ M)
    (hMnot : ¬ IsStronglyEmbedded M) :
    ∃ Q : Subgroup H,
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Q ≤ (S : Subgroup H) ∧
        ¬ Subgroup.normalizer (Q : Set H) ≤ M := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_contra hnone
  push Not at hnone
  have hnormM := normalizer_le_of_normalizers_le_on_sylow S M hSM hnone
  apply hMnot
  refine ⟨hMproper, ?_, ?_⟩
  · let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot (S : Subgroup H)).2 hSne
    obtain ⟨n, hnpos, hScard⟩ := S.isPGroup'.nontrivial_iff_card.mp inferInstance
    have htwo : 2 ∣ Nat.card S := by
      rw [hScard]
      exact dvd_pow_self 2 hnpos.ne'
    obtain ⟨s, hsord⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 htwo
    have hsordH : orderOf (s : H) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hsord
    refine ⟨(s : H), hSM s.property, ?_, ?_⟩
    · intro hsone
      have : orderOf (s : H) = 1 := orderOf_eq_one_iff.mpr hsone
      omega
    · have hs := pow_orderOf_eq_one (s : H)
      rw [hsordH] at hs
      exact hs
  · intro g hgM x hxI hxinv
    let Mg : Subgroup H := M.map (MulAut.conj g).toMonoidHom
    let I : Subgroup H := M ⊓ Mg
    have hxI' : x ∈ I := hxI
    have hxord : orderOf x = 2 := orderOf_eq_prime hxinv.2 hxinv.1
    let X : Subgroup H := Subgroup.zpowers x
    have hXcard : Nat.card X = 2 ^ 1 := by
      simp [X, Nat.card_zpowers, hxord]
    have hXp : IsPGroup 2 X := IsPGroup.of_card hXcard
    have hXne : X ≠ ⊥ := by
      simpa [X, Subgroup.zpowers_eq_bot] using hxinv.1
    have hXleI : X ≤ I := by
      change Subgroup.zpowers x ≤ I
      exact Subgroup.zpowers_le.mpr hxI'
    let XI : Subgroup I := X.subgroupOf I
    have hXIp : IsPGroup 2 XI := by
      exact hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXleI).symm
    obtain ⟨QI, hXIQ⟩ := hXIp.exists_le_sylow
    let Q : Subgroup H := (QI : Subgroup I).map I.subtype
    have hQleI : Q ≤ I := Subgroup.map_subtype_le (QI : Subgroup I)
    have hQp : IsPGroup 2 Q := QI.isPGroup'.map I.subtype
    have hxQ : x ∈ Q := by
      refine ⟨⟨x, hxI'⟩, hXIQ ?_, rfl⟩
      exact Subgroup.mem_zpowers x
    have hQne : Q ≠ ⊥ := by
      intro hQbot
      have : x = 1 := by simpa [hQbot] using hxQ
      exact hxinv.1 this
    have hQM : Q ≤ M := hQleI.trans inf_le_left
    have hQMg : Q ≤ Mg := hQleI.trans inf_le_right
    have hnormMg := normalizer_le_conjugate_of_normalizer_le M hnormM g
    obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
    have hQeqP : Q = (P : Subgroup H) := by
      apply le_antisymm hQP
      by_contra hPQ
      have hQproper : Q.subgroupOf (P : Subgroup H) < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop
        exact hPQ (Subgroup.subgroupOf_eq_top.mp htop)
      let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
      have hnormlt :
          Q.subgroupOf (P : Subgroup H) <
            Subgroup.normalizer (Q.subgroupOf (P : Subgroup H)) :=
        Group.normalizerCondition_of_isNilpotent _ hQproper
      obtain ⟨n, hnnorm, hnQ⟩ := SetLike.exists_of_lt hnormlt
      have hnNormQ : (n : H) ∈ Subgroup.normalizer Q := by
        rw [← Subgroup.subgroupOf_normalizer_eq hQP] at hnnorm
        exact hnnorm
      have hnM : (n : H) ∈ M := hnormM Q hQne hQp hQM hnNormQ
      have hnMg : (n : H) ∈ Mg := hnormMg Q hQne hQp hQMg hnNormQ
      have hnI : (n : H) ∈ I := ⟨hnM, hnMg⟩
      let K : Subgroup H := (P : Subgroup H) ⊓ Subgroup.normalizer Q
      have hKleI : K ≤ I := by
        intro y hy
        exact ⟨hnormM Q hQne hQp hQM hy.2,
          hnormMg Q hQne hQp hQMg hy.2⟩
      have hKp : IsPGroup 2 K := P.isPGroup'.to_le inf_le_left
      let KI : Subgroup I := K.subgroupOf I
      have hKIp : IsPGroup 2 KI := by
        exact hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKleI).symm
      have hQIKI : (QI : Subgroup I) ≤ KI := by
        intro q hq
        have hqQ : (q : H) ∈ Q := ⟨q, hq, rfl⟩
        exact ⟨hQP hqQ, Subgroup.le_normalizer hqQ⟩
      have hKIeq : KI = (QI : Subgroup I) := QI.is_maximal' hKIp hQIKI
      have hnKI : (⟨(n : H), hnI⟩ : I) ∈ KI :=
        ⟨n.property, hnNormQ⟩
      have hnQI : (⟨(n : H), hnI⟩ : I) ∈ (QI : Subgroup I) := by
        rw [← hKIeq]
        exact hnKI
      apply hnQ
      exact ⟨⟨(n : H), hnI⟩, hnQI, rfl⟩
    have hPM : (P : Subgroup H) ≤ M := hQeqP ▸ hQM
    have hPgM : (P : Subgroup H) ≤ Mg := hQeqP ▸ hQMg
    have hgmem : g ∈ M := by
      let Pg : Sylow 2 H := g⁻¹ • P
      have hPg_le_M : (Pg : Subgroup H) ≤ M := by
        change MulAut.conj g⁻¹ • (P : Subgroup H) ≤ M
        calc
          MulAut.conj g⁻¹ • (P : Subgroup H) ≤ MulAut.conj g⁻¹ • Mg := by
            gcongr
          _ = M := by
            change MulAut.conj g⁻¹ • (MulAut.conj g • M) = M
            rw [map_inv]
            exact inv_smul_smul (MulAut.conj g) M
      let PgM : Sylow 2 M := Pg.subtype hPg_le_M
      let PM : Sylow 2 M := P.subtype hPM
      obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M PgM PM
      dsimp [PgM, PM, Pg] at hm
      simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hm
      have hmnorm : (m : H) * g⁻¹ ∈ Subgroup.normalizer (P : Subgroup H) :=
        Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hm)
      have hPne : (P : Subgroup H) ≠ ⊥ := hQeqP ▸ hQne
      have hmnormM : (m : H) * g⁻¹ ∈ M :=
        hnormM (P : Subgroup H) hPne P.isPGroup' hPM hmnorm
      have hginM : ((m : H) * g⁻¹)⁻¹ * (m : H) ∈ M :=
        M.mul_mem (M.inv_mem hmnormM) m.property
      simpa [mul_assoc] using hginM
    exact hgM hgmem
