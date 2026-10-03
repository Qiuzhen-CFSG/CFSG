module

public import Stellmacher.SectionFiveToSeven.FiveTwoCentralizerConjugate

/-!
# Prescribing the Sylow alignment in Stellmacher (5.2)

This module strengthens the assertion-(3) conjugate constructed for Lemma
(5.2).  Given a two-subgroup `Q ≤ N_G(K)` containing the Baumann subgroup,
the chosen conjugate of the global Sylow subgroup can be required to contain
`Q`, while retaining both its Sylow intersection with `N_G(K)` and the
subnormality of `K` in the conjugated omega-centralizer.

Starting from the existing conjugate, intersect its Sylow subgroup with
`N_G(K)` and then work inside `N_G(K) ∩ N_G(B(S))`.  Both that intersection
Sylow and `Q` lie there by Baumann weak closure.  Sylow conjugacy inside this
common normalizer supplies an adjustment normalizing both `K` and `B(S)`.
Conjugating the old conclusions by the adjustment gives all four required
properties.  This is the Sylow adjustment following assertions (3)--(6) in
Stellmacher, Journal of Algebra 190 (1997), proof of (5.2), pp. 28--29.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

private theorem map_internal_ambient_align
    {G : Type u} [Group G]
    (e : G ≃* G) (P : Subgroup G) (T : Subgroup P) :
    let eP : P ≃* P.map e.toMonoidHom :=
      P.equivMapOfInjective e.toMonoidHom e.injective
    (T.map eP.toMonoidHom).map (P.map e.toMonoidHom).subtype =
      (T.map P.subtype).map e.toMonoidHom := by
  dsimp only
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem isSylowTwoIn_map_equiv_align
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* G) (S P : Subgroup G)
    (h : IsSylowTwoIn S P) :
    IsSylowTwoIn (S.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hSP, T, hTmap⟩ := h
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  let T' : Sylow 2 (P.map e.toMonoidHom) :=
    T.mapSurjective (f := eP.toMonoidHom) eP.surjective
  refine ⟨Subgroup.map_mono hSP, T', ?_⟩
  have hT' : (T' : Subgroup (P.map e.toMonoidHom)) =
      (T : Subgroup P).map eP.toMonoidHom :=
    Sylow.coe_mapSurjective eP.surjective T
  rw [hT', map_internal_ambient_align, hTmap]

private theorem subnormalIn_map_equiv_align
    {G : Type u} [Group G]
    (e : G ≃* G) (A P : Subgroup G)
    (h : SubnormalIn A P) :
    SubnormalIn (A.map e.toMonoidHom) (P.map e.toMonoidHom) := by
  obtain ⟨hAP, hsub⟩ := h
  let eP : P ≃* P.map e.toMonoidHom :=
    P.equivMapOfInjective e.toMonoidHom e.injective
  have hmapped : ((A.subgroupOf P).map eP.toMonoidHom).IsSubnormal :=
    hsub.map eP.surjective
  refine ⟨Subgroup.map_mono hAP, ?_⟩
  have heq : (A.subgroupOf P).map eP.toMonoidHom =
      (A.map e.toMonoidHom).subgroupOf (P.map e.toMonoidHom) := by
    apply Subgroup.map_injective
      (P.map e.toMonoidHom).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hAP),
      map_internal_ambient_align,
      Subgroup.map_subgroupOf_eq_of_le hAP]
  rw [← heq]
  exact hmapped

private theorem map_conj_eq_self_of_mem_normalizer_align
    {G : Type u} [Group G] (A : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj x).toMonoidHom = A := by
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  · intro ha
    refine ⟨x⁻¹ * a * x, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * a * x)).mpr (by
        simpa [mul_assoc] using ha)
    · simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_map_conj_align
    {G : Type u} [Group G] (A : Subgroup G) (x h : G) :
    (A.map (MulAut.conj h).toMonoidHom).map
        (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj (x * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_smul_subtype_align
    {G : Type u} [Group G] (P : Subgroup G)
    (T : Sylow 2 P) (x : P) :
    (((x • T : Sylow 2 P) : Subgroup P).map P.subtype) =
      ((T : Subgroup P).map P.subtype).map
        (MulAut.conj (x : G)).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  have he :
      MulDistribMulAction.toMonoidEnd (MulAut P) P (MulAut.conj x) =
        (MulAut.conj x).toMonoidHom := by
    ext t
    rfl
  rw [he, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Assertion (3) of (5.2), with a prescribed two-subgroup included in the
chosen conjugate Sylow subgroup. -/
public theorem five_two_exists_centralizer_conjugate_containing
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (P K Q : Subgroup G)
    (hP : P ∈ PStarFamily
      (Subgroup.centralizer (omegaOneCenter (S : Subgroup G) : Set G))
      (S : Subgroup G))
    (hK : K ≤ P)
    (hlocal : ∀ U : Subgroup G,
      IsTwoLocal U → baumannIn (S : Subgroup G) ≤ U →
        Group.IsSolvable U ∧ Stellmacher.IsCharacteristicTwoType U)
    (hcomm : K = ⁅K, baumannIn (S : Subgroup G)⁆)
    (hKne : K ≠ ⊥)
    (hlarger : K ≠ twoResidualIn P →
      ∀ U : Subgroup G, IsTwoLocal U →
        baumannIn (S : Subgroup G) ⊔ twoResidualIn P ≤ U →
        SubnormalIn (twoResidualIn P) U)
    (hQp : IsPGroup 2 Q)
    (hQNK : Q ≤ Subgroup.normalizer (K : Set G))
    (hBQ : baumannIn (S : Subgroup G) ≤ Q) :
    ∃ h : G,
      h ∈ Subgroup.normalizer (baumannIn (S : Subgroup G) : Set G) ∧
      Q ≤ (S : Subgroup G).map (MulAut.conj h).toMonoidHom ∧
      IsSylowTwoIn
        (((S : Subgroup G).map (MulAut.conj h).toMonoidHom) ⊓
          Subgroup.normalizer (K : Set G))
        (Subgroup.normalizer (K : Set G)) ∧
      SubnormalIn K
        ((Subgroup.centralizer
          (omegaOneCenter (S : Subgroup G) : Set G)).map
            (MulAut.conj h).toMonoidHom) := by
  classical
  let S0 : Subgroup G := (S : Subgroup G)
  let B : Subgroup G := baumannIn S0
  let C : Subgroup G := Subgroup.centralizer (omegaOneCenter S0 : Set G)
  let NK : Subgroup G := Subgroup.normalizer (K : Set G)
  obtain ⟨h0, hh0B, hSylow0, hKsub0⟩ :=
    five_two_exists_centralizer_conjugate S P K hP hK hlocal hcomm hKne hlarger
  let e0 : G ≃* G := MulAut.conj h0
  let Sh0 : Subgroup G := S0.map e0.toMonoidHom
  let T0 : Subgroup G := Sh0 ⊓ NK
  let NB : Subgroup G := NK ⊓ Subgroup.normalizer (B : Set G)
  have hBmap0 : B.map e0.toMonoidHom = B := by
    exact map_conj_eq_self_of_mem_normalizer_align B (by simpa [B] using hh0B)
  have hBSh0 : B ≤ Sh0 := by
    rw [← hBmap0]
    exact Subgroup.map_mono inf_le_left
  have hBNK : B ≤ NK := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact hcomm.symm.le
  have hBT0 : B ≤ T0 := le_inf hBSh0 hBNK
  have hSh0p : IsPGroup 2 Sh0 := S.isPGroup'.map e0.toMonoidHom
  have hT0p : IsPGroup 2 T0 := hSh0p.to_le inf_le_left
  have hT0normB : T0 ≤ Subgroup.normalizer (B : Set G) := by
    change T0 ≤ Subgroup.normalizer
      (baumannIn (S : Subgroup G) : Set G)
    have hBT0' : baumannIn (S : Subgroup G) ≤ T0 := by
      simpa [B, S0] using hBT0
    exact Stellmacher.twoSubgroup_le_normalizer_baumann S T0 hT0p (by
      simpa only [baumannIn, omegaOneCenter,
        Stellmacher.omegaOneCenterAmbient] using hBT0')
  have hT0NB : T0 ≤ NB := le_inf inf_le_right hT0normB
  have hQnormB : Q ≤ Subgroup.normalizer (B : Set G) := by
    change Q ≤ Subgroup.normalizer
      (baumannIn (S : Subgroup G) : Set G)
    exact Stellmacher.twoSubgroup_le_normalizer_baumann S Q hQp hBQ
  have hQNB : Q ≤ NB := le_inf (by simpa [NK] using hQNK) hQnormB
  obtain ⟨hT0NK, TN, hTNmap⟩ : IsSylowTwoIn T0 NK := by
    simpa [T0, Sh0, S0, e0, NK] using hSylow0
  let Tsub : Subgroup NB := T0.subgroupOf NB
  have hTsubp : IsPGroup 2 Tsub :=
    hT0p.of_equiv (Subgroup.subgroupOfEquivOfLe hT0NB).symm
  obtain ⟨TNB, hTsubTNB⟩ := hTsubp.exists_le_sylow
  have hTNBmap : (TNB : Subgroup NB).map NB.subtype = T0 := by
    let TG : Subgroup G := (TNB : Subgroup NB).map NB.subtype
    have hTGp : IsPGroup 2 TG := TNB.isPGroup'.map NB.subtype
    have hTGNK : TG ≤ NK :=
      (Subgroup.map_subtype_le (TNB : Subgroup NB)).trans inf_le_left
    have hT0TG : T0 ≤ TG := by
      calc
        T0 = Tsub.map NB.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hT0NB).symm
        _ ≤ (TNB : Subgroup NB).map NB.subtype :=
          Subgroup.map_mono hTsubTNB
        _ = TG := rfl
    have hTNle : (TN : Subgroup NK) ≤ TG.subgroupOf NK := by
      intro t ht
      have ht0 : (t : G) ∈ T0 := hTNmap ▸ Subgroup.mem_map_of_mem NK.subtype ht
      exact hT0TG ht0
    have hTGsubp : IsPGroup 2 (TG.subgroupOf NK) :=
      hTGp.of_equiv (Subgroup.subgroupOfEquivOfLe hTGNK).symm
    have hEq : TG.subgroupOf NK = (TN : Subgroup NK) :=
      TN.is_maximal' hTGsubp hTNle
    change TG = T0
    calc
      TG = (TG.subgroupOf NK).map NK.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTGNK).symm
      _ = (TN : Subgroup NK).map NK.subtype := by rw [hEq]
      _ = T0 := hTNmap
  let Qsub : Subgroup NB := Q.subgroupOf NB
  have hQsubp : IsPGroup 2 Qsub :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQNB).symm
  obtain ⟨U, hQsubU⟩ := hQsubp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq NB TNB U
  let x : G := (n : NB)
  let e : G ≃* G := MulAut.conj x
  let h : G := x * h0
  have hxNK : x ∈ NK := n.property.1
  have hxNB : x ∈ Subgroup.normalizer (B : Set G) := n.property.2
  have hUmap : (U : Subgroup NB).map NB.subtype =
      T0.map e.toMonoidHom := by
    calc
      (U : Subgroup NB).map NB.subtype =
          ((n • TNB : Sylow 2 NB) : Subgroup NB).map NB.subtype := by rw [hn]
      _ = ((TNB : Subgroup NB).map NB.subtype).map
          (MulAut.conj (n : G)).toMonoidHom :=
            map_smul_subtype_align NB TNB n
      _ = T0.map e.toMonoidHom := by rw [hTNBmap]
  have hQTmap : Q ≤ T0.map e.toMonoidHom := by
    rw [← hUmap]
    calc
      Q = Qsub.map NB.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQNB).symm
      _ ≤ (U : Subgroup NB).map NB.subtype := Subgroup.map_mono hQsubU
  have hSh : Sh0.map e.toMonoidHom =
      S0.map (MulAut.conj h).toMonoidHom := by
    simpa [Sh0, e0, e, h] using map_conj_map_conj_align S0 x h0
  have hQSh : Q ≤ S0.map (MulAut.conj h).toMonoidHom := by
    rw [← hSh]
    exact hQTmap.trans (Subgroup.map_mono inf_le_left)
  have hNKmap : NK.map e.toMonoidHom = NK := by
    exact map_conj_eq_self_of_mem_normalizer_align NK
      (NK.le_normalizer hxNK)
  have hSylowMap := isSylowTwoIn_map_equiv_align e T0 NK
    (by exact ⟨hT0NK, TN, hTNmap⟩)
  have hTmap : T0.map e.toMonoidHom =
      S0.map (MulAut.conj h).toMonoidHom ⊓ NK := by
    calc
      T0.map e.toMonoidHom =
          Sh0.map e.toMonoidHom ⊓ NK.map e.toMonoidHom := by
            exact Subgroup.map_inf Sh0 NK e.toMonoidHom e.injective
      _ = S0.map (MulAut.conj h).toMonoidHom ⊓ NK := by rw [hSh, hNKmap]
  have hSylow : IsSylowTwoIn
      (S0.map (MulAut.conj h).toMonoidHom ⊓ NK) NK := by
    rw [hTmap, hNKmap] at hSylowMap
    exact hSylowMap
  have hKmap : K.map e.toMonoidHom = K := by
    exact map_conj_eq_self_of_mem_normalizer_align K (by simpa [NK] using hxNK)
  have hKsubMap := subnormalIn_map_equiv_align e K
    (C.map e0.toMonoidHom) (by simpa [C, e0] using hKsub0)
  have hCmap : (C.map e0.toMonoidHom).map e.toMonoidHom =
      C.map (MulAut.conj h).toMonoidHom := by
    simpa [e0, e, h] using map_conj_map_conj_align C x h0
  have hKsub : SubnormalIn K (C.map (MulAut.conj h).toMonoidHom) := by
    rw [hKmap, hCmap] at hKsubMap
    exact hKsubMap
  refine ⟨h, ?_, hQSh, ?_, ?_⟩
  · exact (Subgroup.normalizer (B : Set G)).mul_mem hxNB (by simpa [B] using hh0B)
  · simpa [S0, NK] using hSylow
  · simpa [C, S0] using hKsub

end Stellmacher.SectionsFiveToSeven
