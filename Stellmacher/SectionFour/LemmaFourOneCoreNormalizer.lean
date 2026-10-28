module

public import Stellmacher.SectionsOneToFourDefs


/-!
# Core and normalizer conclusions in Stellmacher (4.1)

This module proves parts (b) and (c) of Stellmacher (4.1), conditional on the
nonemptiness of `PSet` supplied by part (a).  It follows the proof on journal
page 25 (`refs/latex/stellmacher-n-group.tex`): if `D` is the intersection of
the 2-cores of the members of `PSet`, then
`Z = Ω₁(Z(S)) ≤ D ≤ O₂(N_G(D))`, and `N_G(S)` normalizes `D`.

For the first inclusion, a member `P` of `PSet` lies in the normalizer of its
nontrivial 2-core.  That normalizer has characteristic 2 by the Section 4
hypotheses, so the central involutions of the fixed Sylow subgroup lie in its
2-core and hence in `O₂(P)`.  Nonemptiness makes `D` a 2-subgroup; its normality
inside its normalizer then gives the second inclusion.  Finally, conjugation by
`N_G(S)` permutes `PSet` and transports each 2-core via `pCore_map_iso`, so it
fixes their infimum.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionFour

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem map_internal_ambient
    (P : Subgroup G) (e : G ≃* G) (M : Subgroup P) :
    (M.map (e.subgroupMap P : P →* P.map (e : G →* G))).map
        (P.map (e : G →* G)).subtype =
      (M.map P.subtype).map (e : G →* G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private theorem map_internal_ambient_symm
    (P : Subgroup G) (e : G ≃* G)
    (M : Subgroup (P.map (e : G →* G))) :
    (M.map ((e.subgroupMap P).symm : _ →* P)).map P.subtype =
      (M.map (P.map (e : G →* G)).subtype).map (e.symm : G →* G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private theorem twoCoreAmbient_map
    (P : Subgroup G) (e : G ≃* G) :
    twoCoreAmbient (P.map (e : G →* G)) =
      (twoCoreAmbient P).map (e : G →* G) := by
  let eP : P ≃* P.map (e : G →* G) := e.subgroupMap P
  have hcore : (pCore 2 P).map (eP : P →* P.map (e : G →* G)) =
      pCore 2 (P.map (e : G →* G)) := pCore_map_iso 2 eP
  unfold twoCoreAmbient
  rw [← hcore, map_internal_ambient]

omit [Finite G] in
private theorem uniqueMaximal_map
    (S P : Subgroup G) (e : G ≃* G)
    (hS : S.map (e : G →* G) = S)
    (hP : IsUniqueMaximalContaining S P) :
    IsUniqueMaximalContaining S (P.map (e : G →* G)) := by
  rcases hP with ⟨M, hMcoatom, hSM, hMunique⟩
  let eP : P ≃* P.map (e : G →* G) := e.subgroupMap P
  refine ⟨M.map (eP : P →* P.map (e : G →* G)), ?_, ?_, ?_⟩
  · exact (OrderIso.isCoatom_iff eP.mapSubgroup M).2 hMcoatom
  · rw [map_internal_ambient, ← hS]
    exact Subgroup.map_mono hSM
  · intro M' hM'coatom hSM'
    let M0 : Subgroup P := M'.map (eP.symm : _ →* P)
    have hM0coatom : IsCoatom M0 :=
      (OrderIso.isCoatom_iff eP.symm.mapSubgroup M').2 hM'coatom
    have hSinv : S.map (e.symm : G →* G) = S := by
      calc
        S.map (e.symm : G →* G) =
            (S.map (e : G →* G)).map (e.symm : G →* G) := by rw [hS]
        _ = S := by rw [Subgroup.map_map]; simp
    have hSM0 : S ≤ M0.map P.subtype := by
      rw [map_internal_ambient_symm, ← hSinv]
      exact Subgroup.map_mono hSM'
    have hM0 : M0 = M := hMunique M0 hM0coatom hSM0
    have hback : M0.map (eP : P →* P.map (e : G →* G)) = M' := by
      dsimp [M0]
      rw [Subgroup.map_map]
      simp
    rw [← hback, hM0]

private theorem isSylowSubgroupIn_map
    (S P : Subgroup G) (e : G ≃* G)
    (hS : S.map (e : G →* G) = S)
    (hP : IsSylowSubgroupIn S P) :
    IsSylowSubgroupIn S (P.map (e : G →* G)) := by
  obtain ⟨T, hT⟩ := hP
  let eP : P ≃* P.map (e : G →* G) := e.subgroupMap P
  let Te : Sylow 2 (P.map (e : G →* G)) :=
    T.mapSurjective (f := eP.toMonoidHom) eP.surjective
  refine ⟨Te, ?_⟩
  change ((T : Subgroup P).map eP.toMonoidHom).map
      (P.map (e : G →* G)).subtype = S
  dsimp [eP]
  rw [map_internal_ambient P e (T : Subgroup P), hT, hS]

private theorem pSet_member_map
    (S P : Subgroup G) (e : G ≃* G)
    (hS : S.map (e : G →* G) = S)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) S) :
    P.map (e : G →* G) ∈ SectionThree.PSet (⊤ : Subgroup G) S := by
  refine ⟨⟨le_top, isSylowSubgroupIn_map S P e hS hP.1.2.1, ?_, ?_⟩,
    uniqueMaximal_map S P e hS hP.2⟩
  · rw [twoCoreAmbient_map]
    exact fun hbot ↦ hP.1.2.2.1
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := twoCoreAmbient P) (f := e.toMonoidHom) e.injective).mp hbot)
  · rw [twoCoreAmbient_map, ← hS]
    exact (e.mapSubgroup.injective.ne_iff).2 hP.1.2.2.2

private theorem pSetCore_image_subset
    (S : Subgroup G) (e : G ≃* G)
    (hS : S.map (e : G →* G) = S) :
    e.mapSubgroup ''
        {D : Subgroup G | ∃ P : Subgroup G,
          P ∈ SectionThree.PSet (⊤ : Subgroup G) S ∧ D = twoCoreAmbient P} ⊆
      {D : Subgroup G | ∃ P : Subgroup G,
        P ∈ SectionThree.PSet (⊤ : Subgroup G) S ∧ D = twoCoreAmbient P} := by
  rintro D ⟨D0, ⟨P, hP, rfl⟩, rfl⟩
  exact ⟨P.map (e : G →* G), pSet_member_map S P e hS hP,
    (twoCoreAmbient_map P e).symm⟩

private theorem pSetCore_image_eq
    (S : Subgroup G) (e : G ≃* G)
    (hS : S.map (e : G →* G) = S) :
    e.mapSubgroup ''
        {D : Subgroup G | ∃ P : Subgroup G,
          P ∈ SectionThree.PSet (⊤ : Subgroup G) S ∧ D = twoCoreAmbient P} =
      {D : Subgroup G | ∃ P : Subgroup G,
        P ∈ SectionThree.PSet (⊤ : Subgroup G) S ∧ D = twoCoreAmbient P} := by
  apply Set.Subset.antisymm (pSetCore_image_subset S e hS)
  intro D hD
  have hSinv : S.map (e.symm : G →* G) = S := by
    calc
      S.map (e.symm : G →* G) =
          (S.map (e : G →* G)).map (e.symm : G →* G) := by rw [hS]
      _ = S := by rw [Subgroup.map_map]; simp
  obtain ⟨P, hP, rfl⟩ := hD
  refine ⟨twoCoreAmbient (P.map (e.symm : G →* G)),
    ⟨P.map (e.symm : G →* G), pSet_member_map S P e.symm hSinv hP, rfl⟩,
    ?_⟩
  change (twoCoreAmbient (P.map (e.symm : G →* G))).map
    (e : G →* G) = twoCoreAmbient P
  rw [← twoCoreAmbient_map, Subgroup.map_map]
  simp

private theorem dSubgroup_map
    (S : Sylow 2 G) (e : G ≃* G)
    (hS : (S : Subgroup G).map (e : G →* G) = S) :
    (dSubgroup S).map (e : G →* G) = dSubgroup S := by
  let C : Set (Subgroup G) :=
    {D : Subgroup G | ∃ P : Subgroup G,
      P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) ∧
        D = twoCoreAmbient P}
  change (sInf C).map (e : G →* G) = sInf C
  calc
    (sInf C).map (e : G →* G) = e.mapSubgroup (sInf C) := rfl
    _ = sInf (e.mapSubgroup '' C) := by
      simpa only [sInf_image] using e.mapSubgroup.map_sInf C
    _ = sInf C := by rw [pSetCore_image_eq (S : Subgroup G) e hS]

private theorem normalizer_s_le_normalizer_d (S : Sylow 2 G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (dSubgroup S : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact dSubgroup_map S (MulAut.conj g)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg)

omit [Finite G] in
private theorem zSubgroup_le_centerAmbient (S : Sylow 2 G) :
    zSubgroup S ≤ (Subgroup.center S).map (S : Subgroup G).subtype := by
  unfold zSubgroup omegaOneCenterAmbient
  exact Subgroup.map_mono
    (Subgroup.map_subtype_le
      ((omega₁ (G := Subgroup.center S) (p := 2)) : Subgroup (Subgroup.center S)))

private theorem zSubgroup_ne_bot
    (S : Sylow 2 G) (heven : Even (Nat.card G)) :
    zSubgroup S ≠ ⊥ := by
  have hSne : (S : Subgroup G) ≠ ⊥ :=
    S.ne_bot_of_dvd_card heven.two_dvd
  let : Nontrivial S :=
    (Subgroup.nontrivial_iff_ne_bot (S : Subgroup G)).2 hSne
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center S) :=
    S.isPGroup'.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hcenterP.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  have hinner := omega₁_map_subtype_ne_bot
    (G := S) (Subgroup.center S) 2 hdvd
  intro hz
  apply hinner
  apply (Subgroup.map_eq_bot_iff_of_injective
    (H := (omega₁ (G := Subgroup.center S) (p := 2)).map
      (Subgroup.center S).subtype)
    (f := (S : Subgroup G).subtype) (S : Subgroup G).subtype_injective).mp
  simpa [zSubgroup, omegaOneCenterAmbient] using hz

omit [Finite G] in
private theorem twoCoreAmbient_normal_subgroupOf (P : Subgroup G) :
    ((twoCoreAmbient P).subgroupOf P).Normal := by
  rw [← Subgroup.comap_subtype, twoCoreAmbient,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  exact (inferInstance : (pCore 2 P).Normal)

omit [Finite G] in
private theorem twoCoreAmbient_isPGroup (P : Subgroup G) :
    IsPGroup 2 (twoCoreAmbient P) :=
  (pCore_isPGroup (p := 2) (G := P)).map P.subtype

omit [Finite G] in
private theorem normal_pSubgroup_le_twoCoreAmbient
    (Q P : Subgroup G) (hQP : Q ≤ P)
    (hQp : IsPGroup 2 Q) (hQnormal : (Q.subgroupOf P).Normal) :
    Q ≤ twoCoreAmbient P := by
  have hQpP : IsPGroup 2 (Q.subgroupOf P) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : Q.subgroupOf P ≤ pCore 2 P := le_sSup ⟨hQnormal, hQpP⟩
  calc
    Q = (Q.subgroupOf P).map P.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQP).symm
    _ ≤ (pCore 2 P).map P.subtype := Subgroup.map_mono hle
    _ = twoCoreAmbient P := rfl

private theorem zSubgroup_le_twoCoreAmbient_of_pSet
    (S : Sylow 2 G) (h : Hypotheses G S)
    (P : Subgroup G)
    (hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G)) :
    zSubgroup S ≤ twoCoreAmbient P := by
  let Q : Subgroup G := twoCoreAmbient P
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hQne : Q ≠ ⊥ := hP.1.2.2.1
  have hQp : IsPGroup 2 Q := twoCoreAmbient_isPGroup P
  have hQnormalP : (Q.subgroupOf P).Normal :=
    twoCoreAmbient_normal_subgroupOf P
  have hPnormalizer : P ≤ N := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 P))).mp hQnormalP
  obtain ⟨TP, hTP⟩ := hP.1.2.1
  have hSP : (S : Subgroup G) ≤ P := by
    rw [← hTP]
    exact Subgroup.map_subtype_le (TP : Subgroup P)
  have hSN : (S : Subgroup G) ≤ N := hSP.trans hPnormalizer
  have hNtwo : IsTwoLocal N := ⟨Q, hQne, hQp, rfl⟩
  have hchar : IsCharacteristicTwoType N :=
    (h.local_solvable_characteristicTwo N hNtwo hSN).2
  let TN : Sylow 2 N := S.subtype hSN
  have hCoreNleTN : pCore 2 N ≤ (TN : Subgroup N) :=
    (pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal TN
  have hCoreNleS : twoCoreAmbient N ≤ (S : Subgroup G) := by
    calc
      twoCoreAmbient N = (pCore 2 N).map N.subtype := rfl
      _ ≤ (TN : Subgroup N).map N.subtype := Subgroup.map_mono hCoreNleTN
      _ = (S : Subgroup G) := by
        dsimp [TN]
        exact Subgroup.map_subgroupOf_eq_of_le hSN
  have hzS : zSubgroup S ≤ (S : Subgroup G) :=
    (zSubgroup_le_centerAmbient S).trans
      (Subgroup.map_subtype_le (Subgroup.center S))
  have hzN : zSubgroup S ≤ N := hzS.trans hSN
  have hzCentral : (zSubgroup S).subgroupOf N ≤
      Subgroup.centralizer (pCore 2 N : Set N) := by
    intro z hz q hq
    have hzCenterAmbient := zSubgroup_le_centerAmbient S hz
    obtain ⟨zs, hzs, hzsEq⟩ := hzCenterAmbient
    have hqAmbient : (q : G) ∈ twoCoreAmbient N :=
      Subgroup.mem_map_of_mem N.subtype hq
    have hqS : (q : G) ∈ (S : Subgroup G) := hCoreNleS hqAmbient
    let qs : S := ⟨(q : G), hqS⟩
    have hcomm := (Subgroup.mem_center_iff.mp hzs) qs
    have hzsEq' : (zs : G) = (z : G) := hzsEq
    apply Subtype.ext
    change (q : G) * (z : G) = (z : G) * (q : G)
    rw [← hzsEq']
    simpa [qs] using congrArg (fun x : S ↦ (x : G)) hcomm
  have hzCoreNInternal : (zSubgroup S).subgroupOf N ≤ pCore 2 N :=
    hzCentral.trans hchar
  have hzCoreN : zSubgroup S ≤ twoCoreAmbient N := by
    calc
      zSubgroup S = ((zSubgroup S).subgroupOf N).map N.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hzN).symm
      _ ≤ (pCore 2 N).map N.subtype := Subgroup.map_mono hzCoreNInternal
      _ = twoCoreAmbient N := rfl
  have hCoreNP : twoCoreAmbient N ≤ P := hCoreNleS.trans hSP
  have hNnormalizer : N ≤ Subgroup.normalizer (twoCoreAmbient N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (pCore 2 N))).mp
        (twoCoreAmbient_normal_subgroupOf N)
  have hCoreNnormalP : ((twoCoreAmbient N).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCoreNP).mpr
      (hPnormalizer.trans hNnormalizer)
  exact hzCoreN.trans (normal_pSubgroup_le_twoCoreAmbient
    (twoCoreAmbient N) P hCoreNP (twoCoreAmbient_isPGroup N) hCoreNnormalP)

private theorem zSubgroup_le_dSubgroup
    (S : Sylow 2 G) (h : Hypotheses G S) :
    zSubgroup S ≤ dSubgroup S := by
  rw [dSubgroup]
  apply le_sInf
  intro D hD
  obtain ⟨P, hP, rfl⟩ := hD
  exact zSubgroup_le_twoCoreAmbient_of_pSet S h P hP

omit [Finite G] in
private theorem dSubgroup_le_twoCoreAmbient_mSubgroup
    (S : Sylow 2 G)
    (hPnonempty :
      SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅) :
    dSubgroup S ≤ twoCoreAmbient (mSubgroup S) := by
  obtain ⟨P, hP⟩ := Set.nonempty_iff_ne_empty.mpr hPnonempty
  have hDleCoreP : dSubgroup S ≤ twoCoreAmbient P := by
    rw [dSubgroup]
    exact sInf_le ⟨P, hP, rfl⟩
  have hDp : IsPGroup 2 (dSubgroup S) :=
    (twoCoreAmbient_isPGroup P).to_le hDleCoreP
  have hDM : dSubgroup S ≤ mSubgroup S := by
    exact Subgroup.le_normalizer
  have hDnormalM : ((dSubgroup S).subgroupOf (mSubgroup S)).Normal := by
    unfold mSubgroup
    infer_instance
  exact normal_pSubgroup_le_twoCoreAmbient
    (dSubgroup S) (mSubgroup S) hDM hDp hDnormalM

public theorem lemma_four_one_core_normalizer
    (S : Sylow 2 G) (h : Hypotheses G S)
    (hPnonempty :
      SectionThree.PSet (⊤ : Subgroup G) (S : Subgroup G) ≠ ∅) :
    twoCoreAmbient (mSubgroup S) ≠ ⊥ ∧
      Subgroup.normalizer (S : Set G) ≤ mSubgroup S := by
  have hzNe : zSubgroup S ≠ ⊥ := zSubgroup_ne_bot S h.even_order
  have hzD : zSubgroup S ≤ dSubgroup S := zSubgroup_le_dSubgroup S h
  have hDCore : dSubgroup S ≤ twoCoreAmbient (mSubgroup S) :=
    dSubgroup_le_twoCoreAmbient_mSubgroup S hPnonempty
  refine ⟨?_, ?_⟩
  · intro hcore
    apply hzNe
    apply eq_bot_iff.mpr
    simpa [hcore] using hzD.trans hDCore
  · simpa [mSubgroup] using normalizer_s_le_normalizer_d S

end Stellmacher.SectionFour
