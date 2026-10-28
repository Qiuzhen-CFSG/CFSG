module
public import CFSG.Quasithin.Chapter14.Section02.ProperComponent
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Faithful
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.PResidual.NormalClosureCover

/-!
# Placement of the selected component over its actual Sylow subgroup

The original H-core gives local-family membership for the selected subgroup.
For an exchanged component this applies directly at its normalizer in T.
Sylow conjugacy inside Mc transports the uniqueness theorem for its actual
C-components. In the other case, the decomposition from 14.1.18 bounds the
three-rank of M ∩ Mc by one; a join of three-rank at least two therefore has
Mc as its unique maximal two-local overgroup.

The final adapters consume the precise component-or-rank consequence of
14.2.9, or the diagram equality K = Kc together with its Sylow generation
mark. These catalogue inputs remain explicit: unique component containment
alone does not establish them. The proper-completion theorem applies the
placement result to the literal join K₁ ∨ Y ∨ S of 14.2.15.

Source: Aschbacher--Smith, 14.2.8--10, printed pp.983--984, and 14.2.15,
printed p.985; using 14.1.6 and 14.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter1
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Locality of the actual selected subgroup, using the original H-core. -/
theorem source_selected_mem_local
    (T : Sylow 2 G) (H K S : Subgroup G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hKH : K ≤ H) (hST : S ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 S (K ⊔ S))
    (hK : (K.subgroupOf (K ⊔ S)).IsCComponent)
    (hcore : H.pCoreIn 2 ≤ S) : K ∈ Chapter1.L G S := by
  exact proper_selected_mem_local H K S (K ⊔ S) hKH (hST.trans hH.2)
    le_sup_left le_sup_right hSylow hK hH.1 hcore


/-- For the exchanged source, the local-family membership at the literal
normalizer in T requires no new core or Sylow premise. -/
theorem source_paired_selected_mem_local
    (T : Sylow 2 G) (H : Subgroup G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup H) (hK : K.IsCComponent) :
    K.map H.subtype ∈ Chapter1.L G
      ((T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G)) := by
  let B := K.map H.subtype
  let S := (T : Subgroup G) ⊓ normalizer (B : Set G)
  have hBH : B ≤ H := map_subtype_le K
  have hBc : (B.subgroupOf H).IsCComponent := by
    simpa only [B,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hK
  have hBT : B ∈ Chapter1.L G (T : Subgroup G) :=
    (Chapter1.lemma_1_2_6 T hH).2 ((Chapter1.lemma_1_2_6 T hH).1 ⟨hBH,hBc⟩)
  have hcoreN : pCore 2 H ≤ normalizer (K : Set H) := by
    let := pCore_isPGroup (p := 2) (G := H) |>.isNilpotent
    rw [← normalizer_cComponent_quotient hK (pCore 2 H)]
    intro x hx
    change QuotientGroup.mk' (pCore 2 H) x ∈
      normalizer (K.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))
    rw [show QuotientGroup.mk' (pCore 2 H) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.2] at hh
  have hcore : H.pCoreIn 2 ≤ S :=
    le_inf hcoreT ((map_mono (f := H.subtype) hcoreN).trans (K.le_normalizer_map H.subtype))
  exact source_selected_mem_local T H B S hH hBH inf_le_left
    (Chapter1.Section02.Adequate.local_normalizer_isSylow hBT)
    (hBc.subgroupOf_of_le le_sup_left (sup_le hBH (inf_le_left.trans hH.2))) hcore

/-- An actual C-component has the same unique maximal local after any
Sylow change inside Mc. -/
theorem source_component_sylow_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc K : Subgroup G}
    (hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hK : K ∈ Chapter1.cComponentsIn Mc) (P : Sylow 2 Mc) :
    maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc} := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Mc P (T.subtype hMc.2)
  let e := MulAut.conj (g : G)
  have hMe : Mc.map e.toMonoidHom = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer g.property)
  let C := (K.subgroupOf Mc).map (MulAut.conj g).toMonoidHom
  have hC : C.IsCComponent := hK.2.map_equiv (MulAut.conj g)
  have hCe : C.map Mc.subtype = K.map e.toMonoidHom := by
    change ((K.subgroupOf Mc).map (MulAut.conj g).toMonoidHom).map Mc.subtype = _
    rw [map_map]
    have hh : Mc.subtype.comp (MulAut.conj g).toMonoidHom =
        e.toMonoidHom.comp Mc.subtype := rfl
    rw [hh,←map_map,map_subgroupOf_eq_of_le hK.1]
  have hKe : K.map e.toMonoidHom ∈ Chapter1.cComponentsIn Mc := by
    rw [←hCe]
    refine ⟨map_subtype_le C,?_⟩
    simpa only [subgroupOf,comap_map_eq_self_of_injective Mc.subtype_injective] using hC
  have hPT : ((P : Subgroup Mc).map Mc.subtype).map e.toMonoidHom = (T : Subgroup G) := by
    have hh := congrArg (fun Q : Sylow 2 Mc => (Q : Subgroup Mc).map Mc.subtype) hg
    change ((P : Subgroup Mc).map (MulAut.conj g).toMonoidHom).map Mc.subtype = _ at hh
    rw [map_map] at hh ⊢
    change (P : Subgroup Mc).map (e.toMonoidHom.comp Mc.subtype) = _ at hh
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hMc.2] using hh
  have heuniq := InitialSource.component_unique_maximal_overgroup
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    hG T hempty hMc hu hKe
  ext N
  constructor
  · intro hN
    have hn : N.map e.toMonoidHom ∈
        maximalTwoLocalOvergroups (K.map e.toMonoidHom ⊔ (T : Subgroup G)) := by
      refine ⟨Theory.GroupTheory.isMaximalTwoLocal_map e hN.1,?_⟩
      rw [←hPT,←Subgroup.map_sup]
      exact map_mono hN.2
    have hh : N.map e.toMonoidHom = Mc := Set.mem_singleton_iff.mp (heuniq ▸ hn)
    exact Set.mem_singleton_iff.mpr (map_injective e.injective (hh.trans hMe.symm))
  · rintro rfl
    exact ⟨hMc.1,sup_le hK.1 (map_subtype_le _)⟩

/-- The two original maximal locals have intersection of three-rank at most one. -/
theorem source_intersection_threeRank_le_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    primeRank 3 (M ⊓ Mc : Subgroup G) ≤ 1 := by
  obtain ⟨_,_,hI,_,_,_,_,_,_,_,_,hr,_,_,_⟩ :=
    source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  let I := (M ⊓ Mc).subgroupOf M
  let Q := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
  have hC : C.map M.subtype = M ⊓ centralizer (localModule T M : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hQM : (M ⊓ Mc).pCoreIn 2 ≤ M := (pCoreIn_le 2 _).trans inf_le_left
  have hcover : I ≤ C ⊔ Q := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [Subgroup.map_sup,hC,map_subgroupOf_eq_of_le hQM]
    change ((M ⊓ Mc).subgroupOf M).map M.subtype ≤ _
    rw [map_subgroupOf_eq_of_le inf_le_left]
    exact hI.le
  have hres := embedded_pResidual_le_of_normal_sup_pGroup C Q I
    (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype hcover
  have heI := primeRank_equiv 3 (subgroupOfEquivOfLe (show M ⊓ Mc ≤ M from inf_le_left))
  have heR := primeRank_equiv 3 ((pResidual 2 I).equivMapOfInjective I.subtype I.subtype_injective)
  have heC := primeRank_equiv 3 ((C.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hC))
  have hbound := primeRank_mono 3 hres
  have hresrank := ResidualCentralizerRank.primeRank_residual (G := I)
    (by decide : Nat.Coprime 2 3)
  calc
    primeRank 3 (M ⊓ Mc : Subgroup G) = primeRank 3 I := heI.symm
    _ = primeRank 3 (pResidual 2 I) := hresrank.symm
    _ = primeRank 3 ((pResidual 2 I).map I.subtype) := heR
    _ ≤ primeRank 3 C := hbound
    _ = primeRank 3 (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) := heC
    _ ≤ 1 := hr

/-- The rank-two case of 14.2.10: Sylow conjugacy and the original
intersection bound exclude the other maximal local. -/
theorem source_rank_two_sylow_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (P : Sylow 2 Mc) (X : Subgroup G) (hPX : (P : Subgroup Mc).map Mc.subtype ≤ X)
    (hXM : X ≤ Mc) (hrank : 2 ≤ primeRank 3 X) :
    maximalTwoLocalOvergroups X = {Mc} := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hpair⟩ :=
    source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hMc0 : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu.symm ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc :=
    (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans hMc0.2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Mc P (T.subtype hTMc)
  let a := MulAut.conj (g : G)
  have hMe : Mc.map a.toMonoidHom = Mc :=
    mem_normalizer_iff_map_conj_eq.mp (Mc.le_normalizer g.property)
  have hTX : (T : Subgroup G) ≤ X.map a.toMonoidHom := by
    intro x hx
    have hx' : (⟨x,hTMc hx⟩ : Mc) ∈ T.subtype hTMc := hx
    rw [←hg] at hx'
    obtain ⟨p,hp,hpx⟩ := hx'
    exact mem_map.mpr ⟨p,hPX (mem_map_of_mem _ hp),congrArg Subtype.val hpx⟩
  have hXe : X.map a.toMonoidHom ≤ Mc := (map_mono hXM).trans_eq hMe
  have hnot : ¬ X.map a.toMonoidHom ≤ M := by
    intro hXM'
    have hh := (primeRank_mono 3 (le_inf hXM' hXe)).trans
      (source_intersection_threeRank_le_one hG T hempty hM hu hmany hcard e)
    have he := primeRank_equiv 3 (X.equivMapOfInjective a.toMonoidHom a.injective)
    omega
  ext N
  constructor
  · intro hN
    have hn : N.map a.toMonoidHom ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨Theory.GroupTheory.isMaximalTwoLocal_map a hN.1,hTX.trans (map_mono hN.2)⟩
    rw [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hn
    have he : N.map a.toMonoidHom = Mc := hn.resolve_left (fun he => hnot (he ▸ map_mono hN.2))
    exact Set.mem_singleton_iff.mpr (map_injective a.injective (he.trans hMe.symm))
  · rintro rfl
    exact ⟨hMc0.1,hXM⟩

/-- The exact consequence of the source catalogue needed by 14.2.10.
The component-or-rank alternative is explicit: its model exclusions belong
to 14.2.9 and are not inferred from mere component containment. -/
theorem source_selected_sylow_placement_of_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (K S : Subgroup G) (hKM : K ≤ Mc)
    (hcatalogue : K ∈ Chapter1.cComponentsIn Mc ∨
      ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
        2 ≤ primeRank 3 (K ⊔ (P : Subgroup Mc).map Mc.subtype : Subgroup G)) :
    ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc} := by
  intro P hSP
  rcases hcatalogue with hK | hr
  · have hMc0 : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu.symm ▸ Set.mem_singleton Mc
    exact source_component_sylow_placement hG T hempty
      ⟨hMc0.1,(le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans hMc0.2⟩
      hu hK P
  · exact source_rank_two_sylow_placement hG T hempty hM hu hmany hcard e P
      (K ⊔ (P : Subgroup Mc).map Mc.subtype) le_sup_right
      (sup_le hKM (map_subtype_le _)) (hr P hSP)

/-- The diagram case, retaining the source equality K = Kc and the actual
Sylow generation mark. Neither follows from containment alone. -/
theorem source_diagram_selected_sylow_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (K Kc K₁ S : Subgroup G) (hKc : Kc ∈ Chapter1.cComponentsIn Mc)
    (heq : K = Kc) (hK₁K : K₁ ≤ K)
    (hgen : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      K ≤ K₁ ⊔ (P : Subgroup Mc).map Mc.subtype) :
    ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K₁ ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc} := by
  subst Kc
  intro P hSP
  have huniq := source_component_sylow_placement hG T hempty hMc hu hKc P
  ext N
  constructor
  · intro hN
    exact Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp (huniq ▸
      (show N ∈ maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) from
        ⟨hN.1,sup_le ((hgen P hSP).trans hN.2) (le_sup_right.trans hN.2)⟩)))
  · rintro rfl
    exact ⟨hMc.1,sup_le (hK₁K.trans hKc.1) (map_subtype_le _)⟩

/-- Literal proper-completion consumer. The 14.2.10 placement callback
is replaced by precisely the component-or-rank consequence of 14.2.9. -/
theorem source_proper_completion_sylow_of_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hKM : K ≤ Mc) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hcatalogue : K ∈ Chapter1.cComponentsIn Mc ∨
      ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
        2 ≤ primeRank 3 (K ⊔ (P : Subgroup Mc).map Mc.subtype : Subgroup G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S) :=
  source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH K S hST hi hN
    (source_selected_sylow_placement_of_catalogue hG T hempty hM hu hmany hcard e
      K S hKM hcatalogue) hcore

end CFSG.Quasithin.Chapter14.Section02

