module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelection
public import Theory.GroupTheory.PCoreImage

/-!
# Simultaneous source choices for original 4.3.2

Maximize the order of O₂(LT) ∩ H among the outside maximal two-locals
containing L, then maximize the order of T ∩ H. Sylow conjugation in N(L)
preserves the first maximum because O₂(LT) is the intersection of T with
the normal section centralizer. The resulting I = L(O₂(LT) ∩ H) has the
original inclusion maximality and belongs to μ*. Consequently the genuine
C.2.8 setup uses this same I, H, T and full omega-center commutator.

The escaping containing component is a separate source obligation. Nothing
here identifies the chosen Chapter 12 module with that full module.
Source: Aschbacher–Smith 4.2.12 and 4.3.2–4, printed pp.610–614.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The local core is the intersection with the normal section centralizer. -/
theorem source_core_section_intersection (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ sectionCentralizerIn (normalizer (L : Set G)) L := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := sectionCentralizerIn (normalizer (L : Set G)) L
  have hyp := source_hypothesis411 h (unique_sylow_join D h)
  have hsyl := ChapterA.Section04.sylow_core_sectionCentralizer T L
    hyp.plus_perfect D.sylow_normalizes_component
  rw [← sectionCentralizerIn_eq_twoSectionCentralizer] at hsyl
  obtain ⟨P,hP⟩ := hsyl
  change (P : Subgroup C).map C.subtype = Q at hP
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have he := P.is_maximal' (T.isPGroup'.comap_subtype (K := C))
    (show (P : Subgroup C) ≤ (T : Subgroup G).subgroupOf C from
      fun x hx => hQT (hP ▸ mem_map_of_mem C.subtype hx))
  have hm := congrArg (map C.subtype) he
  change ((T : Subgroup G).subgroupOf C).map C.subtype = _ at hm
  rw [subgroupOf_map_subtype,hP] at hm
  exact hm.symm

/-- Sylow conjugacy in the fixed normalizer preserves L. -/
private theorem conjugate_into_source_sylow (D : ChosenModule T L V)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hWM : W ≤ normalizer (L : Set G)) :
    ∃ g : normalizer (L : Set G),
      W.map (MulAut.conj (g : G)).toMonoidHom ≤ (T : Subgroup G) := by
  let M := normalizer (L : Set G)
  obtain ⟨P,hWP⟩ := (hW.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M P (T.subtype D.sylow_normalizes_component)
  let e := MulAut.conj (g : G)
  have hPg : ((P : Subgroup M).map M.subtype).map e.toMonoidHom = (T : Subgroup G) := by
    have hh := congrArg (fun Z : Sylow 2 M => (Z : Subgroup M).map M.subtype) hg
    change (((P : Subgroup M).map (MulAut.conj g).toMonoidHom).map M.subtype) = _ at hh
    rw [map_map] at hh ⊢
    change (P : Subgroup M).map (M.subtype.comp (MulAut.conj g).toMonoidHom) = _ at hh
    change (P : Subgroup M).map (e.toMonoidHom.comp M.subtype) =
      ((T : Subgroup G).subgroupOf M).map M.subtype at hh
    rwa [map_subgroupOf_eq_of_le D.sylow_normalizes_component] at hh
  refine ⟨g,?_⟩
  rw [← hPg]
  apply map_mono
  rw [← map_subgroupOf_eq_of_le hWM]
  exact map_mono hWP

/-- A maximal core intersection, followed by a maximal Sylow intersection. -/
structure OutsideChoice (T : Sylow 2 G) (L : Subgroup G) where
  H : Subgroup G
  maximal : IsMaximalTwoLocal H
  contains : L ≤ H
  outside : H ≠ normalizer (L : Set G)
  core_max : ∀ J : Subgroup G, IsMaximalTwoLocal J → L ≤ J →
    J ≠ normalizer (L : Set G) →
    Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J : Subgroup G) ≤
      Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H : Subgroup G)
  sylow_max : ∀ J : Subgroup G, IsMaximalTwoLocal J → L ≤ J →
    J ≠ normalizer (L : Set G) →
    Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H : Subgroup G) ≤
      Nat.card ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J : Subgroup G) →
    Nat.card ((T : Subgroup G) ⊓ J : Subgroup G) ≤ Nat.card ((T : Subgroup G) ⊓ H : Subgroup G)

/-- The two finite maximal choices require only failure of uniqueness over L. -/
theorem exists_outside_choice (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (OutsideChoice T L) := by
  classical
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let candidates : Set (Subgroup G) := {H | IsMaximalTwoLocal H ∧ L ≤ H ∧ H ≠ M}
  have hu := unique_sylow_join D h
  have hn : candidates.Nonempty := by
    by_contra hn
    exact hnot ⟨hu.1,L.le_normalizer,fun H hH hLH => by
      by_contra he
      exact hn ⟨H,hH,hLH,he⟩⟩
  obtain ⟨H0,h0,hm0⟩ := Set.exists_max_image candidates
    (fun H => Nat.card (Q ⊓ H : Subgroup G)) candidates.toFinite hn
  let best : Set (Subgroup G) := {H | H ∈ candidates ∧
    Nat.card (Q ⊓ H0 : Subgroup G) ≤ Nat.card (Q ⊓ H : Subgroup G)}
  obtain ⟨H,hH,hm⟩ := Set.exists_max_image best
    (fun H => Nat.card ((T : Subgroup G) ⊓ H : Subgroup G)) best.toFinite ⟨H0,h0,le_rfl⟩
  exact ⟨⟨H,hH.1.1,hH.1.2.1,hH.1.2.2,
    fun J hJ hLJ hJM => (hm0 J ⟨hJ,hLJ,hJM⟩).trans hH.2,
    fun J hJ hLJ hJM hb => hm J ⟨⟨hJ,hLJ,hJM⟩,hH.2.trans hb⟩⟩⟩

/-- The simultaneous maximum has a full Sylow intersection in H ∩ N(L). -/
theorem OutsideChoice.local_sylow (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L) :
    ∃ P : Sylow 2 (c.H ⊓ normalizer (L : Set G) : Subgroup G),
      (P : Subgroup _).map (c.H ⊓ normalizer (L : Set G)).subtype =
        (T : Subgroup G) ⊓ c.H := by
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let S := (T : Subgroup G) ⊓ c.H
  let A := c.H ⊓ M
  have hQ : Q = (T : Subgroup G) ⊓ C := source_core_section_intersection D h
  have hSA : S ≤ A := le_inf inf_le_right (inf_le_left.trans D.sylow_normalizes_component)
  obtain ⟨P,hSP⟩ := ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := A)).exists_le_sylow
  let W := (P : Subgroup A).map A.subtype
  have hSW : S ≤ W := by
    rw [← map_subgroupOf_eq_of_le hSA]
    exact map_mono hSP
  have hWA : W ≤ A := map_subtype_le _
  obtain ⟨g,hWg⟩ := conjugate_into_source_sylow D (P.isPGroup'.map A.subtype)
    (hWA.trans inf_le_right)
  let e := MulAut.conj (g : G)
  have hLg : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp g.property
  have hMg : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  have hCg : C.map e.toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp
    (sectionCentralizerIn_normalized (show M ≤ normalizer (L : Set G) from le_rfl) g.property)
  have hHge : c.H.map e.toMonoidHom ≠ M := by
    intro he
    exact c.outside ((map_injective e.injective) (he.trans hMg.symm))
  have hRg : (Q ⊓ c.H).map e.toMonoidHom ≤ Q ⊓ c.H.map e.toMonoidHom := by
    apply le_inf _ (map_mono inf_le_right)
    apply le_trans (b := (T : Subgroup G) ⊓ C) ?_ hQ.ge
    apply le_inf
    · exact (map_mono (show Q ⊓ c.H ≤ W from
        (le_inf (inf_le_left.trans (hQ.le.trans inf_le_left)) inf_le_right).trans hSW)).trans hWg
    · exact (map_mono (inf_le_left.trans (hQ.le.trans inf_le_right))).trans hCg.le
  have hb : Nat.card (Q ⊓ c.H : Subgroup G) ≤ Nat.card (Q ⊓ c.H.map e.toMonoidHom : Subgroup G) := by
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using card_le_of_le hRg
  have hmax := c.sylow_max _ (Theory.Quasithin.isMaximalTwoLocal_map e c.maximal)
    (hLg.ge.trans (map_mono (f := e.toMonoidHom) c.contains)) hHge hb
  have hcard := card_le_of_le (le_inf hWg (map_mono (f := e.toMonoidHom) (hWA.trans inf_le_left)))
  rw [card_map_of_injective (f := e.toMonoidHom) e.injective] at hcard
  exact ⟨P,(eq_of_le_of_card_ge hSW (hcard.trans hmax)).symm⟩

/-- The intermediate subgroup determined by the simultaneous choice. -/
@[expose] noncomputable def OutsideChoice.intermediate (c : OutsideChoice T L) : Subgroup G :=
  L ⊔ ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ c.H)

/-- The selected radical is exactly the original local-core intersection. -/
theorem OutsideChoice.intermediate_core (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L) :
    c.intermediate.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ c.H := by
  have hIH : c.intermediate ≤ c.H := sup_le c.contains inf_le_right
  have hc := (intermediate_core_identities D h (show L ≤ c.intermediate from le_sup_left)
    (sup_le_sup_left inf_le_left L)).2
  apply le_antisymm
  · exact le_inf (hc.le.trans inf_le_right) ((pCoreIn_le 2 _).trans hIH)
  · rw [hc]
    exact le_inf le_sup_right inf_le_left

/-- The global core maximum bounds every covering counterexample containing L. -/
theorem OutsideChoice.counterexample_core_bound (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L)
    {Mminus J : Subgroup G} (hminus : Mminus ≤ normalizer (L : Set G))
    (hJ : J ∈ mu (normalizer (L : Set G)) L Mminus) (hLJ : L ≤ J) :
    Nat.card (J.pCoreIn 2) ≤ Nat.card (c.intermediate.pCoreIn 2) := by
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hyp := source_hypothesis411 h (unique_sylow_join D h)
  have hRC := core_le_sectionCentralizer_of_eta hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hminus hJ.1
  obtain ⟨H,hH,hJH,hout⟩ := exists_maximal_outside_of_mu hJ
  obtain ⟨g,hRg⟩ := conjugate_into_source_sylow D (isPGroup_pCoreIn 2 J) (hRC.trans inf_le_left)
  let e := MulAut.conj (g : G)
  have hLg : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp g.property
  have hMg : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  have hCg : C.map e.toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp
    (sectionCentralizerIn_normalized (show M ≤ normalizer (L : Set G) from le_rfl) g.property)
  have houtg : H.map e.toMonoidHom ≠ M := by
    intro he
    have hHM : H = M := (map_injective e.injective) (he.trans hMg.symm)
    exact hout hHM.le
  have hcoreg : (J.pCoreIn 2).map e.toMonoidHom ≤ Q ⊓ H.map e.toMonoidHom := by
    refine le_inf ?_ (map_mono ((pCoreIn_le 2 J).trans hJH))
    exact (le_inf hRg ((map_mono hRC).trans hCg.le)).trans
      (source_core_section_intersection D h).ge
  have hb := (card_le_of_le hcoreg).trans (c.core_max _
    (Theory.Quasithin.isMaximalTwoLocal_map e hH)
    (hLg.ge.trans (map_mono (f := e.toMonoidHom) (hLJ.trans hJH))) houtg)
  rw [card_map_of_injective (f := e.toMonoidHom) e.injective] at hb
  rwa [c.intermediate_core D h]

/-- This same intermediate subgroup is maximal for the original pushing relation. -/
theorem OutsideChoice.intermediate_muStar (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L) :
    c.intermediate ∈ muStar (normalizer (L : Set G)) L
      (coveringOvergroup (normalizer (L : Set G)) L c.intermediate) := by
  let M := normalizer (L : Set G)
  let I := c.intermediate
  have hu := unique_sylow_join D h
  have hIM : I ≤ M := (sup_le_sup_left inf_le_left L).trans
    ((sup_le le_sup_left (pCoreIn_le 2 _)).trans hu.2.1)
  have hcover : (L : Set G) ⊆ (I : Set G) * (L.pCoreIn 2 : Set G) :=
    fun x hx => ⟨x,(show L ≤ I from le_sup_left) hx,1,one_mem _,mul_one x⟩
  have hne : I.pCoreIn 2 ≠ ⊥ := by
    rw [c.intermediate_core D h]
    exact fun he => D.ne_bot (bot_unique ((le_inf D.le_core
      (D.le_component.trans c.contains)).trans_eq he))
  obtain ⟨hs,heta⟩ := coveringOvergroup_eta L.le_normalizer le_rfl hIM hcover hne
  have hnot : ¬ UniqueMaximalOvergroup I M := fun hi =>
    c.outside (hi.2.2 c.H c.maximal (sup_le c.contains inf_le_right))
  refine ⟨mem_mu_of_eta_not_unique hu.1 hs.1 heta hnot,?_⟩
  intro J hJ hIJ hlt
  have hLJ : L ≤ J := by
    intro x hx
    exact (hIJ.2 ⟨(show L ≤ I from le_sup_left) hx,hx⟩).1
  exact hlt.ne (eq_of_le_of_card_ge hlt.le (c.counterexample_core_bound D h hs.1 hJ hLJ))

/-- Strict extensions of the selected Sylow intersection are uniqueness subgroups. -/
theorem OutsideChoice.strict_unique (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L)
    {X : Subgroup G} (hSX : (T : Subgroup G) ⊓ c.H < X) (hXT : X ≤ (T : Subgroup G)) :
    UniqueMaximalOvergroup (L ⊔ X) (normalizer (L : Set G)) := by
  have hu := unique_sylow_join D h
  refine ⟨hu.1,sup_le L.le_normalizer (hXT.trans D.sylow_normalizes_component),?_⟩
  intro J hJ hLXJ
  by_contra hJM
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    (source_core_section_intersection D h).le.trans inf_le_left
  have hR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ c.H ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ J :=
    le_inf inf_le_left ((le_inf (inf_le_left.trans hQT) inf_le_right).trans
      (hSX.le.trans (le_sup_right.trans hLXJ)))
  have hc := c.sylow_max J hJ (le_sup_left.trans hLXJ) hJM (card_le_of_le hR)
  have hXJ : X ≤ (T : Subgroup G) ⊓ J := le_inf hXT (le_sup_right.trans hLXJ)
  have he := eq_of_le_of_card_ge (hSX.le.trans hXJ) hc
  exact hSX.not_ge (hXJ.trans he.ge)

/-- Original maximality of I under inclusion, for this same simultaneous choice. -/
theorem OutsideChoice.intermediate_maximal (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L)
    {J : Subgroup G} (hIJ : c.intermediate < J)
    (hJ : J ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    UniqueMaximalOvergroup J (normalizer (L : Set G)) := by
  have hu := unique_sylow_join D h
  have hLJ : L ≤ J := le_sup_left.trans hIJ.le
  obtain ⟨heJ,hcJ⟩ := intermediate_core_identities D h hLJ hJ
  refine ⟨hu.1,hJ.trans ((sup_le le_sup_left (pCoreIn_le 2 _)).trans hu.2.1),?_⟩
  intro K hK hJK
  by_contra hKM
  have hRK : J.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ K :=
    le_inf (hcJ.le.trans inf_le_right) ((pCoreIn_le 2 J).trans hJK)
  have hb := (card_le_of_le hRK).trans (c.core_max K hK (hLJ.trans hJK) hKM)
  have hcI := c.intermediate_core D h
  have hRI : c.intermediate.pCoreIn 2 ≤ J.pCoreIn 2 := by
    rw [hcJ,hcI]
    exact le_inf (le_sup_right.trans hIJ.le) inf_le_left
  have he := eq_of_le_of_card_ge hRI (by rwa [hcI])
  have hIe : c.intermediate = L ⊔ c.intermediate.pCoreIn 2 := by rw [hcI]; rfl
  exact hIJ.ne (hIe.trans ((congrArg (fun R : Subgroup G => L ⊔ R) he).trans heJ.symm))

/-- C.2.8 uses the original T and the core of the same I chosen above. -/
theorem OutsideChoice.c28 (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (c : OutsideChoice T L) :
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple c.H (c.H ⊓ normalizer (L : Set G))
      L (c.intermediate.pCoreIn 2)
      (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
  have hu := unique_sylow_join D h
  have hyp := source_hypothesis411 h hu
  have hI := c.intermediate_muStar D h
  have hs : coveringOvergroup (normalizer (L : Set G)) L c.intermediate ∈
      sigma (normalizer (L : Set G)) L := by
    refine ⟨sup_le (hI.1.1.1.trans ?_) inf_le_left,?_⟩
    · exact sup_le
        ((sup_le_sup_left inf_le_left L).trans ((sup_le le_sup_left (pCoreIn_le 2 _)).trans hu.2.1))
        inf_le_left
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hsyl := ChapterA.Section04.sylow_core_sectionCentralizer T L
    hyp.plus_perfect D.sylow_normalizes_component
  rw [← sectionCentralizerIn_eq_twoSectionCentralizer] at hsyl
  obtain ⟨P,hP⟩ := hsyl
  have hout : ¬ c.H ≤ normalizer (L : Set G) :=
    fun hh => c.outside (c.maximal.eq_of_le hu.1.1 hh)
  have hC := Section02.Unitary.source_C28_of_muStar h D hu hs hI c.maximal
    (sup_le c.contains inf_le_right) hout P
    ((c.intermediate_core D h).le.trans (inf_le_left.trans hP.ge))
  rw [hP] at hC
  have he : (solvableResidual (L ⊓ c.H : Subgroup G)).map (L ⊓ c.H).subtype = L := by
    rw [inf_eq_left.mpr c.contains]
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
    rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]
  rwa [he] at hC

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
