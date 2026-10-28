module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionConstrainedQuotient
public import Theory.GroupTheory.NormalizerCentralizerTwoLocal

/-!
# The full normalizer in the aligned ordinary branch

The ordinary component centralizes the nontrivial O₂(H). If a two-group A
containing S = T ∩ H normalizes K, then C_A(K) is nontrivial, and its normalizer
gives a genuine two-local containing KA. When A also normalizes L, conjugation
inside N_G(L) aligns A with the original T. Both maxima in OutsideChoice then
force A = S. Applying the normalizer condition inside an arbitrary two-group
gives that the same S is Sylow in N_G(K), and that T cannot normalize K.

If Z(K) is nontrivial, the source odd-core bound makes it a characteristic
two-group, proving H = N_G(K). For centerless K the remaining sufficient input
is O₂(C_G(K)) ≠ 1, on the literal ambient centralizer. The final constructor
retains this input explicitly; it does not assert the unconditional 4.3.3 equality.

Source: Aschbacher–Smith 4.3.2–3, printed pp.613–614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The ordinary component centralizes the original ambient two-core of H. -/
theorem OutsideChoice.ordinary_core_centralizes
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K) :
    c.H.pCoreIn 2 ≤ centralizer (K.map c.H.subtype : Set G) := by
  let : Group.IsNilpotent (pCore 2 c.H) := pCore_isPGroup.isNilpotent
  have hc := ho.le_centralizer_of_solvable_normal (pCore 2 c.H)
  apply le_centralizer_iff.mp
  rintro _ ⟨k,hk,rfl⟩ _ ⟨q,hq,rfl⟩
  exact congrArg Subtype.val (hc hk q hq)

/-- The centralizer of K in the original Sylow intersection contains the nontrivial O₂(H). -/
theorem OutsideChoice.ordinary_sylow_centralizer_ne_bot
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K) :
    ((T : Subgroup G) ⊓ c.H) ⊓ centralizer (K.map c.H.subtype : Set G) ≠ ⊥ := by
  obtain ⟨P,hP⟩ := (c.sylow_data D h hpsl).2.2
  have hQ := le_inf ((pCoreIn_le_sylow c.H P).trans_eq hP)
    (c.ordinary_core_centralizes K ho)
  exact fun he => (c.c28 D h).core_nontrivial (bot_unique (hQ.trans_eq he))

private theorem conjugate_twoGroup_into_sylow (D : ChosenModule T L V)
    {A : Subgroup G} (hp : IsPGroup 2 A) (hAM : A ≤ normalizer (L : Set G)) :
    ∃ g : normalizer (L : Set G),
      A.map (MulAut.conj (g : G)).toMonoidHom ≤ (T : Subgroup G) := by
  let M := normalizer (L : Set G)
  obtain ⟨P,hAP⟩ := (hp.comap_subtype (K := M)).exists_le_sylow
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
  rw [← map_subgroupOf_eq_of_le hAM]
  exact map_mono hAP

/-- Maximality of the aligned choice rules out a larger two-group normalizing both L and K. -/
theorem OutsideChoice.ordinary_normalizing_twoGroup_eq_sylow
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (A : Subgroup G) (hp : IsPGroup 2 A)
    (hSA : (T : Subgroup G) ⊓ c.H ≤ A)
    (hAM : A ≤ normalizer (L : Set G))
    (hAK : A ≤ normalizer (K.map c.H.subtype : Set G)) :
    A = (T : Subgroup G) ⊓ c.H := by
  let B := K.map c.H.subtype
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hne : A ⊓ centralizer (B : Set G) ≠ ⊥ := by
    intro he
    exact c.ordinary_sylow_centralizer_ne_bot D h hpsl K ho
      (bot_unique ((inf_le_inf_right _ hSA).trans_eq he))
  obtain ⟨J,hJ,hBAJ⟩ := local_overgroup_of_nontrivial_two_centralizer B A hp hAK hne
  have hAJ : A ≤ J := le_sup_right.trans hBAJ
  have hBJ : B ≤ J := le_sup_left.trans hBAJ
  obtain ⟨g,hAg⟩ := conjugate_twoGroup_into_sylow D hp hAM
  let e := MulAut.conj (g : G)
  have hLg : L.map e.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp g.property
  have hMg : M.map e.toMonoidHom = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
  have hCg : C.map e.toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp
    (sectionCentralizerIn_normalized (show M ≤ normalizer (L : Set G) from le_rfl) g.property)
  have houtg : J.map e.toMonoidHom ≠ M := by
    intro he
    have hJM : J = M := map_injective e.injective (he.trans hMg.symm)
    exact hout (hBJ.trans_eq hJM)
  have hQ : Q = (T : Subgroup G) ⊓ C := source_core_section_intersection D h
  have hRA : Q ⊓ c.H ≤ A :=
    (le_inf (inf_le_left.trans (hQ.le.trans inf_le_left)) inf_le_right).trans hSA
  have hRg : (Q ⊓ c.H).map e.toMonoidHom ≤ Q ⊓ J.map e.toMonoidHom := by
    apply le_inf ?_ (map_mono (hRA.trans hAJ))
    apply le_trans (b := (T : Subgroup G) ⊓ C) ?_ hQ.ge
    exact le_inf ((map_mono hRA).trans hAg)
      ((map_mono (inf_le_left.trans (hQ.le.trans inf_le_right))).trans hCg.le)
  have hb : Nat.card (Q ⊓ c.H : Subgroup G) ≤ Nat.card (Q ⊓ J.map e.toMonoidHom : Subgroup G) := by
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using card_le_of_le hRg
  have hmax := c.sylow_max _ (Theory.Quasithin.isMaximalTwoLocal_map e hJ)
    (hLg.ge.trans (map_mono (hLK.trans hBJ))) houtg hb
  have hc := card_le_of_le (le_inf hAg (map_mono hAJ))
  rw [card_map_of_injective e.injective] at hc
  exact (eq_of_le_of_card_ge hSA (hc.trans hmax)).symm

/-- The normalizer condition promotes the bound to every two-group normalizing K. -/
theorem OutsideChoice.ordinary_twoGroup_maximal
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (P : Subgroup G) (hp : IsPGroup 2 P)
    (hSP : (T : Subgroup G) ⊓ c.H ≤ P)
    (hPK : P ≤ normalizer (K.map c.H.subtype : Set G)) :
    P = (T : Subgroup G) ⊓ c.H := by
  let S := (T : Subgroup G) ⊓ c.H
  let A := P ⊓ normalizer (S : Set G)
  have hAS : A = S := c.ordinary_normalizing_twoGroup_eq_sylow D h hpsl K ho hLK hout
    A (hp.to_le inf_le_left) (le_inf hSP S.le_normalizer)
    (inf_le_right.trans (c.sylow_data D h hpsl).2.1) (inf_le_left.trans hPK)
  let : Group.IsNilpotent P := hp.isNilpotent
  have hn : normalizer (S.subgroupOf P : Set P) = S.subgroupOf P := by
    apply le_antisymm ?_ (S.subgroupOf P).le_normalizer
    rw [← subgroupOf_normalizer_eq hSP]
    intro x hx
    exact hAS.le ⟨x.property,hx⟩
  have ht := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P)) _ hn
  exact le_antisymm (subgroupOf_eq_top.mp ht) hSP

/-- The original T ∩ H is Sylow in the full ambient normalizer of K. -/
theorem OutsideChoice.ordinary_normalizer_sylow
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    ∃ P : Sylow 2 (normalizer (K.map c.H.subtype : Set G)),
      (P : Subgroup _).map (normalizer (K.map c.H.subtype : Set G)).subtype =
        (T : Subgroup G) ⊓ c.H := by
  let N := normalizer (K.map c.H.subtype : Set G)
  let S := (T : Subgroup G) ⊓ c.H
  have hHN : c.H ≤ N := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hKN
  have hSN : S ≤ N := inf_le_right.trans hHN
  obtain ⟨P,hSP⟩ := ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    (K := N)).exists_le_sylow
  refine ⟨P,c.ordinary_twoGroup_maximal D h hpsl K ho hLK hout _
    (P.isPGroup'.map N.subtype) ?_ (map_subtype_le _)⟩
  change S ≤ (P : Subgroup N).map N.subtype
  rw [← map_subgroupOf_eq_of_le hSN]
  exact map_mono hSP

/-- The original T has exactly the same intersection with H and with the full normalizer of K. -/
theorem OutsideChoice.ordinary_normalizer_sylow_intersection
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    (T : Subgroup G) ⊓ normalizer (K.map c.H.subtype : Set G) = (T : Subgroup G) ⊓ c.H := by
  have hHN : c.H ≤ normalizer (K.map c.H.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hKN
  exact c.ordinary_twoGroup_maximal D h hpsl K ho hLK hout _
    (T.isPGroup'.to_le inf_le_left) (inf_le_inf_left _ hHN) inf_le_right

/-- The ambient Sylow cannot normalize K, without assuming the full normalizer equality. -/
theorem OutsideChoice.ordinary_component_not_normalized_by_sylow
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    ¬ (T : Subgroup G) ≤ normalizer (K.map c.H.subtype : Set G) := by
  intro ht
  have he := c.ordinary_normalizer_sylow_intersection D h hpsl K ho hLK hout hKN
  rw [inf_eq_left.mpr ht] at he
  exact (c.sylow_data D h hpsl).1.ne he.symm

/-- The nontrivial-center branch of the full normalizer equality. The source odd-core bound makes the center a two-group. -/
theorem OutsideChoice.ordinary_normalizer_of_center_ne_bot
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hKN : K.Normal) (hz : center K ≠ ⊥) :
    c.H = normalizer (K.map c.H.subtype : Set G) := by
  let := ho.2
  have hodd := ho.1.pPrimeCore_eq_bot (c.c28 D h).oddCore_eq_bot
  have hcore : pCore 2 K ≠ ⊥ := by
    rwa [← IsQuasisimple.center_eq_pCore hodd]
  let B := K.map c.H.subtype
  let e : K ≃* B := K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  have hbcore : pCore 2 B ≠ ⊥ := by
    intro he
    have hh := pCore_map_iso 2 e
    rw [he] at hh
    exact hcore ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  have hHN : c.H ≤ normalizer (B : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [B,subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hKN
  obtain ⟨J,hJ,hNJ⟩ := exists_twoLocal_overgroup_normalizer B (pCore 2 B) hbcore pCore_isPGroup
  exact le_antisymm hHN (hNJ.trans (c.maximal.2 hJ (hHN.trans hNJ)))

omit [Finite G] in
/-- The literal ordinary normalizer consumer of a nontrivial full centralizer core. -/
theorem OutsideChoice.ordinary_normalizer_of_centralizer_core
    (c : OutsideChoice T L) (K : Subgroup c.H) (hKN : K.Normal)
    (hc : pCore 2 (centralizer (K.map c.H.subtype : Set G)) ≠ ⊥) :
    c.H = normalizer (K.map c.H.subtype : Set G) := by
  let B := K.map c.H.subtype
  have hHN : c.H ≤ normalizer (B : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [B,subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hKN
  exact normalizer_eq_of_centralizer_twoCore_ne_bot c.maximal hHN hc

/-- The ordinary constructor retains the literal original H and embedded K,
together with ordinary component status, for an actual branch exclusion. -/
theorem OutsideChoice.exists_ordinary_sourceConfiguration_of_normalizer
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H)
    (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (houtK : ¬ K.map c.H.subtype ≤ normalizer (L : Set G))
    (hKN : K.Normal) (hNK : c.H = normalizer (K.map c.H.subtype : Set G)) :
    ∃ d : SourceConfiguration T L, d.H = c.H ∧
      d.K.map d.H.subtype = K.map c.H.subtype ∧ IsComponent d.H d.K := by
  have hK := ho.isCComponent
  have hq := c.component_quotient_of_ordinary D h K ho
  have hu := unique_sylow_join D h
  have hout : ¬ c.H ≤ normalizer (L : Set G) :=
    fun hh => c.outside (c.maximal.eq_of_le hu.1.1 hh)
  have hLI : L ≤ c.intermediate := le_sup_left
  have hI : c.intermediate ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sup_le_sup_left inf_le_left L
  have hIH : c.intermediate ≤ c.H := sup_le c.contains inf_le_right
  have hmax := fun J hIJ hJ => c.intermediate_maximal D h (J := J) hIJ hJ
  obtain ⟨hIe,hIc⟩ := intermediate_core_identities D h hLI hI
  obtain ⟨hST,hnS,hS⟩ := c.sylow_data D h hpsl
  obtain ⟨hRS,hRJ⟩ := selected_core_sylow D h hLI hI hmax c.maximal hIH hout
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    (source_core_section_intersection D h).le.trans inf_le_left
  have hTQ : (T : Subgroup G) ≤
      normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  obtain ⟨t,ht,htout,htn,htsq,htcore⟩ := exists_source_crossing_in_core hST hQT hTQ hRS
  have hc := c.c28 D h
  exact ⟨{
    I := c.intermediate
    H := c.H
    K := K
    t := t
    le_I := hLI
    I_le := hI
    I_maximal := hmax
    I_eq := hIe
    core_intersection := hIc
    maximal := c.maximal
    I_le_H := hIH
    outside := hout
    c28 := hc
    component := hK
    quotient := hq
    le_component := hLK
    component_outside := houtK
    component_normal := hKN
    component_cases := hK.component_or_generalizedFitting_eq_pCore hc.oddCore_eq_bot
    normalizer_component := hNK
    sylow_strict := hST
    sylow := hS
    normalizer_sylow := hnS
    strict_unique := fun _ hSX hXT => c.strict_unique D h hSX hXT
    core_sylow := hRS
    core_join := hRJ
    crossing_mem := ht
    crossing_outside := htout
    crossing_normalizes := htn
    crossing_square := htsq
    crossing_core := htcore },rfl,rfl,ho⟩

/-- The aligned configuration now requires only the centerless ordinary centralizer-core
input. Its original Sylow marking and failure of T-normalization are supplied here.
The centralizer-core input remains with the global uniqueness assembly owner. -/
theorem exists_sourceConfiguration_of_centerless_centralizer_core
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hcentralizer : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal → center K = ⊥ →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ c.H)
        (normalizer (K.map c.H.subtype : Set G)) →
      (¬ (T : Subgroup G) ≤ normalizer (K.map c.H.subtype : Set G)) →
      pCore 2 (centralizer (K.map c.H.subtype : Set G)) ≠ ⊥)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  apply exists_sourceConfiguration_of_ordinary_normalizer D h hpsl ?_ hnot
  intro c K ho hLK hout hn
  by_cases hz : center K = ⊥
  · exact c.ordinary_normalizer_of_centralizer_core K hn (hcentralizer c K ho hLK hout hn hz
      (c.ordinary_normalizer_sylow D h hpsl K ho hLK hout hn)
      (c.ordinary_component_not_normalized_by_sylow D h hpsl K ho hLK hout hn))
  · exact c.ordinary_normalizer_of_center_ne_bot D h K ho hn hz

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
