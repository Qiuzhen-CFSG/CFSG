module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionAssembly
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# A normal escaping component containing the original rank-one L

The aligned full Sylow intersection puts L in the literal local component
family of H. The proved source 1.2.4 supplies a normal containing C-component.
If it lay in N(L), minimality would identify it with the nonsolvable normal
subgroup L, contradicting the outside choice of H.

For an ordinary component the core quotient is quasisimple. For a constrained
component its nontrivial characteristic two-core identifies H with its full
ambient normalizer. The other half of each branch remains explicit in the
final conditional configuration constructor. No full C.4.8 classification is
asserted here.

Source: Aschbacher–Smith 1.2.4 and 4.3.2–3, printed pp.505,613–614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The aligned source Sylow group places L in the literal local component family of H. -/
theorem OutsideChoice.local_component (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (c : OutsideChoice T L) :
    L.subgroupOf c.H ∈ Chapter1.L c.H (((T : Subgroup G) ⊓ c.H).subgroupOf c.H) := by
  let S := (T : Subgroup G) ⊓ c.H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hc := c.c28 D h
  have hS := (c.sylow_data D h hpsl).2.2
  have hLI : L ≤ c.intermediate := le_sup_left
  have hI : c.intermediate ≤ L ⊔ Q := sup_le_sup_left inf_le_left L
  have hIH : c.intermediate ≤ c.H := sup_le c.contains inf_le_right
  have hQ : Q ≤ (T : Subgroup G) := (source_core_section_intersection D h).le.trans inf_le_left
  have hRS : Q ⊓ c.H ≤ S := le_inf (inf_le_left.trans hQ) inf_le_right
  have hjoin : c.intermediate ⊔ S = L ⊔ S := by
    change (L ⊔ (Q ⊓ c.H)) ⊔ S = L ⊔ S
    rw [sup_assoc,sup_eq_right.mpr hRS]
  have hout : ¬ c.H ≤ normalizer (L : Set G) :=
    fun hh => c.outside (c.maximal.eq_of_le (unique_sylow_join D h).1.1 hh)
  have hR := (selected_core_sylow D h hLI hI
    (fun _ hIJ hJ => c.intermediate_maximal D h hIJ hJ) c.maximal hIH hout).2
  change c.intermediate.pCoreIn 2 = (c.intermediate ⊔ S).pCoreIn 2 at hR
  rw [hjoin] at hR
  have hne : (L ⊔ S).pCoreIn 2 ≠ ⊥ := by
    rw [← hR,c.intermediate_core D h]
    exact fun he => D.ne_bot (bot_unique ((le_inf D.le_core
      (D.le_component.trans c.contains)).trans_eq he))
  apply (Chapter1.mem_LIn_iff_subgroupOf (show S ≤ c.H from inf_le_right) c.contains).mp
  refine ⟨c.contains,?_,Chapter1.IsSylowIn.restrict hS le_sup_right
    (sup_le c.contains inf_le_right),hne⟩
  exact hc.component.subgroupOf_of_le le_sup_left
    (sup_le hc.component_le (le_inf inf_le_right (inf_le_left.trans D.sylow_normalizes_component)))

/-- Source 1.2.4 supplies an actual normal C-component containing L. It escapes
N(L): a contained component would equal the nonsolvable normal subgroup L. -/
theorem OutsideChoice.exists_normal_escaping_component (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (c : OutsideChoice T L) :
    ∃ K : Subgroup c.H, K.IsCComponent ∧ L ≤ K.map c.H.subtype ∧
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) ∧ K.Normal := by
  let B := L.subgroupOf c.H
  have hc := c.c28 D h
  obtain ⟨P,hP⟩ := (c.sylow_data D h hpsl).2.2
  have hPsub : ((T : Subgroup G) ⊓ c.H).subgroupOf c.H = (P : Subgroup c.H) := by
    apply map_injective c.H.subtype_injective
    exact (map_subgroupOf_eq_of_le inf_le_right).trans hP.symm
  have hB := c.local_component D h hpsl
  rw [hPsub] at hB
  have hPN : (P : Subgroup c.H) ≤ normalizer (B : Set c.H) := by
    change (P : Subgroup c.H) ≤ normalizer (L.subgroupOf c.H : Set c.H)
    rw [← subgroupOf_normalizer_eq c.contains]
    intro p hp
    exact D.sylow_normalizes_component (hP.le (mem_map_of_mem c.H.subtype hp)).1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (c.H ⧸ pCore 2 c.H) := by
    refine ⟨?_,hc.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hc.sqtk.stronglyQuasithin p hp ho)
  obtain ⟨K,⟨hK,hBK,hKN⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source hQ P hB hPN
  have hLK : L ≤ K.map c.H.subtype := by
    exact (map_subgroupOf_eq_of_le c.contains).ge.trans (map_mono hBK)
  refine ⟨K,hK,hLK,?_,hKN⟩
  intro hKM
  have hKB : K ≤ normalizer (B : Set c.H) := by
    change K ≤ normalizer (L.subgroupOf c.H : Set c.H)
    rw [← subgroupOf_normalizer_eq c.contains]
    intro k hk
    exact hKM (mem_map_of_mem c.H.subtype hk)
  have hBN : (B.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKB
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  have hBp : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe c.contains).symm.toMonoidHom)
    (subgroupOfEquivOfLe c.contains).symm.surjective
  have hBne : B ≠ ⊥ := by
    intro he
    have hmap := congrArg (map c.H.subtype) he
    change (L.subgroupOf c.H).map c.H.subtype = (⊥ : Subgroup c.H).map c.H.subtype at hmap
    rw [map_subgroupOf_eq_of_le c.contains,Subgroup.map_bot] at hmap
    exact D.ne_bot (bot_unique (D.le_component.trans_eq hmap))
  have hKB' : K ≤ B := hK.minimal B hBK hBne hBp
    (Subgroup.IsSubnormal.trans hBK hBN.isSubnormal hK.subnormal)
  have he : K.map c.H.subtype = L := by
    exact (congrArg (map c.H.subtype) (le_antisymm hKB' hBK)).trans
      (map_subgroupOf_eq_of_le c.contains)
  have hHN : c.H ≤ normalizer (K.map c.H.subtype : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hKN
  rw [he] at hHN
  exact c.outside (c.maximal.eq_of_le (unique_sylow_join D h).1.1 hHN)

/-- The ordinary branch already has a quasisimple intrinsic two-core quotient. -/
theorem OutsideChoice.component_quotient_of_ordinary
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (c : OutsideChoice T L) (K : Subgroup c.H) (hK : IsComponent c.H K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := hK.2
  have ho := hK.1.pPrimeCore_eq_bot (c.c28 D h).oddCore_eq_bot
  have he := IsQuasisimple.center_eq_pCore ho
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq he).symm.isSimpleGroup
  let : Nontrivial (K ⧸ pCore 2 K) := inferInstance
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' (pCore 2 K))
    (QuotientGroup.mk'_surjective _)

/-- In the constrained branch, the nontrivial characteristic two-core makes
maximal two-locality identify the full ambient normalizer. -/
theorem OutsideChoice.component_normalizer_of_constrained
    (c : OutsideChoice T L) (K : Subgroup c.H) (hK : K.IsCComponent)
    (hn : K.Normal) (hf : generalizedFitting K = pCore 2 K) :
    c.H = normalizer (K.map c.H.subtype : Set G) := by
  let B := K.map c.H.subtype
  have hkcore : pCore 2 K ≠ ⊥ := by
    intro he
    have hz := centralizer_generalizedFitting_le K
    rw [hf,he] at hz
    have htop : (⊤ : Subgroup K) = ⊥ := le_bot_iff.mp (le_trans (by
      intro x _
      exact mem_centralizer_iff.mpr (fun y hy => by
        have hy1 : y = 1 := hy
        simp only [hy1,mul_one,one_mul])) hz)
    have hmap := congrArg (map K.subtype) htop
    rw [← MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] at hmap
    exact hK.ne_bot hmap
  let e : K ≃* B := K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  have hbcore : pCore 2 B ≠ ⊥ := by
    intro he
    have hh := pCore_map_iso 2 e
    rw [he] at hh
    exact hkcore ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  have hHN : c.H ≤ normalizer (B : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    simpa only [B,subgroupOf,comap_map_eq_self_of_injective c.H.subtype_injective] using hn
  obtain ⟨J,hJ,hNJ⟩ := exists_twoLocal_overgroup_normalizer B (pCore 2 B) hbcore pCore_isPGroup
  exact le_antisymm hHN (hNJ.trans (c.maximal.2 hJ (hHN.trans hNJ)))

/-- Only the quotient and full-normalizer identifications remain after the
aligned source selection and genuine containing-component theorem. -/
theorem exists_sourceConfiguration_of_component_identifications
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hidentify : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      K.IsCComponent → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      IsQuasisimple (K ⧸ pCore 2 K) ∧ c.H = normalizer (K.map c.H.subtype : Set G))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  apply exists_sourceConfiguration_of_component_selection D h hpsl ?_ hnot
  intro c
  obtain ⟨K,hK,hLK,hout,hn⟩ := c.exists_normal_escaping_component D h hpsl
  obtain ⟨hq,hNK⟩ := hidentify c K hK hLK hout hn
  exact ⟨K,hK,hq,hLK,hout,hn,hNK⟩

/-- Assembly separates the two remaining source deductions: the ordinary
normalizer equality and the constrained quasisimple quotient. -/
theorem exists_sourceConfiguration_of_component_branches
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hordinary : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hconstrained : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      K.IsCComponent → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      generalizedFitting K = pCore 2 K → IsQuasisimple (K ⧸ pCore 2 K))
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    Nonempty (SourceConfiguration T L) := by
  apply exists_sourceConfiguration_of_component_identifications D h hpsl ?_ hnot
  intro c K hK hLK hout hn
  rcases hK.component_or_generalizedFitting_eq_pCore (c.c28 D h).oddCore_eq_bot with ho | hf
  · exact ⟨c.component_quotient_of_ordinary D h K ho,hordinary c K ho hLK hout hn⟩
  · exact ⟨hconstrained c K hK hLK hout hn hf,c.component_normalizer_of_constrained K hK hn hf⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
