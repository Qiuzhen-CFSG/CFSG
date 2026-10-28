module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.Recognition
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveRankOne
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension

/-!
# The actual local embedding in the original A₅ overcomponent

Restrict the original local C-component and its prescribed full Sylow to I,
then pass to the literal quotient I/O₂(I). The smaller image is proper:
otherwise adjoining the two-core, which lies in the Sylow, makes the local
join all of I and contradicts the strict inclusion L < I. Its two-core
quotient remains A₅. These are the exact local inputs to A.3.14.

The proved odd rank-one embedding rows force the image to be A₅, and hence
force the original moved layer into O₂(I). The quadratic row forces the
field order twenty-five; the prime row retains both source congruences.
Other carrier embedding rows are not asserted here.

Source: Aschbacher–Smith 10.2.1, printed p.743, and A.3.14(3), pp.49–50.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
open Chapter3.Section02 ChapterC ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original strict local component remains proper after quotienting by O₂(I). -/
theorem source_containing_component_local_sylow (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {I X : Subgroup G} (hLI : L < I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X) :
    ∃ S : Sylow 2 I,
      (S:Subgroup I).map I.subtype = ((T:Subgroup G)⊓normalizer (L:Set G))⊓I ∧
      (S:Subgroup I) ≤ normalizer (L.subgroupOf I : Set I) ∧
      L.subgroupOf I ∈ localCComponents S ∧
      (⊤ : Subgroup I).IsCComponent ∧
      (L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≠ ⊤ := by
  let R := (T:Subgroup G)⊓normalizer (L:Set G)
  let K := L.subgroupOf I
  obtain ⟨S,hSm,hn⟩ := source_containing_component_sylow hLI.le hIX hI hS
  have hSe : (S:Subgroup I) = R.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hSm,subgroupOf_map_subtype]
  have hlocal : L ∈ localCComponents R :=
    localCComponents_antitone inf_le_left D.maximal.1.1
  have hK : K ∈ localCComponents S := by
    rw [hSe]
    exact SourceEmbeddings.local_restrict hlocal hLI.le
  have htop : (⊤:Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.subgroupOf_of_le le_rfl hIX
  refine ⟨S,hSm,hn,hK,htop,?_⟩
  intro he
  have hsup : K ⊔ pCore 2 I = ⊤ := by
    simpa only [comap_map_eq,QuotientGroup.ker_mk',comap_top] using
      congrArg (comap (QuotientGroup.mk' (pCore 2 I))) he
  have hjoin : K ⊔ (S:Subgroup I) = ⊤ := top_unique
    (hsup ▸ sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) K)
  have hwhole : K.IsCComponent := by
    change (K.subgroupOf (K ⊔ (S:Subgroup I))).IsCComponent at hK
    rw [hjoin] at hK
    simpa only [map_subgroupOf_eq_of_le le_top] using
      hK.map_subtype (show (⊤:Subgroup I).IsSubnormal from .top)
  have heK : K = ⊤ := hwhole.eq_of_le htop le_top
  exact hLI.ne (le_antisymm hLI.le (subgroupOf_eq_top.mp heK))


/-- The exact quotient map and full Sylow retain the local condition and A₅ section. -/
theorem source_a5_overcomponent_quotient_local_embedding
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I X : Subgroup G} (hLI : L < I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X) :
    ∃ S : Sylow 2 I,
      (S:Subgroup I).map I.subtype = ((T:Subgroup G)⊓normalizer (L:Set G))⊓I ∧
      let q := QuotientGroup.mk' (pCore 2 I)
      let B := (L.subgroupOf I).map q
      let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
      B ∈ localCComponents Sbar ∧
      (Sbar:Subgroup (I ⧸ pCore 2 I)) ≤ normalizer (B:Set _) ∧
      (⊤:Subgroup (I ⧸ pCore 2 I)).IsCComponent ∧ B ≠ ⊤ ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨S,hSm,hn,hK,htop,hne⟩ := source_containing_component_local_sylow D hLI hIX hI hS
  let K := L.subgroupOf I
  let q := QuotientGroup.mk' (pCore 2 I)
  let : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  refine ⟨S,hSm,?_,?_,?_,hne,?_⟩
  · exact Chapter1.Section02.localCComponents_map_of_solvable_ker hK q
  · exact (map_mono hn).trans (le_normalizer_map q)
  · simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 I)
  · let k : K ≃* L := subgroupOfEquivOfLe hLI.le
    have hk : IsPGroup 2 (q.subgroupMap K).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    let d := (q.subgroupMap K).pCoreQuotientEquiv (q.subgroupMap_surjective K) hk
    exact ⟨d.symm.trans ((QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans e)⟩

/-- The smaller image has exactly the radical quotient required in A.3.14. -/
theorem source_a5_overcomponent_quotient_radical
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I X : Subgroup G} (hLI : L < I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X) :
    let B := (L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
    solvableRadical B = pCore 2 B ∧
      Nonempty ((B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨S,_,hl,_,_,_,⟨b⟩⟩ := source_a5_overcomponent_quotient_local_embedding D e hLI hIX hI hS
  let B := (L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  let := hl.perfect
  let d : B.subgroupOf (B ⊔ (Sbar:Subgroup _)) ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := b.isSimpleGroup
  have hr : solvableRadical B = pCore 2 B := PerfectCoreTwoExtension.radical_eq_core
  exact ⟨hr,⟨(QuotientGroup.quotientMulEquivOfEq hr).trans b⟩⟩

private theorem layer_contained_of_image_five
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    (hb : Nonempty ((L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≃*
      alternatingGroup (Fin 5))) :
    (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I := by
  rcases source_a5_overcomponent_layer_alternative D e hn hout hLI hIX hI hS with h | h
  · exact h.1
  · have hd := (blockU ((L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)))).card_subgroup_dvd_card
    rw [h.blockU_card,Nat.card_congr hb.some.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd

/-- The prime-field row kills the original layer and retains both exceptional congruences. -/
theorem source_a5_overcomponent_primePSL2
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L < I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 p) :
    Chapter1.Section02.A312ExceptionalPrime p ∧
    Nonempty ((L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≃*
      alternatingGroup (Fin 5)) ∧
    (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I := by
  obtain ⟨S,_,hl,_,hc,hne,_⟩ := source_a5_overcomponent_quotient_local_embedding D e hLI hIX hI hS
  obtain ⟨hprime,hb⟩ := SourceEmbeddings.proper_primePSL2_models
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))) hl hc le_top hne hp ho
    (hm.of_mulEquiv topEquiv)
  exact ⟨hprime,hb,layer_contained_of_image_five D e hn hout hLI.le hIX hI hS hb⟩

/-- The quadratic-field row is exactly PSL₂(25), with the original layer killed. -/
theorem source_a5_overcomponent_quadraticPSL2
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T:Subgroup G)≤normalizer (L:Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T:Subgroup G):Set G)≤D.maximalLocal)
    {I X : Subgroup G} (hLI : L < I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent)
    (hS : Chapter1.IsSylowIn 2 ((T:Subgroup G)⊓normalizer (L:Set G)) X)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (p^2)) :
    p = 5 ∧ Nonempty ((L.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) ≃*
      alternatingGroup (Fin 5)) ∧
    (blockU (L.subgroupOf I)).map (L.subgroupOf I).subtype ≤ pCore 2 I := by
  obtain ⟨S,_,hl,_,hc,hne,hsection⟩ := source_a5_overcomponent_quotient_local_embedding D e hLI hIX hI hS
  obtain ⟨hp5,hb⟩ := SourceEmbeddings.proper_quadraticPSL2_five_models
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))) hl hc le_top hne hp ho
    (hm.of_mulEquiv topEquiv) hsection
  exact ⟨hp5,hb,layer_contained_of_image_five D e hn hout hLI.le hIX hI hS hb⟩

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
