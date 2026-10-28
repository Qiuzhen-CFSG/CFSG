module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramLocal
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCoreSelection
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramCoreReduction
public import CFSG.Quasithin.Chapter14.Section02.SelectedComponentPlacement
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Ambient selected residual with maximal two-core control

This consumer applies the literal H-source selector to the original
ambient diagram branch. It transports the residual geometry to G and
combines the two-core actor calculation with the source Sylow containment.
The resulting conclusion keeps the only genuine small-field alternative
explicit: either the original O₂(M) lies in the selected normalizer, or
f=2.

Source: Aschbacher--Smith 14.2.8(3), 14.2.12, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_diagram_ambient_core_residual_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hn : 1 < generationParameter H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : DiagramModel ((H ⊓ M).subgroupOf H) K (T.subtype hH.1.1.2 : Subgroup H) f) :
    ∃ L : Subgroup G, L ≤ K.map H.subtype ∧ Group.IsPerfect L ∧ ¬L ≤ M ∧
      L ⊔ (T : Subgroup G) = H ∧
      let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
      S.relIndex (T : Subgroup G) = 2 ∧ Chapter1.IsSylowIn 2 (S ⊓ L) L ∧
      H.pCoreIn 2 ≤ S ∧ Chapter1.IsSylowIn 2 S (L ⊔ S) ∧
      (L.subgroupOf (L ⊔ S)).IsCComponent ∧ L ∈ Chapter1.L G S ∧
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^f) ∧
      ChapterF.Source.IsRankOneModel (L ⧸ pCore 2 L) ∧
      (M.pCoreIn 2 ≤ S ∨ f = 2) := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let TH := T.subtype hTH
  obtain ⟨_,hP,hN,_,_,_⟩ :=
    source_lemma_14_2_2_8_minimal hG T hempty hM hu hmany hcard e H hH
  have hmax : (H ⊓ M).subgroupOf H = ChapterB.minimalParabolicMax TH hP :=
    ChapterB.minimalParabolicMax_unique TH hP hN (fun x hx => ⟨x.property,hM.1.2 hx⟩)
  have hs : ¬Group.IsSolvable H := by
    intro hs
    let := hs
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨L,hLK,hperf,hout,hLT,hi,hSyl,hcore,hMcore,F,hF,hfin,hchar,hcardF,⟨eF⟩⟩ :=
    source_diagram_core_residual_selection TH hP hs K hK hqK hgen hf (hmax ▸ hm)
  have hlin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^f) :=
    ⟨F,hF,hfin,hcardF,⟨eF⟩⟩
  let A := L.map H.subtype
  let S := (T : Subgroup G) ⊓ normalizer (A : Set G)
  let R := (TH : Subgroup H) ⊓ normalizer (L : Set H)
  have hTmap : (TH : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTH
  have hRmap : R.map H.subtype = S := by
    have hc : (normalizer (A : Set G)).comap H.subtype = normalizer (L : Set H) := by
      rw [comap_normalizer_eq_of_le_range (map_le_range H.subtype L),
        comap_map_eq_self_of_injective H.subtype_injective]
    rw [show R = S.comap H.subtype by rw [comap_inf,hc]; rfl,
      map_comap_eq_self]
    exact (inf_le_left.trans hTH).trans_eq (range_subtype H).symm
  have hAS : Chapter1.IsSylowIn 2 (S ⊓ A) A := by
    have hh := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hSyl
    change Chapter1.IsSylowIn 2 ((R ⊓ L).map H.subtype) A at hh
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,hRmap] at hh
    exact hh
  have hSA : Chapter1.IsSylowIn 2 S (A ⊔ S) :=
    sylow_in_normalized_join A S inf_le_right (T.isPGroup'.to_le inf_le_left) hAS
  let d := (L.equivMapOfInjective H.subtype H.subtype_injective).symm
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hlinA : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2^f) := hlin.of_mulEquiv dq
  have hpA : Group.IsPerfect A := by
    let := hperf
    exact Group.IsPerfect.ofSurjective (f := d.symm.toMonoidHom) d.symm.surjective
  have hcA : (A.subgroupOf (A ⊔ S)).IsCComponent := by
    obtain ⟨F,hF,hfin,hq,⟨eF⟩⟩ := hlinA
    have h4 : 4 ≤ Nat.card F := by
      rw [hq]
      have hh : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at hh ⊢
      exact hh
    exact perfect_binary_rank_one_local_component A S inf_le_right hpA h4 eF
  have hcoreA : H.pCoreIn 2 ≤ S := by
    rw [← hRmap]
    exact map_mono hcore
  refine ⟨A,map_mono hLK,hpA,?_,?_,?_,hAS,hcoreA,hSA,hcA,?_,hlinA,
    ChapterF.Source.IsRankOneModel.linear f (by omega) hlinA,?_⟩
  · intro hAM
    apply hout
    rw [←hmax]
    intro x hx
    exact ⟨x.property,hAM (mem_map_of_mem H.subtype hx)⟩
  · have hh := congrArg (Subgroup.map H.subtype) hLT
    simpa only [Subgroup.map_sup,hTmap,←MonoidHom.range_eq_map,range_subtype] using hh
  · change S.relIndex (T : Subgroup G) = 2
    rw [←hRmap,←hTmap,relIndex_map_map_of_injective _ _ H.subtype_injective]
    exact hi
  · exact source_selected_mem_local T H A S hH.1.1 (map_subtype_le _) inf_le_left
      hSA hcA hcoreA
  · rcases hMcore with hMcore | hf2
    · left
      obtain ⟨hQT,hQ⟩ := shared_sylow_twoCore_le_overlap_core T M H hM.1.2 hTH
      have hn : (((H ⊓ M).subgroupOf H).pCoreIn 2).map H.subtype ≤
          normalizer (A : Set G) := by
        rw [hmax]
        exact (map_mono hMcore).trans (L.le_normalizer_map H.subtype)
      exact le_inf hQT (hQ.trans hn)
    · exact Or.inr hf2
end CFSG.Quasithin.Chapter14.Section02
