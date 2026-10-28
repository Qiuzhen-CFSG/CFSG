module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSecondarySelectionSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.Source
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentStructure

/-!
# Original secondary involution-centralizer component inputs

The distinguished involution in the single alternating-five case yields an
actual local pair and a Sylow subgroup of its centralizer. The original
central involution of the ambient Sylow therefore supplies the marked 1.1.5
hypotheses, and the source form of 2.3.9 applies to every ordinary component.
The moved elementary subgroup also kills the odd core and produces an
ordinary component when the centralizer is not of characteristic two.

Source: Aschbacher–Smith, the proof of 2.4.29, printed pp.545–546.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
variable (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
variable (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
variable (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
variable (hsingle : d.L0 = d.block)
variable (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
variable (u : G) (hu2 : orderOf u = 2)
variable (huR : u ∈ (center (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).map
  (elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)).subtype)
variable (hout : ¬ d.H ⊓ centralizer ({u} : Set G) ≤ M)
variable (hMu : M ⊓ centralizer ({u} : Set G) = (T : Subgroup G) ⊓ centralizer ({u} : Set G))
variable (hi : ((T : Subgroup G) ⊓ centralizer ({u} : Set G)).relIndex (T : Subgroup G) = 2)
variable (P : Sylow 2 (centralizer ({u} : Set G)))
variable (hP : (P : Subgroup (centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype =
  (T : Subgroup G) ⊓ centralizer ({u} : Set G))
variable (z : G) (hz : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
variable (hz2 : orderOf z = 2)

omit [Finite G] in
include hST huR hi hP in
private theorem secondary_sylow_control :
    let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let C := centralizer ({u} : Set G)
    R ≤ (P : Subgroup C).map C.subtype ∧
      (P : Subgroup C).map C.subtype < (T : Subgroup G) ∧
      (center (T : Subgroup G)).map (T : Subgroup G).subtype ≤ (P : Subgroup C).map C.subtype := by
  let R := elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  have hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype := sSup_le fun _ h => h.1
  have huT := hST.le (hRS (map_subtype_le _ huR))
  constructor
  · rw [hP]
    refine le_inf (hRS.trans hST.le) ?_
    obtain ⟨a,ha,he⟩ := huR
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨r,hr⟩)
  constructor
  · rw [hP]
    apply lt_of_le_of_ne inf_le_left
    intro hh
    have hj := hi
    rw [hh,relIndex_self] at hj
    omega
  · rw [hP]
    rintro x ⟨a,ha,rfl⟩
    refine ⟨a.property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (congrArg Subtype.val (mem_center_iff.mp ha ⟨u,huT⟩)).symm

include hG hM hTM hu hST hsingle hA hu2 huR hout hMu hi hP hz hz2 in
theorem MinimalBlockSetup.single_alternating_secondary_lemma115_of_marks :
    Chapter1.Lemma115Hypotheses (centralizer ({u} : Set G)) P M z := by
  obtain ⟨hp,hg,_⟩ := d.single_alternating_secondary_selection_of_marks hG T hM hTM hu hST
    hsingle hA u hu2 huR hout hMu hi
  obtain ⟨hRP,hPT,hZP⟩ := secondary_sylow_control d T hST u huR hi P hP
  have hcentral (s : G) (hs : s ∈ (P : Subgroup _).map (centralizer ({u} : Set G)).subtype) :
      s*z=z*s := by
    obtain ⟨a,ha,he⟩ := hz
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨s,hPT.le hs⟩)
  apply lemma_2_3_8_6 hG T hM hTM hu (Or.inr hg) hp P hRP hz2 (hZP hz) hcentral
  refine ⟨T.subtype hTM,?_⟩
  intro x hx
  have hxT : x ∈ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hx
  obtain ⟨a,ha,he⟩ := hz
  rw [←he]
  exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hxT⟩)

include hG hM hTM hu hST hsingle hA hu2 huR hout hMu hi hP hz hz2 in
noncomputable def MinimalBlockSetup.single_alternating_secondary_refinement_setup_of_marks
    (K : Subgroup (centralizer ({u} : Set G)))
    (hK : IsComponent (centralizer ({u} : Set G)) K) :
    ComponentRefinement.MathieuSourceSetup (centralizer ({u} : Set G))
      (K.map (centralizer ({u} : Set G)).subtype) M P z := by
  have hsel := d.single_alternating_secondary_selection_of_marks hG T hM hTM hu hST
    hsingle hA u hu2 huR hout hMu hi
  have hcontrol := secondary_sylow_control d T hST u huR hi P hP
  have hk : (K.map (centralizer ({u} : Set G)).subtype).subgroupOf (centralizer ({u} : Set G))=K :=
    comap_map_eq_self_of_injective (centralizer ({u} : Set G)).subtype_injective K
  exact ⟨T,hM,hTM,hu,Or.inr hsel.2.1,
    elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),
    d.H ⊓ centralizer ({u} : Set G),hsel.1,hcontrol.1,map_subtype_le _,hk.symm ▸ hK,
    hcontrol.2.1,hcontrol.2.2,hz,hz2⟩

include hG hM hTM hu hST hsingle hA hu2 huR hout hMu hi hP hz hz2 in
theorem MinimalBlockSetup.single_alternating_secondary_refinement_of_marks
    (K : Subgroup (centralizer ({u} : Set G)))
    (hK : IsComponent (centralizer ({u} : Set G)) K) :
    let A := K.map (centralizer ({u} : Set G)).subtype
    ComponentRefinement.RefinedIntersection A M
      ((P : Subgroup _).map (centralizer ({u} : Set G)).subtype) z ∨
      (Nat.card (pCore 2 A)=2 ∧ Nonempty ((A ⧸ pCore 2 A) ≃* Sporadic.Mathieu.M22) ∧
        IsCyclic (center (T : Subgroup G))) := by
  exact ((d.single_alternating_secondary_refinement_setup_of_marks hG T hM hTM hu hST
    hsingle hA u hu2 huR hout hMu hi P hP z hz hz2 K hK).source_refinement_or_binary_mathieu
      hG (fun _ _ _ => ChapterA.Section02.theoremsABC_knownSimple) localC129Input_knownSimple).2

include hG hM hTM hu hST hsingle hA hu2 huR hout hMu hi hP hz hz2 in
theorem MinimalBlockSetup.single_alternating_secondary_component_of_marks
    (L E : Subgroup (centralizer ({u} : Set G))) [IsElementaryAbelian 2 E]
    (hL : IsPPerfect 2 L) (hE : ⁅E,L⁆=E)
    (a : centralizer ({u} : Set G)) (ha : a ∈ E) (hza : z=(a:G)*u)
    (hf : generalizedFitting (centralizer ({u} : Set G)) ≠ pCore 2 (centralizer ({u} : Set G))) :
    pPrimeCore 2 (centralizer ({u} : Set G))=⊥ ∧
      ∃ K : Subgroup (centralizer ({u} : Set G)), IsComponent (centralizer ({u} : Set G)) K ∧
        K.map (centralizer ({u} : Set G)).subtype=⁅K.map (centralizer ({u} : Set G)).subtype,zpowers z⁆ ∧
        ¬ K.map (centralizer ({u} : Set G)).subtype ≤ M ∧
        HasModelAction115 K z := by
  exact DoubleA3.source_centralizer_component_catalogue hG u hu2 P M z
    (d.single_alternating_secondary_lemma115_of_marks hG T hM hTM hu hST
      hsingle hA u hu2 huR hout hMu hi P hP z hz hz2) L E hL hE a ha hza hf

end CFSG.Quasithin.Chapter2
