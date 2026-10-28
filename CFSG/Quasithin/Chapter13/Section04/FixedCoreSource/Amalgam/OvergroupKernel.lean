module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentNormalizers
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentAction
public import Theory.GroupTheory.PCoreImage

/-!
# The original component in every local overgroup

The selected component is a Sylow-invariant maximal local component.
Every local overgroup of the original join lies in a maximal two-local,
so the genuine uniqueness theorem forces it to normalize that same
component. Its two-core therefore lies in the overgroup's two-core.

The larger omega-center span is two-reduced. Its component kernel is
bounded above by the already proved kernel on the original span, and
bounded below by the component two-core. The resulting equality identifies
the component image in the literal larger action quotient with C/O₂(C),
including the representative formula. No equality of the two omega spans
or overgroup supplement is assumed or asserted here.

Source: Aschbacher–Smith 13.4.7(2), printed p.902, first paragraph.
Source1332OneTwo remains an earlier source premise for final assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)

include h₀ D m h1332 hTA hTB eA eB hne hindexA hindexB hK

/-- Every local overgroup normalizes the same selected component. -/
theorem original_pair_component_overgroup_normal
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    Y ≤ normalizer (K.map (A ⊔ B).subtype : Set G) := by
  let C := K.map (A ⊔ B).subtype
  obtain ⟨_,_,hstar,hTC,_⟩ := original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun H _ _ => ChapterA.Section02.theoremA_knownSimple (G := H))
    (fun H _ _ => ChapterA.Section02.theoremC_knownSimple (G := H)) h₀.qtke T hstar
  have horb : componentOrbit C (T : Subgroup G) = C :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer C _ C le_rfl hTC)
      (le_componentOrbit C _)
  have hcore : pCore 2 Y ≠ ⊥ := by
    intro he
    exact hY.1 (by change (pCore 2 Y).map Y.subtype = ⊥; rw [he,Subgroup.map_bot])
  obtain ⟨M,hM,hYM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot Y hcore
  have hCM : C ⊔ (T : Subgroup G) ≤ M :=
    (sup_le (map_subtype_le K) (hTA.trans le_sup_left)).trans
      ((show A ⊔ B ≤ Y from hY.2).trans hYM)
  have hM' := hu.normalizer_unique M hM hCM
  change M = normalizer (componentOrbit C (T : Subgroup G) : Set G) at hM'
  rw [horb] at hM'
  exact hYM.trans_eq hM'

variable (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)

include hres

/-- Reducedness of the larger omega span preserves the exact component kernel. -/
theorem original_pair_overgroup_component_kernel
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    let C := K.map (A ⊔ B).subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z Y
    IsPReduced 2 (U.subgroupOf Y) ∧
      C.pCoreIn 2 ≤ Y.pCoreIn 2 ∧
      C ⊓ centralizer (U : Set G) = C.pCoreIn 2 := by
  let C := K.map (A ⊔ B).subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z Y
  have hXY : A ⊔ B ≤ Y := hY.2
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hXY
  have hCY : C ≤ Y := (map_subtype_le K).trans hXY
  have hYC := original_pair_component_overgroup_normal h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK Y hY
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hr : IsPReduced 2 (U.subgroupOf Y) := reduced_conjugateSpan_of_sylow_central
    T Y Z hTY (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    (fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
    (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (h₀.qtke.evenCharacteristic T) ⟨hY.1,hTY⟩))
  have hcore : C.pCoreIn 2 ≤ Y.pCoreIn 2 := pCoreIn_mono_of_normalizes hCY hYC
  refine ⟨hr,hcore,le_antisymm ?_ ?_⟩
  · exact (inf_le_inf_left C (centralizer_le (conjugateSpanBy_mono le_rfl hXY))).trans_eq
      (original_pair_component_action_kernel h₀ D m h1332
        hTA hTB eA eB hne hindexA hindexB hres K hK)
  · refine le_inf (pCoreIn_le 2 C) ?_
    intro c hc u hu
    obtain ⟨q,hq,rfl⟩ := hcore hc
    exact congrArg Subtype.val ((le_centralizer_iff.mp hr.le_centralizer_pCore) hq
      ⟨u,hUY hu⟩ hu)


/-- The component in the larger faithful-action quotient is the same literal
quotient C/O₂(C), with the representative map retained. -/
theorem original_pair_overgroup_component_quotient
    (Y : Subgroup G) (hY : Y ∈ Chapter1.HOver G ((A ⊔ B : Subgroup G) : Set G)) :
    let C := K.map (A ⊔ B).subtype
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y
    let N := centralizer (U.subgroupOf Y : Set Y)
    ∃ hN : N.Normal, let := hN
      let q := QuotientGroup.mk' N
      let f := q.comp (inclusion ((map_subtype_le K).trans (show A ⊔ B ≤ Y from hY.2)))
      ∃ e : (C ⧸ pCore 2 C) ≃* f.range,
        ∀ c : C, (e (QuotientGroup.mk' (pCore 2 C) c)).val = f c := by
  let C := K.map (A ⊔ B).subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z Y
  have hCY : C ≤ Y := (map_subtype_le K).trans hY.2
  have hTY : (T : Subgroup G) ≤ Y := (hTA.trans le_sup_left).trans hY.2
  have hUY : U ≤ Y := conjugateSpanBy_le
    (fun z hz => hTY ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) Y.le_normalizer
  obtain ⟨hr,_,hker⟩ := original_pair_overgroup_component_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK hres Y hY
  let := hr.normal
  let N := centralizer (U.subgroupOf Y : Set Y)
  let hN : N.Normal := inferInstance
  let := hN
  let q := QuotientGroup.mk' N
  let f := q.comp (inclusion hCY)
  have hk : f.ker = pCore 2 C := by
    have he : f.ker = (centralizer (U : Set G)).subgroupOf C := by
      ext c
      change q (inclusion hCY c) = 1 ↔ c.val ∈ centralizer (U : Set G)
      constructor
      · intro hc u hu
        have hcN := (QuotientGroup.eq_one_iff (N := N) (inclusion hCY c)).mp hc
        exact congrArg Subtype.val (hcN ⟨u,hUY hu⟩ hu)
      · intro hc
        apply (QuotientGroup.eq_one_iff (N := N) (inclusion hCY c)).mpr
        intro u hu
        exact Subtype.ext (hc u.val hu)
    rw [he]
    apply map_injective C.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm]
    exact hker
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  exact ⟨hN,e,fun _ => rfl⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
