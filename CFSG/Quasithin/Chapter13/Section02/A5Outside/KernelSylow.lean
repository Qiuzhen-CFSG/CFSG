module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelCommutator
public import Theory.SpecificGroups.AlternatingFiveSylowLift
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental

/-!
# Constructing the source Sylow R=O₂(XT)

The solvable overlap H∩L has normal Sylow two-subgroup T∩L, by the actual
A₅ quotient. Its two-core is therefore T∩L and is normalized by H∩N(L).
For the original residual X≤H∩N(L), this puts T∩L in R=O₂(XT). The subgroup
R lies in T, is T-invariant, contains O₂(H) and V, and is Sylow in LR.
All quotient and subgroup inclusions retain their original ambient maps.

Source: Aschbacher–Smith 13.2.9, printed p. 880.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The original component Sylow is the literal intersection with T. -/
theorem source_component_sylow
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ T from le_sup_left) (sup_le L.le_normalizer d.normalizes_L)
  refine ⟨P,?_⟩
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)] using hP

/-- Solvability identifies the actual overlap core with the component Sylow. -/
theorem source_overlap_component_core
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hTH : (T : Subgroup G) ≤ H) (hs : Group.IsSolvable H) :
    (H ⊓ L).pCoreIn 2 = (T : Subgroup G) ⊓ L := by
  let := hs
  obtain ⟨P,hP⟩ := source_component_sylow d
  let J := H.subgroupOf L
  let j : J →* H := (L.subtype.comp J.subtype).codRestrict H (fun x => x.property)
  let : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
    (f := j) (by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : H => (x : G)) h)
  have hPJ : (P : Subgroup L) ≤ J := by
    intro p hp
    exact hTH ((hP ▸ mem_map_of_mem L.subtype hp).1)
  have hn := Theory.SpecificGroups.solvable_sylow_overgroup_normalizes_of_alternatingFive_quotient
    d.quotient P J hPJ
  have hn' : H ⊓ L ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [←hP]
    apply le_normalizer_iff.mpr
    intro j hj s hsp
    obtain ⟨p,hp,rfl⟩ := hsp
    exact mem_map_of_mem L.subtype (le_normalizer_iff.mp hn ⟨j,hj.2⟩ hj.1 p hp)
  have hSH : (T : Subgroup G) ⊓ L ≤ H ⊓ L := inf_le_inf hTH le_rfl
  obtain ⟨S,hS⟩ := P.exists_map_subtype_eq_of_le
    (show H ⊓ L ≤ L from inf_le_right) (hP ▸ hSH)
  refine le_antisymm ?_ (le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le inf_le_left) hSH hn')
  exact (pCoreIn_le_sylow (H ⊓ L) S).trans_eq (hS.trans hP)

/-- The entire original overlap normalizes T∩L. -/
theorem source_overlap_normalizes_component_sylow
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hTH : (T : Subgroup G) ≤ H) (hs : Group.IsSolvable H) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  rw [←source_overlap_component_core d hTH hs]
  exact ((le_inf (inf_le_left.trans H.le_normalizer) inf_le_right).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (H ⊓ L) (pCore 2 (H ⊓ L : Subgroup G)))


/-- The source R=O₂(XT) contains the component Sylow and is Sylow in LR. -/
theorem source_kernel_core_sylow
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H X : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hTH : (T : Subgroup G) ≤ H) (hs : Group.IsSolvable H)
    (hXH : X ≤ H) (hXM : X ≤ normalizer (L : Set G)) :
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    ((T : Subgroup G) ⊓ L) ≤ R ∧ R ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      H.pCoreIn 2 ≤ R ∧ V ≤ R ∧
      ∃ P : Sylow 2 (L ⊔ R : Subgroup G), (P : Subgroup (L ⊔ R : Subgroup G)).map
        (L ⊔ R).subtype = R := by
  let Y := X ⊔ (T : Subgroup G)
  let R := Y.pCoreIn 2
  have hYH : Y ≤ H := sup_le hXH hTH
  have hYM : Y ≤ normalizer (L : Set G) := sup_le hXM d.normalizes_L
  have hSN : Y ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf hYH hYM).trans (source_overlap_normalizes_component_sylow d hTH hs)
  have hSR : (T : Subgroup G) ⊓ L ≤ R := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le inf_le_left) (inf_le_left.trans le_sup_right) hSN
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow Y (T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ Y from le_sup_right)] using hh
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    ((show (T : Subgroup G) ≤ Y from le_sup_right).trans Y.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hQR : H.pCoreIn 2 ≤ R := by
    have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
      have hh := pCoreIn_le_sylow H (T.subtype hTH)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using hh
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hQT.trans le_sup_right)
      ((hYH.trans H.le_normalizer).trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hVR : V ≤ R := (le_inf d.chosen.le_sylow d.chosen.le_component).trans hSR
  obtain ⟨P,hP⟩ := source_component_sylow d
  refine ⟨hSR,hRT,hnR,hQR,hVR,?_⟩
  exact (isPGroup_pCoreIn 2 Y).exists_sylow_sup_of_coprime_index L R
    (hRT.trans d.normalizes_L) (P : Subgroup L) P.not_dvd_index (hP ▸ hSR)

/-- Literal residual-kernel application: R is constructed from C_H(U), with
its containment, invariance and Sylow properties derived from the source. -/
theorem source_residual_kernel_sylow_configuration
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    ((T : Subgroup G) ⊓ L) ≤ R ∧ R ≤ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧
      H.pCoreIn 2 ≤ R ∧ V ≤ R ∧
      ∃ P : Sylow 2 (L ⊔ R : Subgroup G), (P : Subgroup (L ⊔ R : Subgroup G)).map
        (L ⊔ R).subtype = R := by
  obtain ⟨hXH,hXM,_⟩ := source_kernel_residual_full_commutator d hH hB hZ hs hne
  exact source_kernel_core_sylow d hH.1.1.2 hs hXH hXM

end CFSG.Quasithin.Chapter13.Section02.A5Outside
