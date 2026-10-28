module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawParabolicPlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryParabolics
public import Theory.SpecificGroups.BinaryLinear.CoreParabolicPair
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.EndpointExtension
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryGeneration

/-! The original binary core map is bijective and cubic rank two forces
normalization by the original marked Sylow. The private graph-pair lift
retains the exact quotient marking and full two-core. The import-all edge
intentionally reuses only the record-free embedded_sylow_invariant helper. -/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- The actual central comparison to either binary linear model has no
kernel above the original two-core. -/
theorem PreparedChosenModule.raw_local_binary_linear_cover_bijective
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ≤ centralizer (Z1 : Set G)) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    {n : ℕ} (hn : n=4 ∨ n=5)
    (f : (L ⧸ pCore 2 L) →* SL(n,ZMod 2)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (L ⧸ pCore 2 L)) : Function.Bijective f := by
  let := hq
  rcases hn with rfl | rfl
  · let t : SL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
      Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm
    let c : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) (alternatingGroup (Fin 8)) :=
      ⟨t.toMonoidHom.comp f,t.surjective.comp hf,hq.toIsPerfect,by
        rw [MonoidHom.ker_comp_of_injective _ _ t.injective]; exact hk⟩
    let z := c.quotientCenterEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot)
    have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
      8 (by decide) (by decide) (by decide) z
    have hz : center (L ⧸ pCore 2 L) = ⊥ := by
      apply (eq_bot_iff_card _).mpr
      rcases h.raw_local_core_center_card hG T hZ hZne hL hq with hc | hc
      · exact hc
      · rw [hc] at hd
        norm_num at hd
    exact ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique (hk.trans hz.le)),hf⟩
  · let t := (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5)).symm
    let c : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) PSL(5,ZMod 2) :=
      ⟨t.toMonoidHom.comp f,t.surjective.comp hf,hq.toIsPerfect,by
        intro x hx
        exact hk (t.map_eq_one_iff.mp hx)⟩
    have hi := c.injective_of_universalProjection_ker_eq_bot
      (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot
        (ZMod 2) (by simp))
    exact ⟨fun _ _ hh => hi (congrArg t hh),hf⟩

/-- Native cubic rank two normalizes the same original local component. -/
theorem PreparedChosenModule.raw_binary_linear_sylow_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    {n : ℕ} (hn : n=4 ∨ n=5) (e : (L ⧸ pCore 2 L) ≃* SL(n,ZMod 2)) :
    ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (L : Set G) := by
  apply h.raw_local_normalizes_of_oddRank hG T hZ hZne hL hq Nat.prime_three (by decide)
  rw [primeRank_equiv 3 e]
  exact BinaryLinear.SmallCubicRank.four_or_five hn

namespace RawBinaryParabolic

private theorem graph_pair (L S : Subgroup G) (hnL : S ≤ normalizer (L : Set G))
    (Q : Sylow 2 L) (hQ : (Q : Subgroup L).map L.subtype = S ⊓ L)
    (hf : generalizedFitting L = pCore 2 L)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : (L ⧸ pCore 2 L) ≃* SL(m+1,ZMod 2))
    (b : Basis m)
    (hb : ((S ⊓ L).subgroupOf L).map (coreFlagMap L e) = cutStabilizer b Set.univ)
    (hctrl : ∀ P : Subgroup G, S ⊓ L ≤ P → P < L → S ≤ normalizer (P : Set G) →
      P = S ⊓ L ∨ P = EquivariantLift.lift L (coreFlagMap L e)
        (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}) ∨
      P = EquivariantLift.lift L (coreFlagMap L e)
        (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ)) :
    let C := EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1})
    let E := EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ)
    C < L ∧ E < L ∧ S ⊓ L ≤ C ∧ S ⊓ L ≤ E ∧
      S ≤ normalizer (C : Set G) ∧ S ≤ normalizer (E : Set G) ∧
      generalizedFitting C = pCore 2 C ∧ generalizedFitting E = pCore 2 E ∧
      Nonempty ((E ⧸ pCore 2 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      C ⊔ E = L := by
  obtain ⟨A,B,hgen,hA,hB,hQA,hQB,hAf,hBf,⟨eB⟩,himage,hinv⟩ :=
    BinaryLinear.InvariantNodeActions.exists_core_parabolic_pair hf (by omega) e Q
  let C := A.map L.subtype
  let E := B.map L.subtype
  have hCL : C < L := by
    apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hA
    apply map_injective L.subtype_injective
    simpa only [←MonoidHom.range_eq_map,range_subtype] using he
  have hEL : E < L := by
    apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hB
    apply map_injective L.subtype_injective
    simpa only [←MonoidHom.range_eq_map,range_subtype] using he
  have hSC : S ⊓ L ≤ C := hQ ▸ map_mono hQA
  have hSE : S ⊓ L ≤ E := hQ ▸ map_mono hQB
  have hnC := CaseIComponentData.embedded_sylow_invariant Q hQ hnL A (fun a ha => (hinv a ha).1)
  have hnE := CaseIComponentData.embedded_sylow_invariant Q hQ hnL B (fun a ha => (hinv a ha).2)
  have hCE : C ⊔ E = L := by
    have hh := congrArg (map L.subtype) hgen
    simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] using hh
  let aC := A.equivMapOfInjective L.subtype L.subtype_injective
  let aE := B.equivMapOfInjective L.subtype L.subtype_injective
  have hCf : generalizedFitting C = pCore 2 C := by
    rw [←map_generalizedFitting_equiv aC,←pCore_map_iso 2 aC,hAf]
  have hEf : generalizedFitting E = pCore 2 E := by
    rw [←map_generalizedFitting_equiv aE,←pCore_map_iso 2 aE,hBf]
  have heE : Nonempty ((E ⧸ pCore 2 E) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
    ⟨((QuotientGroup.congr _ _ aE (pCore_map_iso 2 aE)).symm.trans eB)⟩
  have hQS : (Q : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show S ⊓ L ≤ L from inf_le_right)]
    exact hQ
  let U := Q.mapSurjective (coreFlagMap_surjective L e)
  have hbU : (U : Subgroup (LinearGroup (m+1))) = cutStabilizer b Set.univ := by
    change (Q : Subgroup L).map (coreFlagMap L e) = _
    rw [hQS]
    exact hb
  have hCI : (C.subgroupOf L).map (coreFlagMap L e) =
      cutStabilizer b {i | i.val=0 ∨ i.val=m-1} := by
    rw [show C.subgroupOf L = A from comap_map_eq_self_of_injective L.subtype_injective A]
    exact himage.trans (by
      rw [centerIn_eq_map_center]
      exact sylow_center_centralizer_eq_endCuts (by omega) U b hbU)
  have hcore : (coreFlagMap L e).ker ≤ C.subgroupOf L := by
    rw [coreFlagMap_ker]
    exact (pCore_isPGroup.le_sylow_of_normal Q).trans
      (hQS ▸ subgroupOf_mono L hSC)
  have hc : C = EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}) := by
    have hh := EquivariantLift.lift_map_subgroupOf L (coreFlagMap L e) C hCL.le hcore
    rw [hCI] at hh
    exact hh.symm
  have hnot : ¬E ≤ C := fun he => hCL.ne ((sup_eq_left.mpr he).symm.trans hCE)
  have he : E = EquivariantLift.lift L (coreFlagMap L e)
      (cutStabilizer b {i | i.val=0 ∨ i.val=m-1}ᶜ) := by
    rcases hctrl E hSE hEL hnE with he | he | he
    · exact (hnot (he.symm ▸ hSC)).elim
    · exact (hnot (he.trans hc.symm).le).elim
    · exact he
  dsimp only
  rw [←hc,←he]
  exact ⟨hCL,hEL,hSC,hSE,hnC,hnE,hCf,hEf,heE,hCE⟩

end RawBinaryParabolic
end CFSG.Quasithin.Chapter15.Section01
