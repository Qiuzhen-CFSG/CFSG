module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherSymplecticMembership
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherSymplecticMarking

/-!
# The original constrained component has no higher symplectic core

The same C.2.7 input fixes the native parabolic marking. Both actual residuals
are original local-family members, with SL2 cores and nonshort action on the
literal reduced normalizer module. Original local placement puts both in MZ;
their native generation then contradicts the original outside condition.
The full core-to-normalizer-image kernel is killed only after proving that
the original symplectic core is centerless.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- The full original symplectic core is impossible at the selected C.2.7 component. -/
theorem PreparedChosenModule.raw_constrained_not_higher_symplectic_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hi : Input KnownSimple.IsKnownSimple (centralizer (Z1 : Set G))
      ((centralizer (Z1 : Set G) ⊓ Mc).pCoreIn 2)
      (centralizer (Z1 : Set G) ⊓ Mc) L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* Sp F) : False := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let qH := QuotientGroup.mk' C
  let I := (L.subgroupOf H).map qH
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect hL.2
  have houtM : ¬L ≤ M := by
    intro hLM
    exact hi.outside (le_inf hL.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hLM).trans
        (localModule_centralizer_le_partner T M hu)))
  obtain ⟨hr,_,_,_,_,_,_⟩ := h.raw_component_normalizer_source
    hG T hM hJ hu hZ hZne hL hi.quasisimple hi.fitting hi.outside houtM
  let := hr.elementary
  obtain ⟨f,ec,hval,hproj,hf,hec,hcentral,_⟩ :=
    h.raw_component_normalizer_quotient hG T hM hJ hu hZ hZne hL
      hi.quasisimple hi.fitting hi.outside houtM
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  have hm := raw_symplectic_core_marked_parabolic hi hfour e
  obtain ⟨e',hfam⟩ := h.raw_symplectic_core_residual_members hG T hu hZ hZne hL
    hi.quasisimple hF hn e hm
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Theory.GroupTheory.FixedElementary.map_center,EvenProjective.center_eq_bot,Subgroup.map_bot]
  have heci : Function.Injective ec := (MonoidHom.ker_eq_bot_iff ec).mp
    (bot_unique (hcentral.trans_eq hz))
  let ei := MulEquiv.ofBijective ec ⟨heci,hec⟩
  let eI : I ≃* Sp F := ei.symm.trans e'
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have heq : eI.toMonoidHom.comp f = q := by
    apply MonoidHom.ext
    intro x
    change e' (ei.symm (f x)) = e' (QuotientGroup.mk' (pCore 2 L) x)
    rw [←hproj x]
    exact congrArg e' (ei.symm_apply_apply _)
  have hqs : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkq : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hR : IsPGroup 2 R := T.isPGroup'.to_le
    (inf_le_left.trans (show S ≤ (T : Subgroup G) from inf_le_left))
  have hplace (P : Subgroup (Sp F))
      (hP : P ∈ ({pointParabolic,planeParabolic} : Set (Subgroup (Sp F)))) :
      let B := (P.comap q).map L.subtype
      (solvableResidual B).map B.subtype ≤ centralizer (Z1 : Set G) ⊓ Mc := by
    intro B
    let A := (solvableResidual B).map B.subtype
    have hA := hfam P hP
    let : Group.IsPerfect A := Chapter1.mem_L_isPerfect hA.2
    obtain ⟨hfitA,⟨er⟩⟩ := RawClassicalResidual.symplectic_data L q hqs hkq hF hn P hP
    let : IsSimpleGroup SL(2,F) := NaturalExtension.model_simple (by omega)
    let : IsSimpleGroup (A ⧸ pCore 2 A) := er.isSimpleGroup
    have hzA : center (A ⧸ pCore 2 A) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (A ⧸ pCore 2 A)) inferInstance with hzA | hzA
      · exact hzA
      · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hzA)).elim
    let hqa : IsQuasisimple (A ⧸ pCore 2 A) :=
      { simple := ((QuotientGroup.quotientMulEquivOfEq hzA).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hnot : ¬ChapterC.IsShort A := by
      intro hs
      have hh := RawClassicalResidual.symplectic_nonshort L R inf_le_right hR W I f hval eI hF hn P hP
      rw [heq] at hh
      exact hh (hs.of_mulEquiv
        ((solvableResidual B).equivMapOfInjective B.subtype B.subtype_injective).symm)
    exact h.raw_nonshort_slTwo_le_marked hG T hempty hM hJ hu hZ hZne hA hqa hfitA hnot F er
  let : Group.IsNilpotent q.ker := hkq.isNilpotent
  have hgen := congrArg (Subgroup.map L.subtype)
    (preimage_residuals_generate q hqs hF hn)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hgen
  rw [map_embedded_solvableResidual_of_hom,map_embedded_solvableResidual_of_hom] at hgen
  apply hi.outside
  rw [←hgen]
  exact sup_le (hplace _ (Or.inl rfl)) (hplace _ (Or.inr rfl))

end CFSG.Quasithin.Chapter15.Section01
