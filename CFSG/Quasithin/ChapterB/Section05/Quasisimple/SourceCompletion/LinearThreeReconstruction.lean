module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeFlag
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCommonActors
/-!
# Doubled-natural reconstruction in every reducible SL3 source action

On the larger-field component moved action, the genuine chief flag has two
natural factors and no central layers. The complete automorphism and field
transport theorem aligns their actual actor markings as equal or dual.
B.4.9 splits the literal extension and excludes its dual orientation.

All passage to the component action, local chief actor, source hypotheses,
faithfulness and quotient maps is proved on the original module. Degree one
uses the earlier checked central-attachment calculation. Thus every field
has an actual doubled-natural moved module. The proved Sylow-socle argument
then gives G=L and the original quadratic ratio equals one.

Source: Aschbacher--Smith B.5.1, printed p.101, SL3 case (a)--(c), with
B.4.8--9 and I.1.6. The exact full-axis offender iff is assembled separately.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Align and split the two actual large-field chief layers. -/
theorem linearThree_large_flag_double [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (hF : 1 < F.degree) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤) :
    ∃ E : BinaryField, IsRepeatedLinearNatural ρ E 3 2 := by
  obtain ⟨_,_,E,E',hN,hQ⟩ := linearThree_large_flag_layers ρ hK hsemisimple h36 earlier hsq hf hcore hp
    F hF mark f A hA hgen hm
  obtain ⟨a⟩ := hN
  let D : NaturalExtensions.DoubleNatural E 3 ρ :=
    ⟨hf,f.chain 1,a,linearThree_naturals_same_or_dual (f.chain 1).quotientRepresentation
      (f.chain 1).toRepresentation E' E hQ ⟨a⟩⟩
  exact ⟨E,doubleNatural_three_repeated ρ D ⟨A,hA.1.isOffender ρ⟩⟩

private theorem coinvariants_top_of_actionEquiv
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) H X} (e : ActionEquiv ρ σ)
    (hm : Coinvariants.ker ρ = ⊤) : Coinvariants.ker σ = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  have he : Coinvariants.ker ρ ≤ (Coinvariants.ker σ).comap e.linearEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    change e.linearEquiv (ρ g w - w) ∈ Coinvariants.ker σ
    rw [map_sub,e.intertwines]
    exact Coinvariants.sub_mem_ker (e.groupEquiv g) (e.linearEquiv w)
  exact he (hm ▸ Submodule.mem_top)

/-- The original large-field moved component action is doubled natural. -/
theorem linearThree_large_source_moved_double [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) (s : MovedSection ρ L)
    (F : BinaryField) (hF : 1 < F.degree) (mark : L ≃* SL(3,F.Carrier)) :
    ∃ E : BinaryField, IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) E 3 2 := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let δ := s.space.toRepresentation.comp L.subtype
  obtain ⟨hs,hm,hn⟩ := linearThree_component_moved_source ρ hK hsemisimple h36 earlier h hnot s F mark
  have hmoved : moved δ (⊤ : Subgroup L) = ⊤ := by
    rw [← coinvariants_eq_moved]
    have he : δ.comp (⊤ : Subgroup L).subtype =
        δ.comp (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom := rfl
    rw [he]
    exact coinvariants_top_of_actionEquiv δ
      ⟨(Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩ hm
  obtain ⟨A,hA,⟨f⟩⟩ := reducible_source_flag δ hs (by rwa [hmoved])
  let H := (⊤ : Subgroup L) ⊔ A
  let C := (⊤ : Subgroup L).subgroupOf H
  let σ := δ.comp H.subtype
  have hH : H = ⊤ := top_sup_eq A
  let : IsQuasisimple (⊤ : Subgroup L) := hs.quasisimple
  have hfit : generalizedFitting H = C :=
    IrreducibleBranch.local_generalizedFitting (⊤ : Subgroup L) A hs.fitting hs.twoCore
      (hA.1.1.2.isPGroup 2 A)
  let c : C ≃* L := (subgroupOfEquivOfLe (show (⊤ : Subgroup L) ≤ H from le_sup_left)).trans Subgroup.topEquiv
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv c.symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hsq : IsSQTK K (generalizedFitting H) := (IsSQTK.equiv
    ((MulEquiv.subgroupCongr hfit).trans c)).mpr h.sqtk
  have hcore : pCore 2 H = ⊥ := IrreducibleBranch.local_twoCore_eq_bot (⊤ : Subgroup L) H
    hs.fitting hs.twoCore le_sup_left
  have hp : IsPGroup 2 (H ⧸ generalizedFitting H) :=
    (IrreducibleBranch.local_quotient_isTwoGroup (⊤ : Subgroup L) A
      (hA.1.1.2.isPGroup 2 A)).of_equiv (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  let g : generalizedFitting H ≃* L := (MulEquiv.subgroupCongr hfit).trans c
  let e : ActionEquiv δ (σ.comp (generalizedFitting H).subtype) :=
    ⟨g.symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hmF := coinvariants_top_of_actionEquiv δ e hm
  have hAH : A ≤ H := le_sup_right
  have hmin : IsMinimalBestOffender σ (A.subgroupOf H) := by
    refine ⟨hA.1.subgroupOf δ hAH,?_⟩
    intro B hB hBA
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH]
    apply hA.2 _ (hB.map_subtype δ)
    refine ⟨(map_mono hBA.1).trans_eq (map_subgroupOf_eq_of_le hAH),?_⟩
    have hw := hBA.2
    rw [weight_comp_map δ H.subtype H.subtype_injective,
      weight_comp_map δ H.subtype H.subtype_injective,map_subgroupOf_eq_of_le hAH] at hw
    exact hw
  have hgen : generalizedFitting H ⊔ A.subgroupOf H = ⊤ := by
    rw [hfit]
    change (⊤ : Subgroup L).subgroupOf H ⊔ A.subgroupOf H = ⊤
    simp only [Subgroup.top_subgroupOf,top_sup_eq]
  obtain ⟨E,⟨a⟩⟩ := linearThree_large_flag_double σ hK hsemisimple h36 earlier hsq
    (hs.faithful.comp H.subtype_injective) hcore hp F hF (g.trans mark) f (A.subgroupOf H) hmin hgen hmF
  let b : L ≃* H := ((MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv).symm
  exact ⟨E,⟨⟨b.trans a.groupEquiv,a.linearEquiv,fun x v => a.intertwines (b x) v⟩⟩⟩

/-- The genuine reducible SL3 source is doubled natural in every field degree. -/
theorem linearThree_source_moved_double [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) (s : MovedSection ρ L)
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) :
    ∃ E : BinaryField, IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) E 3 2 := by
  by_cases hF : F.degree = 1
  · exact ⟨BinaryField.two,linearThree_degreeOne_source_moved_double ρ hK hsemisimple h36 earlier h hnot s F hF mark⟩
  · exact linearThree_large_source_moved_double ρ hK hsemisimple h36 earlier h hnot s F
      (by have hp := F.degree_pos; omega) mark

/-- Original G=L, ratio one and doubled coordinates, with all local source inputs discharged. -/
theorem linearThree_reducible_structure [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) (s : MovedSection ρ L)
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) :
    L = ⊤ ∧ quadraticRatio ρ = 1 ∧
      ∃ E : BinaryField, IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) E 3 2 := by
  obtain ⟨E,⟨a⟩⟩ := linearThree_source_moved_double ρ hK hsemisimple h36 earlier h hnot s F mark
  have hL := whole_of_repeatedThree_source ρ hK earlier h s E ⟨a⟩
  exact ⟨hL,doubleThree_source_ratio ρ h s hL E a,E,⟨a⟩⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
