module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelSource
public import CFSG.Quasithin.ChapterG.Section12.Conjugation
public import CFSG.Quasithin.ChapterG.Section12.ResidualModels
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.Representation.NormalComponentConstituents.CenterlessImage

/-!
# The nondegenerate exchanged constituent as a literal G.12 action

On the same constituent chosen by the original terminal source, take the
images of the normal component orbit H and its actor stabilizer Y = N_X(I).
The H-image is perfect, irreducible, normal in the generated image HY, and
is its embedded solvable residual. Under nondegeneracy and properness,
the full hyperplane-center action supplies the exact G.12.1 hypotheses.

The recognition theorem remains an explicit premise of the model-reduction
lemma. Centerlessness of a recognized image separately removes the central
kernel; centrality alone is never used as faithfulness. Neither recognition
nor the subsequent model exclusions is asserted by this module.

Source: Aschbacher--Smith G.10.15, printed p.363, and G.12.12, p.374.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

abbrev constituentLinearAction : (componentOrbit L ⊤) →* (I ≃ₗ[ZMod 2] I) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom

abbrev constituentStabilizer :=
  (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))

/-- The literal action of N_X(I) on I. -/
def constituentStabilizerAction : constituentStabilizer (F := F) (g := g) (I := I) →*
    (I ≃ₗ[ZMod 2] I) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
    ((stabilizerRepresentation F.terminalRepresentation I).asGroupHom.comp
      { toFun := fun y => ⟨((y : F.terminalDot (F.X g)) : F.TerminalHdot), y.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl })

abbrev constituentGeneratedImage : Subgroup (I ≃ₗ[ZMod 2] I) :=
  s.constituentLinearAction.range ⊔
    (constituentStabilizerAction (F := F) (g := g) (I := I)).range

include s

theorem constituentImage_irreducible :
    ChapterG.Section12.Irreducible s.constituentLinearAction.range := by
  intro U hU
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let J : Subrepresentation R.toRepresentation := ⟨U, fun a w hw =>
    hU _ ⟨a,rfl⟩ w hw⟩
  rcases s.irreducible.eq_bot_or_eq_top J with hb | ht
  · exact Or.inl (congrArg Subrepresentation.toSubmodule hb)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule ht)

theorem constituentGeneratedImage_preserves :
    s.constituentGeneratedImage ≤ ChapterG.Section12.formStabilizer (B.restrict I) := by
  apply sup_le
  · rintro _ ⟨a,rfl⟩ u w
    exact s.hypothesis.preserves a u w
  · rintro _ ⟨a,rfl⟩ u w
    exact s.hypothesis.preserves ((a : F.terminalDot (F.X g)) : F.TerminalHdot) u w

/-- The same nondegenerate constituent, with its literal H and Y images,
meets G.12.1's hypotheses. No classification alternative is assumed. -/
theorem nondegenerate_classification_inputs
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnd : (B.restrict I).Nondegenerate) :
    ∃ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i := by
  obtain ⟨hgeo,_,_,_⟩ := Recognition.source_terminal_exchanged_constituent_completion
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem hproper
  obtain ⟨x,hx,hop,hdis,hindex,i,hi0,hvi,hiW,hcenter⟩ := hgeo
  let S := pointSylow (F := F)
  have hnX := s.actor_sylow.2
  have haxis := s.hypothesis.exchanged_constituent_not_le_axis s.nonsolvable
    s.component s.moved S hnX
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected s.point_not_mem hproper
  let U := I ⊓ (B v).ker
  let W : Submodule (ZMod 2) I := ((B v).comp I.subtype).ker
  let j : W ≃ₗ[ZMod 2] U :=
    { toFun := fun w => ⟨w, w.val.property, w.property⟩
      invFun := fun w => ⟨⟨w,w.property.1⟩,w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let iw : W := j.symm i
  let Q := (constituentStabilizerAction (F := F) (g := g) (I := I)).range
  have hfull : BinaryTransvection.FullCenterAction Q.subtype W iw := by
    refine ⟨?_,?_,?_,?_⟩
    · intro hz
      exact hi0 (congrArg (fun z : I => (z : Additive F.Uhat)) hz)
    · rintro ⟨_,y,rfl⟩
      exact Subtype.ext (hcenter.fixes y)
    · rintro ⟨_,y,rfl⟩ w
      have hm := hcenter.displacement y (j w)
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
      exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc⟩
    · intro φ hφ
      obtain ⟨y,hy⟩ := hcenter.full (φ.comp j.symm.toLinearMap) hφ
      refine ⟨⟨_,y,rfl⟩,fun w => ?_⟩
      exact Subtype.ext (hy (j w))
  have hW : finrank (ZMod 2) W + 1 = finrank (ZMod 2) I := by
    apply Module.Dual.finrank_ker_add_one_of_ne_zero
    intro hz
    apply haxis
    intro w hw
    have he := LinearMap.congr_fun hz (⟨w,hw⟩ : I)
    exact he
  have halt : (B.restrict I).IsAlt := fun w => s.hypothesis.alternating w
  have hpres := s.constituentGeneratedImage_preserves
  have hperp : W = ((B.restrict I) (iw : I)).ker :=
    hfull.hyperplane_eq_orthogonal (B.restrict I) halt hnd
      (fun q => hpres ((show Q ≤ s.constituentGeneratedImage from le_sup_right) q.property))
      hW s.dimension_gt_two
  have hgood := ChapterG.Section12.goodVector_of_fullCenterAction halt hpres
    (show Q ≤ s.constituentGeneratedImage from le_sup_right) hfull hperp
  have hWne : W ≠ ⊤ := by
    intro he
    rw [he,finrank_top] at hW
    omega
  obtain ⟨a,ha,haW⟩ := s.constituentImage_irreducible.exists_outside hWne hfull.nonzero
  have hpair : (B.restrict I) (a iw) iw ≠ 0 := by
    intro hz
    exact haW (hperp.ge (halt.eq_iff.mp hz))
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I) halt hnd
  have hd := s.dimension_gt_two
  exact ⟨a iw,iw,halt,hnd,hpres,by omega,
    hgood.conjugate hpres ((show s.constituentLinearAction.range ≤ s.constituentGeneratedImage
      from le_sup_left) ha),hgood,hpair⟩


/-- The normal component orbit has perfect image on the same constituent. -/
theorem constituentImage_perfect : Group.IsPerfect s.constituentLinearAction.range := by
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  exact Group.IsPerfect.ofSurjective (f := s.constituentLinearAction.rangeRestrict)
    s.constituentLinearAction.rangeRestrict_surjective

/-- Relative normality in the generated action image, not in all GL(I). -/
theorem constituentImage_normal :
    (s.constituentLinearAction.range.subgroupOf s.constituentGeneratedImage).Normal := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let N := subspaceStabilizer F.terminalRepresentation I
  let a : N →* (I ≃ₗ[ZMod 2] I) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
      (stabilizerRepresentation F.terminalRepresentation I).asGroupHom
  have hK : s.constituentLinearAction.range = (H.subgroupOf N).map a := by
    ext k
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨⟨h,s.selected.invariant h.property⟩,h.property,rfl⟩
    · rintro ⟨h,hh,he⟩
      exact ⟨⟨h,hh⟩,he⟩
  have hQ : (constituentStabilizerAction (F := F) (g := g) (I := I)).range ≤
      (⊤ : Subgroup N).map a := by
    rintro k ⟨y,rfl⟩
    exact ⟨⟨((y : F.terminalDot (F.X g)) : F.TerminalHdot),y.property⟩,mem_top _,rfl⟩
  have hn : (constituentStabilizerAction (F := F) (g := g) (I := I)).range ≤
      normalizer (s.constituentLinearAction.range : Set (I ≃ₗ[ZMod 2] I)) := by
    rw [hK]
    exact hQ.trans (by
      rw [← (H.subgroupOf N).normalizer_eq_top]
      exact Subgroup.le_normalizer_map a)
  exact normal_subgroupOf_of_le_normalizer
    (sup_le s.constituentLinearAction.range.le_normalizer hn)

/-- HY has the literal H-image as its embedded solvable residual. -/
theorem constituentGeneratedImage_residual :
    ChapterG.Section12.embeddedResidual s.constituentGeneratedImage =
      s.constituentLinearAction.range := by
  let K := s.constituentLinearAction.range
  let Q := (constituentStabilizerAction (F := F) (g := g) (I := I)).range
  let D := s.constituentGeneratedImage
  let Y := constituentStabilizer (F := F) (g := g) (I := I)
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  have hp : IsPGroup 2 Q := (IsElementaryAbelian.isPGroup 2 Y).of_surjective
    (constituentStabilizerAction (F := F) (g := g) (I := I)).rangeRestrict
    (constituentStabilizerAction (F := F) (g := g) (I := I)).rangeRestrict_surjective
  let : Group.IsPerfect K := s.constituentImage_perfect
  let : (K.subgroupOf D).Normal := s.constituentImage_normal
  let : Group.IsPerfect (K.subgroupOf D) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ D from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ D from le_sup_left)).symm.surjective
  have hgen : K.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ D from le_sup_left),
      map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right),
      ← MonoidHom.range_eq_map,range_subtype]
  change (solvableResidual D).map D.subtype = K
  rw [(residuals_of_perfect_normal_sup_twoGroup (K.subgroupOf D)
    (Q.subgroupOf D) hp.comap_subtype hgen).2,
    map_subgroupOf_eq_of_le (show K ≤ D from le_sup_left)]

/-- The G.12 recognition input is applied to the actual generated image;
the perfect normal image is its literal residual. -/
theorem nondegenerate_models_of_recognition
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hnd : (B.restrict I).Nondegenerate)
    (hrecognition : ∀ u i : I, ChapterG.Section12.ClassificationHypotheses
      s.constituentGeneratedImage (B.restrict I) u i →
      ChapterG.Section12.ResidualModel
        (ChapterG.Section12.embeddedResidual s.constituentGeneratedImage) (B.restrict I)) :
    ChapterG.Section12.ResidualModel s.constituentLinearAction.range (B.restrict I) := by
  obtain ⟨u,i,h⟩ := s.nondegenerate_classification_inputs hproper hnd
  have hm := hrecognition u i h
  rwa [s.constituentGeneratedImage_residual] at hm

/-- Centerlessness of the actual constituent image discharges the full
central kernel. In particular there is no unexplained quotient invariance
assumption in the later automorphism argument. -/
theorem faithful_of_constituentImage_centerless
    (hc : center s.constituentLinearAction.range = ⊥) :
    Function.Injective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  exact faithful_constituent_of_centerless_image F.terminalRepresentation s.hypothesis.faithful
    (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) (componentOrbit L ⊤) I
    s.selected.invariant (s.selected.isIrrPlus.ne_bot F.terminalRepresentation) hc s.central_kernel


/-- The literal faithful Y-action supplied by properness is the action used
in the generated linear image. -/
theorem constituentStabilizerAction_injective
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom) :
    Function.Injective (constituentStabilizerAction (F := F) (g := g) (I := I)) := by
  obtain ⟨_,_,hfaith,_⟩ := Recognition.source_terminal_exchanged_constituent_completion
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem hproper
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro y hy
  apply mem_bot.mpr
  apply hfaith y
  intro u
  exact congrArg (fun a : I ≃ₗ[ZMod 2] I => (a u : Additive F.Uhat)) hy

/-- A centerless recognized image cannot have its natural module fixed by all
its automorphisms. The conjugating element and intertwiner use the literal
constituent action; no invariance of a nontrivial kernel is presumed. -/
theorem not_imageAutomorphismsLinear_of_constituentImage_centerless
    (hproper : ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom)
    (hc : center s.constituentLinearAction.range = ⊥) :
    ¬ ImageAutomorphismsLinear s.constituentLinearAction.range := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  obtain ⟨hgeo,_,_,_⟩ := Recognition.source_terminal_exchanged_constituent_completion
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem hproper
  obtain ⟨x,hx,_⟩ := hgeo
  have hxinv : (x : F.TerminalHdot)⁻¹ = x :=
    inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (x : F.TerminalHdot) x.property)
  exact s.selected.not_imageAutomorphismsLinear F.terminalRepresentation
    s.fixedSpace_eq_bot (s.faithful_of_constituentImage_centerless hc) x (by rwa [hxinv])

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
