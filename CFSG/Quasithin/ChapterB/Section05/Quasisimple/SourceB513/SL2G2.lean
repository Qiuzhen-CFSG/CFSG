module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.SL2OrthogonalCover.DualRatio
public import Theory.Representation.G2OrthogonalCover.DualRatio
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# The SL₂ and G₂ natural-cover branches of B.5.13

The literal projection from the moved space to its central quotient is a
cover by Irr⁺. The quotient's action marking reindexes that same projection
onto the concrete natural model. The universal-cover root calculation gives
the dual bound, and the original component inclusion carries the same actor
back to the ambient group. Perfectness handles the full G₂ row; the binary
derived row retains G₂(2)′ literally. The SL₂ field-size exclusion is explicit.

The final source applications use the corrected B.5.1 conclusion and the
original representation's literal dual. Their fixed-supplement premise is
discharged by the B.5.13 assembly from clause (5); it is not asserted here.

Source: Aschbacher–Smith B.5.13, printed pp.110–112, and I.1.5–6 and I.2.3,
printed pp.408 and 413, combined manuscript (1 March 2004).
-/

public section

open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {D V : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {L : Subgroup D}
variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {τ : Representation (ZMod 2) E W}

private noncomputable def markedProjection (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) τ) :
    Representation.IntertwiningMap
      (s.space.toRepresentation.comp (L.subtype.comp e.groupEquiv.symm.toMonoidHom)) τ :=
  (e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    change e.linearEquiv ((s.action.comp L.subtype) (e.groupEquiv.symm g)
      (s.central.toSubmodule.mkQ v)) = _
    rw [e.intertwines, e.groupEquiv.apply_symm_apply]
    rfl)

omit [FiniteDimensional (ZMod 2) V] in
private theorem markedProjection_isCover (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) τ) :
    IsCover (markedProjection s e) := by
  refine ⟨e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _), ?_, ?_⟩
  · intro v hv g
    have hz : s.central.toSubmodule.mkQ v = 0 :=
      e.linearEquiv.injective (hv.trans (map_zero e.linearEquiv).symm)
    have hc := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hc
    exact hc (e.groupEquiv.symm g)
  · let σ := s.space.toRepresentation.comp (L.subtype.comp e.groupEquiv.symm.toMonoidHom)
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker σ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      refine ⟨σ (e.groupEquiv ⟨g,hg⟩) ⟨v,hv⟩ - ⟨v,hv⟩,
        Coinvariants.sub_mem_ker _ _, ?_⟩
      change ρ (e.groupEquiv.symm (e.groupEquiv ⟨g,hg⟩)) v - v = ρ g v - v
      rw [e.groupEquiv.symm_apply_apply]
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

omit [FiniteDimensional (ZMod 2) V] in
private theorem marked_dual_bound (s : MovedSection ρ L)
    (e : ActionEquiv (s.action.comp L.subtype) τ)
    (hq : quadraticRatio (Representation.dual
      (s.space.toRepresentation.comp (L.subtype.comp e.groupEquiv.symm.toMonoidHom))) ≤ 2) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  let f := L.subtype.comp e.groupEquiv.symm.toMonoidHom
  apply (quadraticRatio_le_of_injective_equivariant _ _
    f (L.subtype_injective.comp e.groupEquiv.symm.injective)
    (LinearEquiv.refl _ _) ?_).trans hq
  intro g v
  ext w
  change v (s.space.toRepresentation (f g⁻¹) w) =
    v (s.space.toRepresentation ((f g)⁻¹) w)
  rw [map_inv]

/-- The moved central cover of a marked SL₂ natural plane has dual ratio at most two. -/
theorem linearTwo_moved_dual_ratio_le_two (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (hn : IsLinearNatural (s.action.comp L.subtype) F 2) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  obtain ⟨e⟩ := hn
  apply marked_dual_bound s e
  exact Representation.SL2OrthogonalCover.cover_dual_quadraticRatio_le_two
    F.degree hF F.card_eq (markedProjection s e) (markedProjection_isCover s hi e)

/-- A marked derived G₂ natural central cover has the dual bound over every binary field. -/
theorem derivedG2_moved_dual_ratio_le_two (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (F : BinaryField)
    (hn : Nonempty (ActionEquiv (s.action.comp L.subtype)
      (Atlas.G2.Natural.OrthogonalCover.binaryNatural F.Carrier))) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  obtain ⟨e⟩ := hn
  apply marked_dual_bound s e
  exact Atlas.G2.Natural.OrthogonalCover.cover_dual_quadraticRatio_le_two
    F.Carrier (markedProjection s e) (markedProjection_isCover s hi e)

/-- A perfect actor in the full G₂ row uses its derived natural cover without changing the marking. -/
theorem g2_moved_dual_ratio_le_two [Group.IsPerfect L]
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (F : BinaryField) (hn : Nonempty (ActionEquiv (s.action.comp L.subtype) (binaryG2 F))) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  obtain ⟨e⟩ := hn
  let : Group.IsPerfect (Atlas.G2.Model F.Carrier) :=
    Group.IsPerfect.ofSurjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
  let k : Atlas.G2.Model F.Carrier ≃* commutator (Atlas.G2.Model F.Carrier) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm)
  let e' : ActionEquiv (s.action.comp L.subtype)
      (Atlas.G2.Natural.OrthogonalCover.binaryNatural F.Carrier) :=
    { groupEquiv := e.groupEquiv.trans k
      linearEquiv := e.linearEquiv
      intertwines := e.intertwines }
  exact derivedG2_moved_dual_ratio_le_two s hi F ⟨e'⟩

/-- The binary endpoint uses the actual G₂(2)′ action. -/
theorem derivedG2_two_moved_dual_ratio_le_two
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (hn : Nonempty (ActionEquiv (s.action.comp L.subtype) (g2DerivedNatural (ZMod 2)))) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  exact derivedG2_moved_dual_ratio_le_two s hi BinaryField.two hn


/-- The original dual moved cover and its fixed supplement yield the SL₂ branch. -/
theorem quadraticRatio_le_two_of_linearTwo_source_supplement [Finite D]
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField) (hF : 1 < F.degree)
    (he : IsLinearNatural (c.sectionData.action.comp L.subtype) F 2)
    (hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤) :
    quadraticRatio ρ ≤ 2 := by
  exact quadraticRatio_le_two_of_dual_fixed_supplement ρ c.sectionData.space hs
    (linearTwo_moved_dual_ratio_le_two c.sectionData (c.clause_two hn).1 F hF he)

/-- Perfectness retains the original full G₂ row while the root lies in its derived group. -/
theorem quadraticRatio_le_two_of_g2_source_supplement [Finite D] [Group.IsPerfect L]
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField)
    (he : Nonempty (ActionEquiv (c.sectionData.action.comp L.subtype) (binaryG2 F)))
    (hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤) :
    quadraticRatio ρ ≤ 2 := by
  exact quadraticRatio_le_two_of_dual_fixed_supplement ρ c.sectionData.space hs
    (g2_moved_dual_ratio_le_two c.sectionData (c.clause_two hn).1 F he)

/-- The binary derived G₂ row uses the literal derived natural module. -/
theorem quadraticRatio_le_two_of_derivedG2_source_supplement [Finite D]
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (he : Nonempty (ActionEquiv (c.sectionData.action.comp L.subtype)
      (g2DerivedNatural (ZMod 2))))
    (hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤) :
    quadraticRatio ρ ≤ 2 := by
  exact quadraticRatio_le_two_of_dual_fixed_supplement ρ c.sectionData.space hs
    (derivedG2_two_moved_dual_ratio_le_two c.sectionData (c.clause_two hn).1 he)

end CFSG.Quasithin.ChapterB.SourceB513
