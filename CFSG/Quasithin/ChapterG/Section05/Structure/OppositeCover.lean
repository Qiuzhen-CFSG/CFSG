module

public import CFSG.Quasithin.ChapterG.Section05.Structure.Defs
public import Theory.Representation.BinaryDuadStructure.Universal
public import Theory.Representation.BinaryDuadStructure.OppositeCover.Geometry

/-!
# The marked opposite natural cover on D/C

Send a syntheme to the class of its line complement in the literal middle
quotient. The sum through each point is a perpendicular complement and hence
vanishes modulo C. Pentad duality turns these into the usual point–line
relations, giving a surjective map from the five-dimensional line quotient.
Both spaces have dimension five, so this is an isomorphism intertwining the
original middle action with the automorphic twist of the known natural cover.

Transport of the projection supplies the equivariant perfect central cover.
Its quotient action is the catalogue's opposite polar action, whose actual
aligned automorphism exchanges G₁ and G₂; irreducibility, inequivalence and
self-duality provide all fields of `middleCoverData`. The explicit generator
formula retains the natural-module identification. The parent radical argument
separately identifies D and C with the required radical powers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.3(5),
printed pp.343–345 (PDF pp.354–356).
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryAlternatingSix BinaryDuadModule BinaryPermutation

namespace CFSG.Quasithin.ChapterG.Section05.Structure
open BinaryDuadStructure BinaryDuadStructure.OppositeCover

private def lineElement (s : Syntheme) : lineComplementSpan :=
  ⟨lineComplement s, Submodule.subset_span (Set.mem_range_self s)⟩

noncomputable def middleClass (s : Syntheme) : MiddleQuotient :=
  MiddleRelations.mkQ ⟨lineComplement s, Submodule.subset_span (Set.mem_range_self s)⟩

private lemma lineElement_span :
    Submodule.span (ZMod 2) (Set.range lineElement) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff _ _).mpr rfl

lemma middleClass_span : Submodule.span (ZMod 2) (Set.range middleClass) = ⊤ := by
  change Submodule.span (ZMod 2) (Set.range (MiddleRelations.mkQ ∘ lineElement)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, lineElement_span, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

lemma middleClass_relation (s : Syntheme) :
    ∑ d ∈ Finset.univ.filter (fun d => incident d s), middleClass (linePoint.symm d) = 0 := by
  change (∑ d ∈ Finset.univ.filter (fun d => incident d s),
    MiddleRelations.mkQ (lineElement (linePoint.symm d))) = 0
  rw [← map_sum]
  apply (Submodule.Quotient.mk_eq_zero MiddleRelations).mpr
  change (∑ d ∈ Finset.univ.filter (fun d => incident d s),
    (lineElement (linePoint.symm d) : lineComplementSpan)) ∈
      naturalSubmodule.toSubmodule.comap lineComplementSpan.subtype
  change lineComplementSpan.subtype (∑ d ∈ Finset.univ.filter (fun d => incident d s),
    lineElement (linePoint.symm d)) ∈ naturalSubmodule
  rw [map_sum]
  change (∑ d ∈ Finset.univ.filter (fun d => incident d s),
    lineComplement (linePoint.symm d)) ∈ naturalSubmodule
  rw [sum_lineComplements_dual]
  exact ⟨(polarVector (dualLine s)).val, rfl⟩

private lemma pointAction_line (g : S6) (s : Syntheme) :
    pointAction g (lineComplement s) = lineComplement (synthemeAct g s) := by
  ext d
  have he := incident_act_iff g (g⁻¹ • d) s
  rw [smul_inv_smul] at he
  change (if incident (g⁻¹ • d) s then (0 : ZMod 2) else 1) =
    if incident d (synthemeAct g s) then 0 else 1
  simp only [he]

lemma middleClass_equivariant (g : G) (s : Syntheme) :
    middleClass (synthemeAct g.val s) = middleAction g (middleClass s) := by
  change MiddleRelations.mkQ (lineElement (synthemeAct g.val s)) =
    MiddleRelations.mkQ (BinaryDuadModule.lineComplementSubrepresentation.toRepresentation g
      (lineElement s))
  congr 1
  apply Subtype.ext
  exact (pointAction_line g.val s).symm

private lemma configuration_equivariant (g : G) (d : Duad) :
    middleClass (linePoint.symm (g • d)) =
      middleAction (alternatingDiagramAut.symm g) (middleClass (linePoint.symm d)) := by
  rw [← middleClass_equivariant]
  congr 1
  apply linePoint.injective
  rw [linePoint.apply_symm_apply, linePoint_equivariant, linePoint.apply_symm_apply]
  have he : diagramAut (alternatingDiagramAut.symm g).val = g.val :=
    congrArg Subtype.val (alternatingDiagramAut.apply_symm_apply g)
  rw [he]
  rfl

/-- Send each point generator of the ordinary cover to its dual line complement. -/
noncomputable def dualIncidenceMap : LineQuotient →ₗ[ZMod 2] MiddleQuotient :=
  lineQuotientLift (fun d => middleClass (linePoint.symm d)) middleClass_relation

lemma dualIncidenceMap_surjective : Function.Surjective dualIncidenceMap := by
  apply lineQuotientLift_surjective
  have he : Set.range (fun d => middleClass (linePoint.symm d)) = Set.range middleClass :=
    by simpa only [Function.comp_def] using linePoint.symm.surjective.range_comp middleClass
  rw [he]
  exact middleClass_span

lemma dualIncidenceMap_equivariant (g : G) (q : LineQuotient) :
    dualIncidenceMap (lineQuotientAction (alternatingDiagramAut g) q) =
      middleAction g (dualIncidenceMap q) := by
  have he := lineQuotientLift_equivariant
    (middleAction.comp alternatingDiagramAut.symm.toMonoidHom)
    (fun d => middleClass (linePoint.symm d)) middleClass_relation
    configuration_equivariant (alternatingDiagramAut g) q
  simpa only [dualIncidenceMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using he

noncomputable def dualIncidenceEquiv : LineQuotient ≃ₗ[ZMod 2] MiddleQuotient :=
  LinearEquiv.ofBijective dualIncidenceMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (lineQuotient_finrank.trans middleQuotient_finrank.symm)).mpr dualIncidenceMap_surjective,
      dualIncidenceMap_surjective⟩

lemma dualIncidenceEquiv_symm_equivariant (g : G) (q : MiddleQuotient) :
    dualIncidenceEquiv.symm (middleAction g q) =
      lineQuotientAction (alternatingDiagramAut g) (dualIncidenceEquiv.symm q) := by
  apply dualIncidenceEquiv.injective
  rw [dualIncidenceEquiv.apply_symm_apply]
  change _ = dualIncidenceMap (lineQuotientAction _ _)
  rw [dualIncidenceMap_equivariant]
  exact congrArg (middleAction g) (dualIncidenceEquiv.apply_symm_apply q).symm

noncomputable def oppositeProjection : middleAction.IntertwiningMap secondAlternating :=
  (naturalProjection.comp dualIncidenceEquiv.symm.toLinearMap).intertwiningMap_of_isIntertwiningMap
    _ _ (by
      intro g q
      change naturalProjection (dualIncidenceEquiv.symm (middleAction g q)) =
        secondAlternating g (naturalProjection (dualIncidenceEquiv.symm q))
      rw [dualIncidenceEquiv_symm_equivariant, naturalProjection_equivariant]
      rfl)

lemma middleAction_generated : Representation.Coinvariants.ker middleAction = ⊤ := by
  let C := Representation.Coinvariants.ker middleAction
  have he : Representation.Coinvariants.ker lineQuotientAction ≤
      C.comap dualIncidenceMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, q⟩, rfl⟩
    change dualIncidenceMap (lineQuotientAction g q - q) ∈ C
    rw [map_sub]
    have hg : g = alternatingDiagramAut (alternatingDiagramAut.symm g) :=
      (alternatingDiagramAut.apply_symm_apply g).symm
    rw [hg, dualIncidenceMap_equivariant]
    exact Representation.Coinvariants.sub_mem_ker _ _
  rw [lineQuotient_generated] at he
  apply top_unique
  intro q _
  obtain ⟨u, rfl⟩ := dualIncidenceMap_surjective q
  exact he Submodule.mem_top

lemma oppositeProjection_isCover : Representation.OneCohomology.IsCover oppositeProjection := by
  refine ⟨naturalProjection_surjective.comp dualIncidenceEquiv.symm.surjective, ?_,
    middleAction_generated⟩
  intro q hq g
  apply dualIncidenceEquiv.symm.injective
  rw [dualIncidenceEquiv_symm_equivariant]
  exact naturalProjection_ker_fixed hq (alternatingDiagramAut g)

lemma oppositeProjection_middleClass (s : Syntheme) :
    oppositeProjection (middleClass s) = (polarVector (linePoint s)).val := by
  have he : dualIncidenceEquiv (pointClass (linePoint s)) = middleClass s := by
    change lineQuotientLift (fun d => middleClass (linePoint.symm d))
      middleClass_relation (pointClass (linePoint s)) = _
    rw [lineQuotientLift_point, linePoint.symm_apply_apply]
  change naturalProjection (dualIncidenceEquiv.symm (middleClass s)) = _
  rw [← he, dualIncidenceEquiv.symm_apply_apply]
  exact pointSum_single _

/-- The marked middle section is the perfect central five-dimensional cover of 4₂. -/
noncomputable def middleCoverData : MiddleCoverData where
  oppositeAction := secondAlternating
  irreducible := secondAlternating_irreducible
  selfDual := ⟨secondSelfDual⟩
  distinct := fun ⟨e⟩ => natural_inequivalent.false e
  projection := oppositeProjection
  isCover := oppositeProjection_isCover

/-- The action in the cover witness is the polar action pulled back along the
actual exceptional automorphism exchanging the two specified parabolics. -/
lemma middleCoverData_oppositeAction (g : G) (v : NaturalModule) :
    middleCoverData.oppositeAction g v = naturalAction (alternatingDiagramAut g) v := rfl

lemma middle_quotient_is_five_dimensional_cover :
    Module.finrank (ZMod 2) MiddleQuotient = 5 ∧
      Representation.OneCohomology.IsCover oppositeProjection :=
  ⟨middleQuotient_finrank, oppositeProjection_isCover⟩

end CFSG.Quasithin.ChapterG.Section05.Structure
