module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry.ReverseIndex.Contained.Nonquadratic.Marking.Construction.Affine
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Pencils.Transport
/-!
# The simultaneous incident S₄ marking of the original source

Choose a common representative m₀ of the two incident cosets. Conjugation
by m₀ preserves the first core at 1 and represents the opposite actor at d.
The original flag conjugation and diagram involution then align these two
cores with the literal point and line cores. Restrict the original quotient
through the injective amalgam embedding and use the fixed affine S₄ marking.

The restriction retains its evaluation formula. The change from m₀ to d is
an inner automorphism of the original model parabolic, which supplies the
exact `CompatibleProjection` equation as well as both core-image equalities.

The restriction argument adapts the earlier proof in
`Structure/Core/Naturality/Movement/Source/Marking`, without importing that
branch. Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of
rank two* (1993), printed pp.905--907.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic
open MarkingConstruction
private theorem diagram_line : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
  rw [← pointParabolic_map_diagram, Subgroup.map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact diagram_involutive x
  rw [he, Subgroup.map_id]

private theorem model_orientation (t : SL) (j : Bool) : ∃ e : MulAut SL,
    pointParabolicSL.map e.toMonoidHom = modelParabolic t j ∧
    lineParabolicSL.map e.toMonoidHom = modelParabolic t (!j) := by
  cases j
  · exact ⟨MulAut.conj t, rfl, rfl⟩
  · refine ⟨MulAut.conj t * diagram, ?_, ?_⟩
    · change pointParabolicSL.map ((MulAut.conj t).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← Subgroup.map_map, pointParabolic_map_diagram]
      rfl
    · change lineParabolicSL.map ((MulAut.conj t).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← Subgroup.map_map, diagram_line]
      rfl

private theorem map_conj_comap {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup H) (g : G) :
    (A.comap f).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (f g)).toMonoidHom).comap f := by
  ext x
  simp only [mem_map_equiv, mem_comap]
  change f (g⁻¹ * x * g) ∈ A ↔ (f g)⁻¹ * f x * f g ∈ A
  simp only [map_mul, map_inv]

private theorem map_conj_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (g : G) :
    (A.map f).map (MulAut.conj (f g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map f := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

private theorem map_symm_comap {G H : Type*} [Group G] [Group H]
    (f : G →* H) (e : MulAut H) (A : Subgroup H) :
    (A.map e.toMonoidHom).comap f = A.comap (e.symm.toMonoidHom.comp f) := by
  ext x
  simp only [mem_comap, mem_map_equiv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- Restrict an onto quotient to the preimage of a model subgroup, retaining
its kernel and every subgroup image through an injective ambient embedding. -/
private theorem exists_restricted_marking {G H K : Type*} [Group G] [Group H] [Group K]
    (j : G →* H) (hj : Function.Injective j) (π : G →* K) (hπ : Function.Surjective π)
    (P : Subgroup K) (A : Subgroup H) (hA : A = (P.comap π).map j) :
    ∃ f : A →* P, Function.Surjective f ∧
      f.ker = (π.ker.map j).subgroupOf A ∧
      (∀ x : G, ∀ a : A, (a : H) = j x → (f a : K) = π x) ∧
      ∀ C : Subgroup K, C ≤ P →
        (((C.comap π).map j).subgroupOf A).map f = C.subgroupOf P := by
  let e : P.comap π ≃* A :=
    ((P.comap π).equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hA.symm)
  let q : P.comap π →* P := {
    toFun x := ⟨π x, x.property⟩
    map_one' := Subtype.ext (map_one π)
    map_mul' x y := Subtype.ext (map_mul π (x : G) (y : G)) }
  let f : A →* P := q.comp e.symm.toMonoidHom
  have hfe (x : P.comap π) : f (e x) = q x := by simp only [f, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := hπ y
    refine ⟨e ⟨x, ?_⟩, ?_⟩
    · change π x ∈ P
      rw [hx]
      exact y.property
    · rw [hfe]
      exact Subtype.ext hx
  · ext a
    obtain ⟨x, rfl⟩ := e.surjective a
    rw [MonoidHom.mem_ker, hfe]
    change q x = 1 ↔ j x ∈ π.ker.map j
    constructor
    · intro hx
      exact ⟨x, congrArg Subtype.val hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := hj hyx
      subst y
      exact Subtype.ext hy
  · intro x a ha
    obtain ⟨y, rfl⟩ := e.surjective a
    have hy : (y : G) = x := hj ha
    rw [hfe]
    exact congrArg π hy
  · intro C hCP
    ext c
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, hy, hyx⟩ := ha
      have hyx' : y = x := hj hyx
      subst y
      rw [hfe]
      exact hy
    · intro hc
      obtain ⟨x, hx⟩ := hπ c
      have hxc : π x ∈ C := hx.symm ▸ hc
      let xP : P.comap π := ⟨x, hCP hxc⟩
      refine ⟨e xP, ⟨x, hxc, rfl⟩, ?_⟩
      rw [hfe]
      exact Subtype.ext hx


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Incidence supplies one onto S₄ marking with the original projection,
the exact Q_alpha kernel, and both prescribed core images. -/
theorem exists_parabolicMarking (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) : Nonempty (ParabolicMarking source i d) := by
  obtain ⟨m₀, hm₀, hdm₀⟩ := (flagIncident_one_iff source i d).mp hd
  have hAm : localFlagActor source (!i) m₀ = localFlagActor source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagActor_right_mul source (!i) d (d⁻¹ * m₀) hdm₀
  have hKm : localFlagKernel source (!i) m₀ = localFlagKernel source (!i) d := by
    simpa only [mul_inv_cancel_left] using
      localFlagKernel_right_mul source (!i) d (d⁻¹ * m₀) hdm₀
  have hIm : localFlagKernel source i m₀ = flagKernel source i :=
    mem_normalizer_iff_map_conj_eq.mp
      (flagKernel_normalized source i (mem_map_of_mem (embedM R) hm₀))
  obtain ⟨e₀, hp₀, hl₀⟩ := model_orientation source.flag i
  let e : MulAut SL := MulAut.conj (source.projection m₀) * e₀
  have hp : pointParabolicSL.map e.toMonoidHom =
      (modelParabolic source.flag i).map (MulAut.conj (source.projection m₀)).toMonoidHom := by
    change pointParabolicSL.map
      ((MulAut.conj (source.projection m₀)).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← Subgroup.map_map, hp₀]
  have hl : lineParabolicSL.map e.toMonoidHom =
      (modelParabolic source.flag (!i)).map (MulAut.conj (source.projection m₀)).toMonoidHom := by
    change lineParabolicSL.map
      ((MulAut.conj (source.projection m₀)).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← Subgroup.map_map, hl₀]
  let π := e.symm.toMonoidHom.comp source.projection
  have hA : localFlagActor source (!i) d = (lineParabolicSL.comap π).map (embedM R) := by
    rw [← hAm]
    change (((modelParabolic source.flag (!i)).comap source.projection).map (embedM R)).map
      (MulAut.conj (embedM R m₀)).toMonoidHom = _
    rw [map_conj_map, map_conj_comap, ← hl, map_symm_comap]
  have hk (j : Bool) (C P : Subgroup SL) (hC : P.pCoreIn 2 = C)
      (hP : P.map e.toMonoidHom =
        (modelParabolic source.flag j).map (MulAut.conj (source.projection m₀)).toMonoidHom) :
      localFlagKernel source j m₀ = (C.comap π).map (embedM R) := by
    rw [Pencils.localFlagKernel_eq_matrix_preimage]
    change ((((modelParabolic source.flag j).pCoreIn 2).map
      (MulAut.conj (source.projection m₀)).toMonoidHom).comap source.projection).map _ = _
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj (source.projection m₀)).injective,
      ← hP, ← map_pCoreIn_of_injective 2 _ _ e.injective, hC, map_symm_comap]
  have hK : localFlagKernel source (!i) d = (lineV.comap π).map (embedM R) :=
    hKm.symm.trans (hk (!i) lineV lineParabolicSL MarkingConstruction.line_core hl)
  have hI : flagKernel source i = (pointV.comap π).map (embedM R) :=
    hIm.symm.trans (hk i pointV pointParabolicSL MarkedProduct.pointParabolic_core hp)
  have hQ : Q R (alpha R) = (π.ker.map (embedM R)) := by
    rw [Q_alpha R source.two_group source.core_le, ← source.projection_kernel]
    congr 1
    exact (MonoidHom.ker_comp_of_injective source.projection e.symm.toMonoidHom
      e.symm.injective).symm
  obtain ⟨f, hf, hker, heval, himage⟩ := exists_restricted_marking (embedM R) (embedM_injective R)
    π (e.symm.surjective.comp source.projection_surjective) lineParabolicSL _ hA
  let F := lineMarking.toMonoidHom.comp f
  have hcompat : CompatibleProjection source i d F := by
    let P := modelParabolic source.flag (!i)
    have hn : P.map (MulAut.conj (source.projection (d⁻¹ * m₀))).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hdm₀)
    have hc : (MulAut.conj (source.projection m₀)).toMonoidHom =
        (MulAut.conj (source.projection d)).toMonoidHom.comp
          (MulAut.conj (source.projection (d⁻¹ * m₀))).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change source.projection m₀ * x * (source.projection m₀)⁻¹ =
        source.projection d *
          (source.projection (d⁻¹ * m₀) * x * (source.projection (d⁻¹ * m₀))⁻¹) *
          (source.projection d)⁻¹
      simp only [map_mul, map_inv]
      group
    have hl' : lineParabolicSL.map e.toMonoidHom =
        P.map (MulAut.conj (source.projection d)).toMonoidHom := by
      rw [hl, hc, ← Subgroup.map_map, hn]
    let ep : P ≃* lineParabolicSL :=
      ((MulAut.conj (source.projection d)).subgroupMap P).trans
        ((MulEquiv.subgroupCongr hl'.symm).trans (e.subgroupMap lineParabolicSL).symm)
    refine ⟨ep.trans lineMarking, ?_⟩
    intro m a ha
    change lineMarking (f a) = lineMarking (ep (modelProjection source (!i) m))
    apply congrArg lineMarking
    apply Subtype.ext
    rw [heval _ a ha]
    change e.symm (source.projection (d * (m : M) * d⁻¹)) =
      e.symm (source.projection d * source.projection (m : M) * (source.projection d)⁻¹)
    simp only [map_mul, map_inv]
  refine ⟨{
    hom := F
    onto := lineMarking.surjective.comp hf
    kernel := ?_
    compatible := hcompat
    first_le := Incident.flagKernel_le_incidentActor source i d hd
    first_image := ?_
    opposite_image := ?_ }⟩
  · rw [MonoidHom.ker_comp_of_injective f lineMarking.toMonoidHom lineMarking.injective,
      hker, ← hQ]
  · change ((flagKernel source i).subgroupOf _).map (lineMarking.toMonoidHom.comp f) = _
    rw [← Subgroup.map_map, hI, himage pointV pointV_le_line, point_image]
  · change ((localFlagKernel source (!i) d).subgroupOf _).map
      (lineMarking.toMonoidHom.comp f) = _
    rw [← Subgroup.map_map, hK, himage lineV (by rw [← MarkingConstruction.line_core]; exact map_subtype_le _),
      line_image]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving.Nonquadratic
