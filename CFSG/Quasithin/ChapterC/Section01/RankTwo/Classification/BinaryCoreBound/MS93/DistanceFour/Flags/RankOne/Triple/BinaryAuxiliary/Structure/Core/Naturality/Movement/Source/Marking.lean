module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Naturality.Movement.Source.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Pencils
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct

/-!
# The source parabolic marking with both incident cores

The original flag conjugation and the checked inverse-transpose diagram
transport the literal point/line parabolics to the source's two colors.
Restricting the original quotient to its parabolic preimage, then transporting
through the injective amalgam embedding, gives an onto marking with exact
kernel Q_alpha. The same construction identifies both cores: the actor's
core with the point translations and the first core with the incident line core.

All image and kernel identities refer to the original subgroups. No arbitrary
symmetric-group isomorphism or unconnected module marking is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source

private theorem diagram_line : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
  rw [← pointParabolic_map_diagram, Subgroup.map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact diagram_involutive x
  rw [he, Subgroup.map_id]

private theorem line_core : lineParabolicSL.pCoreIn 2 = lineV := by
  have h := map_pCoreIn_of_injective 2 pointParabolicSL diagram.toMonoidHom diagram.injective
  rw [MarkedProduct.pointParabolic_core, pointV_map_diagram, pointParabolic_map_diagram] at h
  exact h.symm

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
  refine ⟨f, ?_, ?_, ?_⟩
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

/-- The two colors are aligned with the literal point/line flag by conjugation
and the checked diagram automorphism, using the original source quotient. -/
theorem exists_parabolicMarking (source : LocalSource L R) (i : Bool) (d : M) :
    Nonempty (ParabolicMarking source i d) := by
  obtain ⟨e₀, hp₀, hl₀⟩ := model_orientation source.flag (!i)
  simp only [Bool.not_not] at hl₀
  let e : MulAut SL := MulAut.conj (source.projection d) * e₀
  have hp : pointParabolicSL.map e.toMonoidHom =
      (modelParabolic source.flag (!i)).map (MulAut.conj (source.projection d)).toMonoidHom := by
    change pointParabolicSL.map
      ((MulAut.conj (source.projection d)).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← Subgroup.map_map, hp₀]
  have hl : lineParabolicSL.map e.toMonoidHom =
      (modelParabolic source.flag i).map (MulAut.conj (source.projection d)).toMonoidHom := by
    change lineParabolicSL.map
      ((MulAut.conj (source.projection d)).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← Subgroup.map_map, hl₀]
  let π := e.symm.toMonoidHom.comp source.projection
  have hA : localFlagActor source (!i) d = (pointParabolicSL.comap π).map (embedM R) := by
    change (((modelParabolic source.flag (!i)).comap source.projection).map (embedM R)).map
      (MulAut.conj (embedM R d)).toMonoidHom = _
    rw [map_conj_map, map_conj_comap, ← hp, map_symm_comap]
  have hk (j : Bool) (C P : Subgroup SL) (hC : P.pCoreIn 2 = C)
      (hP : P.map e.toMonoidHom =
        (modelParabolic source.flag j).map (MulAut.conj (source.projection d)).toMonoidHom) :
      localFlagKernel source j d = (C.comap π).map (embedM R) := by
    rw [Pencils.localFlagKernel_eq_matrix_preimage]
    change ((((modelParabolic source.flag j).pCoreIn 2).map
      (MulAut.conj (source.projection d)).toMonoidHom).comap source.projection).map _ = _
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj (source.projection d)).injective,
      ← hP, ← map_pCoreIn_of_injective 2 _ _ e.injective, hC, map_symm_comap]
  have hK := hk (!i) pointV pointParabolicSL MarkedProduct.pointParabolic_core hp
  have hI := hk i lineV lineParabolicSL line_core hl
  have hQ : Q R (alpha R) = (π.ker.map (embedM R)) := by
    rw [Q_alpha R source.two_group source.core_le, ← source.projection_kernel]
    congr 1
    exact (MonoidHom.ker_comp_of_injective source.projection e.symm.toMonoidHom
      e.symm.injective).symm
  obtain ⟨f, hf, hker, himage⟩ := exists_restricted_marking (embedM R) (embedM_injective R)
    π (e.symm.surjective.comp source.projection_surjective) pointParabolicSL _ hA
  refine ⟨{ hom := f, onto := hf, kernel := ?_, core_image := ?_, incident_image := ?_ }⟩
  · rwa [← hQ] at hker
  · rw [hK]
    apply himage
    rw [← MarkedProduct.pointParabolic_core]
    exact map_subtype_le _
  · rw [hI]
    apply himage
    have hI_le : localFlagKernel source i d ≤ localFlagActor source (!i) d :=
      map_mono (Incident.flagKernel_le_oppositeActor source i)
    rw [hI, hA] at hI_le
    have hpre : lineV.comap π ≤ pointParabolicSL.comap π :=
      (Subgroup.map_le_map_iff_of_injective (embedM_injective R)).mp hI_le
    intro x hx
    obtain ⟨y, rfl⟩ := (e.symm.surjective.comp source.projection_surjective) x
    exact hpre hx

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreMovement.Source
