module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.SylowSource.Selected
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.OvergroupSource
public import Theory.SpecificGroups.PSL3Four.InvolutionMarkings
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.SymmetricPairMarking.Normalizer

/-!
# The selected source normalizer geometry

The selected Sylow normalizer is aligned with two symmetric groups of degree
three. Its component intersection is the first cubic axis, determined by the
actual reflection's fixed component cubic. The original graph and field
involutions then satisfy the generic extended-centralizer geometry, under any
projective marking, with both ambient actors retained explicitly.

Source: Aschbacher--Smith, proof of 15.3.38, printed pp.1136--1137.
-/

public section
open scoped MatrixGroups
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel SylowNormalizer
open Matrix.PSL3Four.ExtendedCentralizer
open Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
variable {G : Type*} [Group G] [Finite G]

/-- The original selected actors give the extended-centralizer normalizer
geometry, with their ambient values retained explicitly. -/
theorem source_selected_normalizer_geometry {d : CharacteristicTwo.LocalData G}
    (s : SourceInputs d) {I L : Subgroup G} (h : Setup d I L)
    (r : LocalResult d I L) (b : SylowResult d I L r)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) :
    letI : (L.subgroupOf I).Normal := r.cover.normal
    ∃ n : NormalizerGeometry (r.extendedOvergroup s h e),
      (n.tauI : G)=(b.lift.dihedral.firstReflection : G) ∧
      (n.fieldI : G)=(b.lift.dihedral.halfTurn : G) := by
  let : (L.subgroupOf I).Normal := r.cover.normal
  let P := (b.lift.X : Subgroup d.Y).map d.Y.subtype
  let N := (d.Y⊔d.S)⊓normalizer (P : Set G)
  have hNI : N≤I := inf_le_left.trans (by rw [←r.cover.plus]; exact h.outside.1.2)
  let tau : N := ⟨b.lift.dihedral.firstReflection,
    mem_sup_right b.lift.first_mem,(source_selected_normalizes r b).1⟩
  let field : N := ⟨b.lift.dihedral.halfTurn,
    mem_sup_right b.lift.halfTurn_mem,(source_selected_normalizes r b).2⟩
  obtain ⟨q₀⟩ := b.lift.normalizer_YS
  obtain ⟨ht2,hf2,ht1,htf,htcomm⟩ := source_selected_pair_laws r b
  obtain ⟨q,hqt,hqf⟩ := aligned_equiv q₀ tau field (Subtype.ext ht2)
    (Subtype.ext hf2) (fun he => ht1 (congrArg Subtype.val he))
    (fun he => htf (congrArg (fun z : N => (z : G)) he)) (Subtype.ext htcomm)
    (fun x hx => Subtype.ext (source_selected_field_inverts_cubics s r b x x.property
      (congrArg Subtype.val hx)))
  have hlinear := source_selected_linear_axis s h r b q tau field rfl rfl hqt hqf
  let NI := N.subgroupOf I
  let j : NI ≃* N := subgroupOfEquivOfLe hNI
  let qI : NI ≃* (SymmetricThree × SymmetricThree) := j.trans q
  let tauI : NI := j.symm tau
  let fieldI : NI := j.symm field
  have hqtI : qI tauI=(1,reflection) := by simpa only [qI,MulEquiv.trans_apply,tauI,j.apply_symm_apply] using hqt
  have hqfI : qI fieldI=(reflection,reflection) := by simpa only [qI,MulEquiv.trans_apply,fieldI,j.apply_symm_apply] using hqf
  have hlinearI : ((L.subgroupOf I).comap NI.subtype).map qI.toMonoidHom =
      (zpowers rotation).prod ⊥ := by
    rw [←hlinear]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨j z,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨j.symm z,hz,?_⟩
      exact congrArg q (j.apply_symm_apply z)
  have hα (x : I) : projectiveAction (L.subgroupOf I)
        (r.extendedOvergroup s h e).cover x =
      (MulAut.congr e) (markedAction r.marking (inclusion (h.normalizes_component s.earlier) x)) := by
    exact DFunLike.congr_fun (r.extendedOvergroup_projectiveAction_eq s h e) x
  have hgraph : IsConj (projectiveAction (L.subgroupOf I)
      (r.extendedOvergroup s h e).cover (tauI : I)) (Matrix.PSL3.OuterSolvable.graph Matrix.PSL3Four.F) := by
    rw [hα]
    obtain ⟨a,ha⟩ := b.lift.graph
    have he := markedAction_eq_of_realizes r.marking
      (inclusion (h.normalizes_component s.earlier) (tauI : I)) ha
    rw [he]
    apply Matrix.PSL3Four.InvolutionMarkings.graph_isConj r.marking.card a ?_ e
    rw [←he,←map_pow]
    have hx : (inclusion (h.normalizes_component s.earlier) (tauI : I))^2=1 :=
      Subtype.ext ht2
    rw [hx,map_one]
  have hfield : IsConj (projectiveAction (L.subgroupOf I)
      (r.extendedOvergroup s h e).cover (fieldI : I)) Matrix.PSL3Four.pslFrobenius := by
    rw [hα]
    obtain ⟨σ,a,hσ,ha⟩ := b.lift.field
    have he := markedAction_eq_of_realizes r.marking
      (inclusion (h.normalizes_component s.earlier) (fieldI : I)) ha
    rw [he]
    apply Matrix.PSL3Four.InvolutionMarkings.field_isConj r.marking.card a σ hσ ?_ e
    rw [←he,←map_pow]
    have hx : (inclusion (h.normalizes_component s.earlier) (fieldI : I))^2=1 :=
      Subtype.ext hf2
    rw [hx,map_one]
  have hcenter : ((tauI : I)*(fieldI : I))∈
      centralizer ((center (L.subgroupOf I)).map (L.subgroupOf I).subtype : Set I) := by
    intro z hz
    obtain ⟨c,hc,rfl⟩ := hz
    have hcL : (((c : L.subgroupOf I) : I) : G) ∈ centerImage L := by
      have hcenterMap : (((c : L.subgroupOf I) : I) : G) ∈ (center L).map L.subtype := by
        exact ⟨(subgroupOfEquivOfLe h.component_le) c,
          (centerCongr (subgroupOfEquivOfLe h.component_le) ⟨c,hc⟩).property,rfl⟩
      exact hcenterMap
    have hh := b.fixes _ (r.cover.center_plane ▸ hcL)
    exact Subtype.ext hh
  obtain ⟨n,hnτ,hnf⟩ := exists_of_marked_normalizer (r.extendedOvergroup s h e)
    NI qI tauI fieldI hqtI hqfI hlinearI hgraph hfield hcenter
  refine ⟨n,?_,?_⟩
  · exact congrArg (fun x : I => (x : G)) hnτ
  · exact congrArg (fun x : I => (x : G)) hnf


end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
