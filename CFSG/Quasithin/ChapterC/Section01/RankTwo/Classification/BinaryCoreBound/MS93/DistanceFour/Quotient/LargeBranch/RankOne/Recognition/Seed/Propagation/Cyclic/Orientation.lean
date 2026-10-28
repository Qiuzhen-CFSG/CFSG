module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Consequences
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Propagation.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import Theory.GroupTheory.PCoreImage
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# The incident frame has the prescribed dual orientation

In the supplied natural module U_alpha, the subgroup fixed by Q_beta has
order four: its index is the edge index two. Frame compatibility identifies
Q_beta with the actual first parabolic core. After transporting that
parabolic from the standard point parabolic, an inner natural marking would
put all four fixed vectors in a binary line, which has only two elements.
Thus the relative marking is outer. The inner/graph automorphism theorem
then aligns both incident parabolics with the inverse-transpose twist of
exactly common.natural.marking, using one inner conjugation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), notation p.905 and the duality conclusion of (4.6.12)(3), p.911.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph Matrix
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {geometry : Geometry R}
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem lineParabolic_map_diagram :
    lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
  rw [← pointParabolic_map_diagram, Subgroup.map_map]
  have he : diagram.toMonoidHom.comp diagram.toMonoidHom = MonoidHom.id SL := by
    ext g : 1
    exact diagram_involutive g
  rw [he, Subgroup.map_id]

private theorem frame_coordinates (f : Frame source) :
    ∃ e : SL ≃* SL,
      pointParabolicSL.map e.toMonoidHom = (f.parabolic false).map source.projection ∧
      lineParabolicSL.map e.toMonoidHom = (f.parabolic true).map source.projection := by
  have hp (i : Bool) : (f.parabolic i).map source.projection =
      modelParabolic f.flag (if i then !f.first else f.first) :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  cases hi : f.first
  · refine ⟨MulAut.conj f.flag, ?_, ?_⟩ <;> rw [hp] <;>
      simp only [hi, Bool.not_false, Bool.false_eq_true, if_false, if_true] <;> rfl
  · refine ⟨diagram.trans (MulAut.conj f.flag), ?_, ?_⟩
    · rw [hp]
      change pointParabolicSL.map ((MulAut.conj f.flag).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← Subgroup.map_map, pointParabolic_map_diagram]
      simp only [hi, Bool.false_eq_true, if_false]
      rfl
    · rw [hp]
      change lineParabolicSL.map ((MulAut.conj f.flag).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← Subgroup.map_map, lineParabolic_map_diagram]
      simp only [hi, Bool.not_true, if_true]
      rfl

private theorem pointV_le_parabolic_core : pointV ≤ pointParabolicSL.pCoreIn 2 := by
  have hn : (pointA.subgroupOf pointParabolicSL).Normal := by
    constructor
    intro a ha g
    exact pointA_conj g g.property a ha
  have h := pCoreIn_mono_of_normalizes (p := 2) pointA_le
    ((normal_subgroupOf_iff_le_normalizer pointA_le).mp hn)
  rwa [point_core] at h

private theorem core_image [Finite M] (f : Frame source) :
    (f.core false).map source.projection =
      ((f.parabolic false).map source.projection).pCoreIn 2 := by
  exact map_pCoreIn_of_ker_isPGroup source.projection
    (by rw [source.projection_kernel]; exact pCore_isPGroup) _

private def t01 : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def t02 : SL := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
private theorem t01_mem : t01 ∈ pointV := by decide
private theorem t02_mem : t02 ∈ pointV := by decide

private theorem fixed_axis (v : Linear.W)
    (h1 : (specialLinearNatural 3) t01 v = v)
    (h2 : (specialLinearNatural 3) t02 v = v) :
    v = ![v 0, 0, 0] := by
  have h1 := congrFun h1 0
  have h2 := congrFun h2 0
  change t01.val.mulVec v 0 = v 0 at h1
  change t02.val.mulVec v 0 = v 0 at h2
  simp [t01, t02, mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
  ext i
  fin_cases i <;> simp [h1, h2]

private theorem natural_fixed [Finite M]
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (f : Frame source) (hf : Compatible f s) (g : SL)
    (hg : g ∈ (f.core false).map source.projection)
    (u : U R (alpha R)) (hu : (u : FreeAmalgam R) ∈ Z R (beta R)) :
    (specialLinearNatural 3) (common.natural.marking g) (common.natural.equiv u).toAdd =
      (common.natural.equiv u).toAdd := by
  obtain ⟨m, hm, rfl⟩ := hg
  have hmQ : embedM R m ∈ Q R (beta R) := by
    rw [← hf.first_core]
    exact mem_map_of_mem _ hm
  have huC : (u : FreeAmalgam R) ∈ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
    have he := Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)
    rw [he] at hu
    exact hu.2
  have ha := common.natural.action m u u (by
    have he := huC (embedM R m) hmQ
    calc
      (u : FreeAmalgam R) = (u * embedM R m) * (embedM R m)⁻¹ := by simp
      _ = (embedM R m * u) * (embedM R m)⁻¹ := by rw [he])
  exact ha.symm

private theorem frame_marking_outer [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (f : Frame source) (hf : Compatible f s)
    (e : SL ≃* SL)
    (he : pointParabolicSL.map e.toMonoidHom = (f.parabolic false).map source.projection) :
    e.trans common.natural.marking ∉ MulAut.innerSubgroup SL := by
  rintro ⟨k, hk⟩
  have hcore : pointV.map e.toMonoidHom ≤ (f.core false).map source.projection := by
    rw [core_image, ← he, ← map_pCoreIn_of_injective 2 _ _ e.injective]
    exact map_mono pointV_le_parabolic_core
  let A := (Z R (beta R)).subgroupOf (U R (alpha R))
  have hindex : A.index = 2 := by
    change (Z R (beta R)).relIndex (U R (alpha R)) = 2
    rw [← Early.edge_Z_index_eq_natural common (alpha R) (beta R) rfl (base_adjacent R)]
    exact radius.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
  have hcard : Nat.card A = 4 := by
    have hh := A.card_mul_index
    rw [hindex, DistanceEight.U_card R common.natural] at hh
    omega
  let q : A → Linear.W := fun u => (specialLinearNatural 3) k⁻¹
    (common.natural.equiv u.val).toAdd
  have hfixed (u : A) (t : SL) (ht : t ∈ pointV) :
      (specialLinearNatural 3) t (q u) = q u := by
    have hh := natural_fixed common s f hf (e t)
      (hcore (mem_map_of_mem _ ht)) u.val u.property
    have heq : common.natural.marking (e t) = k * t * k⁻¹ := by
      exact (congrArg (fun a : MulAut SL => a t) hk).symm
    rw [heq] at hh
    have hh := congrArg ((specialLinearNatural 3) k⁻¹) hh
    simpa only [q, ← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] using hh
  have haxis (u : A) : q u = ![q u 0, 0, 0] :=
    fixed_axis (q u) (hfixed u t01 t01_mem) (hfixed u t02 t02_mem)
  have hq : Function.Injective q := by
    intro u v huv
    apply Subtype.ext
    apply common.natural.equiv.injective
    apply Multiplicative.toAdd.injective
    exact ((specialLinearNatural 3).apply_bijective k⁻¹).1 huv
  have hi : Function.Injective (fun u : A => q u 0) := by
    intro u v huv
    apply hq
    change q u 0 = q v 0 at huv
    rw [haxis u, haxis v, huv]
  have hle := Nat.card_le_card_of_injective _ hi
  rw [hcard, Nat.card_zmod] at hle
  omega

/-- The two incident actors have the orientation dual to the original natural
marking. One inner conjugation aligns the entire flag, not just one parabolic. -/
theorem exists_dual_frame [Finite M]
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (f : Frame source) (hf : Compatible f s) :
    ∃ k : SL,
      pointParabolicSL.map ((MulAut.conj k).trans
        (dualTwist common.natural.marking)).toMonoidHom =
          (f.parabolic false).map source.projection ∧
      lineParabolicSL.map ((MulAut.conj k).trans
        (dualTwist common.natural.marking)).toMonoidHom =
          (f.parabolic true).map source.projection := by
  obtain ⟨e, he, he'⟩ := frame_coordinates f
  obtain ⟨k, hk⟩ := BinaryLinearThree.AutomorphismAction.outer_eq_inner_graph
    (e.trans common.natural.marking) (frame_marking_outer common radius s f hf e he)
  let t := BinaryLinearThree.AutomorphismAction.graph k
  have ht : (MulAut.conj t).trans (dualTwist common.natural.marking) = e := by
    ext g : 1
    apply common.natural.marking.injective
    have hh := congrArg (fun a : MulAut SL => a g) hk
    change common.natural.marking (e g) =
      k * BinaryLinearThree.AutomorphismAction.graph g * k⁻¹ at hh
    rw [hh]
    simp only [MulEquiv.trans_apply, dualTwist, MulAut.conj_apply,
      MulEquiv.apply_symm_apply, map_mul, map_inv, t,
      BinaryLinearThree.AutomorphismAction.graph_graph]
  exact ⟨t, ht ▸ he, ht ▸ he'⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
