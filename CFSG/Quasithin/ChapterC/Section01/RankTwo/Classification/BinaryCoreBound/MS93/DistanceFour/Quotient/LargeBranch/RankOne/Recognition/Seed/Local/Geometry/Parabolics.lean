module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Marked
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.GroupTheory.CoatomPCoreNormalizer

/-!
# Intrinsic alignment of the two seed parabolics

A binary parabolic is maximal in SL₃(2), whose two-core is trivial.
Its nontrivial intrinsic four-group therefore has that parabolic as its
full normalizer. Projecting equal lifted cores identifies the model
parabolics, and taking inverse images identifies the original parabolics,
even when their flag markings differ. Their ordered residuals then agree.

The point residual has index two, and the opposite core contains an explicit
transvection outside it. They generate the whole point parabolic. The diagram
automorphism and conjugation transport this identity to either orientation
of every flag; core and residual image theorems lift it through the supplied
projection. No choice of a new quotient marking is made.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), marked notation on p.905 and the identity
L_delta1 = Ltilde_delta1 Q_delta2 in (4.6.12)(3), printed p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem model_core_card (g : SL) (i : Bool) :
    Nat.card ((modelParabolic g i).pCoreIn 2) = 4 := by
  rw [pCoreIn, card_map_of_injective (modelParabolic g i).subtype_injective]
  exact (ParabolicCoreModel.core_data (modelParabolicEquivSymmetric g i)).2

private theorem model_core_normalizer (g : SL) (i : Bool) :
    normalizer ((modelParabolic g i).pCoreIn 2 : Set SL) = modelParabolic g i := by
  have hm : IsCoatom (modelParabolic g i) := by
    cases i
    · exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr isCoatom_pointParabolicSL
    · exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr isCoatom_lineParabolicSL
  have hSL : pCore 2 SL = ⊥ := by
    have h := pCore_map_iso 2 equiv
    rw [pCore_two_PSL_eq_bot] at h
    exact (map_eq_bot_iff_of_injective _ equiv.injective).mp h
  apply normalizer_map_pCore_eq_of_isCoatom _ hm hSL
  intro h
  have hc := (ParabolicCoreModel.core_data (modelParabolicEquivSymmetric g i)).2
  rw [h, Subgroup.card_bot] at hc
  contradiction

private theorem model_core_le_borel (g : SL) (i : Bool) :
    (modelParabolic g i).pCoreIn 2 ≤ modelBorel g := by
  have hB : (modelBorelSylow g : Subgroup SL) ≤ modelParabolic g i := by
    rw [coe_modelBorelSylow]
    exact modelParabolic_borel_le g i
  have h := pCoreIn_le_sylow (modelParabolic g i) ((modelBorelSylow g).subtype hB)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hB, coe_modelBorelSylow] at h
  exact h

private theorem line_parabolic_core : lineParabolicSL.pCoreIn 2 = lineV := by
  have h := map_pCoreIn_of_injective 2 pointParabolicSL diagram.toMonoidHom diagram.injective
  rw [MarkedProduct.pointParabolic_core, pointV_map_diagram, pointParabolic_map_diagram] at h
  exact h.symm

private theorem point_generation :
    residual pointParabolicSL ⊔ lineParabolicSL.pCoreIn 2 = pointParabolicSL := by
  have hC : lineParabolicSL.pCoreIn 2 ≤ pointParabolicSL := by
    have h := model_core_le_borel (1 : SL) true
    have he : (MulAut.conj (1 : SL)).toMonoidHom = MonoidHom.id SL := by
      ext x; simp
    have hh := h.trans (modelParabolic_borel_le 1 false)
    change (lineParabolicSL.map (MulAut.conj (1 : SL)).toMonoidHom).pCoreIn 2 ≤
      pointParabolicSL.map (MulAut.conj (1 : SL)).toMonoidHom at hh
    rwa [he, map_id, map_id] at hh
  have hA : residual pointParabolicSL ≤ pointParabolicSL := map_subtype_le _
  have hproper : ¬ lineParabolicSL.pCoreIn 2 ≤ residual pointParabolicSL := by
    rw [line_parabolic_core, point_residual]
    let t : SL := ⟨!![1,0,0; 0,1,1; 0,0,1], by decide⟩
    have ht : t ∈ lineV := by
      change pointCorePred (diagram t)
      unfold pointCorePred
      decide +kernel
    have hout : t ∉ pointA := by
      change ¬ pointResidualPred t
      unfold pointResidualPred
      decide +kernel
    exact fun h => hout (h ht)
  let J := residual pointParabolicSL ⊔ lineParabolicSL.pCoreIn 2
  have hJ : J ≤ pointParabolicSL := sup_le hA hC
  have hi : (residual pointParabolicSL).relIndex pointParabolicSL = 2 := by
    have h := relIndex_mul_relIndex ⊥ (residual pointParabolicSL) pointParabolicSL bot_le hA
    rw [relIndex_bot_left, relIndex_bot_left, card_point_residual, card_pointParabolicSL] at h
    omega
  have hmul := relIndex_mul_relIndex (residual pointParabolicSL) J pointParabolicSL
    le_sup_left hJ
  rw [hi] at hmul
  have hne : (residual pointParabolicSL).relIndex J ≠ 1 := by
    intro he
    exact hproper (le_sup_right.trans (relIndex_eq_one.mp he))
  have he : J.relIndex pointParabolicSL = 1 := by
    have hd : (residual pointParabolicSL).relIndex J ∣ 2 := ⟨_, hmul.symm⟩
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
    · exact (hne h).elim
    · rw [h] at hmul; omega
  exact le_antisymm hJ (relIndex_eq_one.mp he)

private theorem base_generation (i : Bool) :
    residual (if i then lineParabolicSL else pointParabolicSL) ⊔
      (if !i then lineParabolicSL else pointParabolicSL).pCoreIn 2 =
      (if i then lineParabolicSL else pointParabolicSL) := by
  cases i
  · exact point_generation
  · have h := congrArg (map diagram.toMonoidHom) point_generation
    rw [Subgroup.map_sup, MarkedAutomorphisms.residual, map_embedded_pResidual, pointParabolic_map_diagram] at h
    have hl : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (diagram_point_line (diagram y)).mp (by rwa [diagram_involutive])
      · intro hx
        exact ⟨diagram x, (diagram_point_line x).mpr hx, diagram_involutive x⟩
    rw [map_pCoreIn_of_injective _ _ _ diagram.injective, hl] at h
    exact h

private theorem model_generation (g : SL) (i : Bool) :
    residual (modelParabolic g i) ⊔ (modelParabolic g (!i)).pCoreIn 2 =
      modelParabolic g i := by
  have h := congrArg (map (MulAut.conj g).toMonoidHom) (base_generation i)
  rw [Subgroup.map_sup, MarkedAutomorphisms.residual, map_embedded_pResidual,
    map_pCoreIn_of_injective _ _ _ (MulAut.conj g).injective] at h
  exact h

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {source : LocalSource L R}

private theorem core_projection (f : Frame source) (i : Bool) :
    (f.core i).map source.projection =
      (modelParabolic f.flag (if i then !f.first else f.first)).pCoreIn 2 := by
  change ((f.parabolic i).pCoreIn 2).map source.projection = _
  rw [map_pCoreIn_of_ker_isPGroup source.projection
    (by rw [source.projection_kernel]; exact pCore_isPGroup)]
  congr 1
  exact map_comap_eq_self_of_surjective source.projection_surjective _

private theorem parabolic_eq_of_core_eq (f k : Frame source) (i j : Bool)
    (h : f.core i = k.core j) : f.parabolic i = k.parabolic j := by
  have he := congrArg (map source.projection) h
  rw [core_projection, core_projection] at he
  have hn := congrArg (fun U : Subgroup SL => normalizer (U : Set SL)) he
  rw [model_core_normalizer, model_core_normalizer] at hn
  exact congrArg (comap source.projection) hn

/-- The first full actor is generated, after the original projection, by its
ordered residual and the second intrinsic core. -/
theorem actor_image_generation (f : Frame source) :
    (f.actor false).map source.projection =
      (f.residual false).map source.projection ⊔ (f.core true).map source.projection := by
  rw [f.actor_eq, core_projection]
  have hP : (f.parabolic false).map source.projection = modelParabolic f.flag f.first :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  have hR : (f.residual false).map source.projection = residual (modelParabolic f.flag f.first) := by
    unfold Frame.residual Frame.parabolic
    rw [rankOne_parabolic_eq source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup), map_embedded_pResidual]
    change ((pResidual 2 ((f.parabolic false).map source.projection)).map
      ((f.parabolic false).map source.projection).subtype) = _
    rw [hP]
    rfl
  rw [hP, hR]
  exact (model_generation f.flag f.first).symm
/-- The projected intrinsic core has exactly four elements. -/
theorem Frame.core_image_card (f : Frame source) (i : Bool) :
    Nat.card ((f.core i).map source.projection) = 4 := by
  rw [core_projection]
  exact model_core_card _ _

/-- Equal intrinsic first cores identify the actual parabolics for arbitrary markings. -/
theorem Frame.first_parabolic_eq_flag {geometry : Geometry R}
    (f : Frame source) (s : CriticalSegment geometry) (hf : Compatible f s)
    (i : Bool) (hi : Flags.RankOne.flagKernel source i = Q R (beta R)) :
    f.parabolic false = MS93.parabolic source.projection source.flag i := by
  let k : Frame source := ⟨source.flag, i⟩
  have he : f.core false = k.core false := by
    apply map_injective (embedM_injective R)
    exact hf.first_core.trans hi.symm
  exact parabolic_eq_of_core_eq f k false false he

/-- The ordered residual aligns through the parabolic equality, without identifying flags. -/
theorem Frame.first_residual_eq_flag {geometry : Geometry R}
    (f : Frame source) (s : CriticalSegment geometry) (hf : Compatible f s)
    (i : Bool) (hi : Flags.RankOne.flagKernel source i = Q R (beta R)) :
    (f.residual false).map (embedM R) = Flags.RankOne.flagResidual source i := by
  unfold Frame.residual
  rw [f.first_parabolic_eq_flag s hf i hi]
  rfl
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
