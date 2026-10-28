module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic

/-!
# Transport of the binary rank-one radius conclusions

The center description of B makes its conjugation covariance explicit.
Consequently the noncentral distance-two generators and their edge span
transport under the original right-coset action. Edge transitivity then
reduces all three radius conclusions to the distinguished edge.

`BaseConclusions` is an output interface. This module proves transport,
not its construction from the source hypotheses.

Source: MS93 (1993), (4.6.8)--(4.6.10), printed pp.905--908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- An intrinsic subgroup center transports under the given ambient isomorphism. -/
theorem centerImage_map {G : Type*} [Group G] (P : Subgroup G) (e : G ≃* G) :
    ((center P).map P.subtype).map e.toMonoidHom =
      (center (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨e.subgroupMap P z, (centerCongr (e.subgroupMap P) ⟨z, hz⟩).property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(e.subgroupMap P).symm z,
      ⟨(e.subgroupMap P).symm z,
        (centerCongr (e.subgroupMap P).symm ⟨z, hz⟩).property, rfl⟩, ?_⟩
    exact congrArg Subtype.val ((e.subgroupMap P).apply_symm_apply z)

/-- The actual radius-center description transports B under right multiplication. -/
theorem B_act (geometry : Geometry R) (early : EarlyFacts R geometry)
    (g : FreeAmalgam R) (a : Vertex R) (ha : color R a = false) :
    B R (act R g a) (geometry.Z_normal (act R g a)) =
      (B R a (geometry.Z_normal a)).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [early.B_eq_center a ha,
    early.B_eq_center (act R g a) (by rwa [action_preserves_color]),
    centerImage_map, V_act]

/-- Noncentral distance-two generators transport in both directions. -/
theorem nu_act_iff (geometry : Geometry R) (early : EarlyFacts R geometry)
    (g : FreeAmalgam R) (a t : Vertex R) (ha : color R a = false) :
    nu R geometry (act R g a) (act R g t) ↔ nu R geometry a t := by
  unfold nu
  rw [dist_act, B_act geometry early g a ha, Z_act,
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]

/-- The actual edge star transports by inverse conjugation in the right-coset graph. -/
theorem edgeStar_act (geometry : Geometry R) (early : EarlyFacts R geometry)
    (g : FreeAmalgam R) (a b : Vertex R) (ha : color R a = false) :
    edgeStar R geometry (act R g a) (act R g b) =
      (edgeStar R geometry a b).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [edgeStar, Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    have ht' : nu R geometry a (act R g⁻¹ t) ∧ Adjacent R b (act R g⁻¹ t) := by
      have hn := (nu_act_iff geometry early g⁻¹ (act R g a) t
        (by rwa [action_preserves_color])).mpr ht.1
      have he := (adjacent_act_iff R g⁻¹ (act R g b) t).mpr ht.2
      simpa only [← act_mul, mul_inv_cancel, act_one] using And.intro hn he
    refine le_iSup_of_le (act R g⁻¹ t) (le_iSup_of_le ht' ?_)
    rw [← Z_act]
    simp only [← act_mul, inv_mul_cancel, act_one, le_refl]
  · apply iSup_le
    intro t
    apply iSup_le
    intro ht
    refine le_iSup_of_le (act R g t) (le_iSup_of_le
      ⟨(nu_act_iff geometry early g a t ha).mpr ht.1,
        (adjacent_act_iff R g b t).mpr ht.2⟩ ?_)
    rw [Z_act]

/-- Distinguished-edge outputs still required from (4.6.9). -/
structure BaseConclusions (R : Subgroup M) (geometry : Geometry R) : Prop where
  radius_derived : ⁅V R (alpha R), V R (alpha R)⁆ = U R (alpha R)
  core_le_radius : core R (alpha R) ≤ V R (alpha R)
  edge_commutator_le : ⁅edgeStar R geometry (alpha R) (beta R), Q R (alpha R)⁆ ≤
    U R (alpha R)

/-- Edge transitivity transports the three distinguished-edge conclusions to every vertex. -/
theorem rankOneConclusions_of_base (geometry : Geometry R)
    (early : EarlyFacts R geometry) (base : BaseConclusions R geometry) :
    RankOneConclusions R geometry where
  radius_derived := by
    intro a ha
    obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
    have hga : act R g (alpha R) = mVertex R g := by simp [alpha]
    rw [← hga, V_act, U_act, ← map_commutator, base.radius_derived]
  core_le_radius := by
    intro a ha
    obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
    have hga : act R g (alpha R) = mVertex R g := by simp [alpha]
    rw [← hga, core_act, V_act]
    exact map_mono base.core_le_radius
  edge_commutator_le := by
    intro a b ha hab
    obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a b).mp hab
    · have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) base.edge_commutator_le
      rw [map_commutator,
        ← edgeStar_act geometry early g (alpha R) (beta R) rfl, ← Q_act, ← U_act] at h
      simpa only [alpha, beta, act_mVertex, act_hVertex, one_mul] using h
    · simp [color, hVertex] at ha

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
