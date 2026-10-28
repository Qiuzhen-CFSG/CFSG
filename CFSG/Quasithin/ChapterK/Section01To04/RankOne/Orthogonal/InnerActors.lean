module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.InnerActors.Transport

/-!
# Inner orthogonal actors in the source Sylow intersection

The original T∩L is the image of a Sylow two-subgroup of the marked layer.
Conjugacy identifies it with the canonical full root group, giving its exact
rank, fixed codimension and ratio. Among elementary actors inside this literal
intersection it is the unique cubic minimizer. The fixed-field lines supply
all inner quadratic threshold actors, through the reexported transport API.

The ambient minima remain conditional on all elementary actors lying in L.
The odd-extension owner discharges that premise; this module does not assume
unfinished extension classification results.

Source: Aschbacher–Smith, K.3.1.2, printed p.454, D.2.1, printed p.178.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
local notation "SL" => Matrix.SpecialLinearGroup (Fin 2) (Field s)
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L)
include M

/-- Mark the literal source intersection T∩L by a conjugate of the full root group. -/
theorem sylow_intersection_model [Finite G] [L.Normal] (T : Sylow 2 G) :
    ∃ g : SL, (T : Subgroup G) ⊓ L = M.modelImage
      ((upperUnipotent (Field s)).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  let Q : Sylow 2 SL := P.mapSurjective (f := M.groupEquiv.toMonoidHom) M.groupEquiv.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL (upperUnipotentSylow (Field s) 2) Q
  have hQ : (Q : Subgroup SL) =
      (upperUnipotent (Field s)).map (MulAut.conj g).toMonoidHom := by rw [← hg]; rfl
  have he : M.modelImage (Q : Subgroup SL) = (P : Subgroup L).map L.subtype := by
    change ((P : Subgroup L).map M.groupEquiv.toMonoidHom).map M.modelEmbedding = _
    rw [Subgroup.map_map]
    congr 1
    ext x
    exact congrArg Subtype.val (M.groupEquiv.symm_apply_apply x)
  exact ⟨g, hP.symm.trans (he.symm.trans (congrArg M.modelImage hQ))⟩

/-- The full source calculation for the literal T∩L, valid also for s=1. -/
theorem sylow_intersection_calculation [Finite G] [L.Normal] (T : Sylow 2 G) :
    IsElementaryTwo ((T : Subgroup G) ⊓ L) ∧
    IsCubic ρ ((T : Subgroup G) ⊓ L) ∧
    ¬ IsQuadratic ρ ((T : Subgroup G) ⊓ L) ∧
    rank ((T : Subgroup G) ⊓ L) = 2 * s ∧
    fixedCodim ρ ((T : Subgroup G) ⊓ L) = 3 * s ∧
    actionRatio ρ ((T : Subgroup G) ⊓ L) = 3 / 2 := by
  obtain ⟨g, hg⟩ := M.sylow_intersection_model T
  rw [hg, M.modelImage_cubic_iff, M.modelImage_quadratic_iff,
    M.modelImage_rank, M.modelImage_fixedCodim, M.modelImage_actionRatio,
    InnerTransport.cubic_conj_iff, InnerTransport.quadratic_conj_iff,
    rank_map_conj, fixedCodim_map_conj, InnerTransport.ratio_conj]
  exact ⟨M.modelImage_elementary ((upper_elementary s).map_conj g),
    root_subgroup_cubic s _ le_rfl, upper_not_quadratic s,
    upper_rank s, upper_fixedCodim s, upper_actionRatio s⟩

/-- A ratio-3/2 actor inside T∩L must be the entire intersection. -/
theorem sylow_intersection_unique_minimizer [Finite G] [L.Normal] (T : Sylow 2 G)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G) ⊓ L) (hA : IsElementaryTwo A) :
    actionRatio ρ A = 3 / 2 ↔ A = (T : Subgroup G) ⊓ L := by
  constructor
  · intro hr
    have hAL : A ≤ L := hAT.trans inf_le_right
    have he := M.modelImage_innerActor A hAL
    have hE := M.innerActor_elementary A hAL hA
    have hR : actionRatio (SL2.BinarySmall.hermitian s) (M.innerActor A) =
        cubicRatio (SL2.BinarySmall.hermitian s) := by
      rw [(inner_ratios s).2, ← M.modelImage_actionRatio, he, hr]
    obtain ⟨g, hg⟩ := (inner_cubic_minimizer_iff s _).mp
      ⟨hE, inner_elementary_cubic s _ hE, hR⟩
    have hrA : rank A = 2 * s := by
      rw [← he, M.modelImage_rank, hg, rank_map_conj, upper_rank]
    have hC := M.sylow_intersection_calculation T
    apply Subgroup.eq_of_le_of_card_ge hAT
    rw [hA.card_eq_two_pow_rank, hC.1.card_eq_two_pow_rank, hrA, hC.2.2.2.1]
  · rintro rfl
    exact (M.sylow_intersection_calculation T).2.2.2.2.2

/-- The source's fixed-line assertion transported to the literal action.
The generated subgroup is the actual join of the embedded R_t and root element. -/
theorem fixedSpace_adjoin_model_outside
    (g : SL) (hg : g ∈ upperUnipotent (Field s)) (hout : g ∉ fixedRootGroup s) :
    fixedSpace ρ (M.modelImage (fixedRootGroup s) ⊔ Subgroup.zpowers (M.modelEmbedding g)) =
      fixedSpace ρ (M.modelImage (upperUnipotent (Field s))) := by
  have he := (fixedSpace_adjoin_outside_fixedRoot s g hg hout).1
  have hmem (A : Subgroup SL) (v : V) :
      v ∈ fixedSpace ρ (M.modelImage A) ↔
        M.coordinates v ∈ fixedSpace (SL2.BinarySmall.hermitian s) A := by
    constructor
    · intro hv a
      have hh := congrArg M.coordinates
        (hv ⟨M.modelEmbedding a, Subgroup.mem_map_of_mem _ a.property⟩)
      change M.coordinates (ρ (M.modelEmbedding a.val) v) = M.coordinates v at hh
      change SL2.BinarySmall.hermitian s a.val (M.coordinates v) = M.coordinates v
      exact (M.modelEmbedding_intertwines a.val v).symm.trans hh
    · intro hv a
      obtain ⟨b, hb, hab⟩ := a.property
      change ρ a.val v = v
      rw [← hab]
      apply M.coordinates.injective
      rw [M.modelEmbedding_intertwines]
      exact hv ⟨b, hb⟩
  have hj : M.modelImage (fixedRootGroup s ⊔ Subgroup.zpowers g) =
      M.modelImage (fixedRootGroup s) ⊔ Subgroup.zpowers (M.modelEmbedding g) := by
    unfold modelImage
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  rw [← hj]
  ext v
  rw [hmem, hmem, he]

end OrthogonalModel
end CFSG.Quasithin.ChapterK.RankOne
