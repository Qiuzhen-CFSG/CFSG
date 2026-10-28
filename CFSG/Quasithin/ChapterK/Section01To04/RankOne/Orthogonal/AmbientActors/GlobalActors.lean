module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.Placement
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.Realization
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.AmbientActors.LocalActors
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification.Conjugacy

/-!
# Global outer actors in the orthogonal source action

Placement by a genuine element of L carries every outer elementary actor
into X. The representation of that same element transports its fixed space.
The pure involution realization discharges the local calculation's action
premise. Thus every outer elementary actor is quadratic, its fixed space has
K-dimension three in rank one and two in larger rank, and its binary ratio
is s or 2s/rank(A), respectively. Threshold actors and minimizers are kept
separate, including the cyclic threshold actors when s=2.

Source: Aschbacher–Smith, K.3.1.2, printed p.454, corrected using the actual
threshold definition D.2.1, printed p.178, in the manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Subgroup
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance globalOuterAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance globalOuterBinarySpace : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L) [L.Normal]

omit [Finite G] [L.Normal] in
/-- The K-span of the marked fixed vectors is transported by the actual layer action. -/
theorem fixedModelSpace_conj (A : Subgroup G) (c : L) :
    M.fixedModelSpace (A.map (MulAut.conj (c : G)).toMonoidHom) =
      (M.fixedModelSpace A).map (action s (M.groupEquiv c)) := by
  rw [fixedModelSpace, fixedModelSpace, Submodule.map_span]
  congr 1
  ext X
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hw : ρ (c : G)⁻¹ v ∈ fixedSpace ρ A := by
      intro a
      change ρ a.val (ρ (c : G)⁻¹ v) = ρ (c : G)⁻¹ v
      have hh : ρ ((c : G) * a.val * (c : G)⁻¹) v = v :=
        hv ⟨_, mem_map_of_mem (MulAut.conj (c : G)).toMonoidHom a.property⟩
      simpa only [map_mul, Module.End.mul_apply, ρ.inv_self_apply] using
        congrArg (ρ (c : G)⁻¹) hh
    refine ⟨M.coordinates (ρ (c : G)⁻¹ v), ⟨_, hw, rfl⟩, ?_⟩
    change SL2.BinarySmall.hermitian s (M.groupEquiv c)
      (M.coordinates (ρ (c : G)⁻¹ v)) = M.coordinates v
    rw [← M.intertwines, ρ.self_inv_apply]
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨ρ (c : G) v, ?_, M.intertwines c v⟩
    intro b
    obtain ⟨a, ha, hab⟩ := b.property
    change ρ b.val (ρ (c : G) v) = ρ (c : G) v
    rw [← hab]
    change ρ ((c : G) * a * (c : G)⁻¹) (ρ (c : G) v) = _
    have hv' : ρ a v = v := hv ⟨a, ha⟩
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply, hv']

omit [Finite G] [L.Normal] in
/-- Layer conjugacy preserves the transported K-dimension, without putting
an additional scalar structure on the original binary carrier. -/
theorem fixedModelSpace_conj_Kfinrank (A : Subgroup G) (c : L) :
    Module.finrank (fixedField s)
      (M.fixedModelSpace (A.map (MulAut.conj (c : G)).toMonoidHom)) =
      Module.finrank (fixedField s) (M.fixedModelSpace A) := by
  rw [M.fixedModelSpace_conj]
  exact (LinearMap.GeneralLinearGroup.toLinearEquiv
    ((action s).asGroupHom (M.groupEquiv c))).finrank_map_eq _

/-- The fixed-space normal forms retain both the original subgroup and the
literal K-linear layer conjugation on its model coordinates. -/
theorem outer_fixedModelSpace_normal_form (h : SourceHypotheses ρ L)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ L) :
    ∃ (c : L) (B : Subgroup G), B ≤ M.outerActor t ∧ ¬ B ≤ L ∧
      A = B.map (MulAut.conj (c : G)).toMonoidHom ∧
      (rank A = 1 → ∃ u : fixedField s,
        B = zpowers (M.modelEmbedding (upper s u.val) * t) ∧
        M.fixedModelSpace A = (outerRootFixedHyperplane s u).map
          (action s (M.groupEquiv c))) ∧
      (2 ≤ rank A → M.fixedModelSpace A =
        (Representation.invariants ((action s).comp (fixedRootGroup s).subtype)).map
          (action s (M.groupEquiv c))) := by
  obtain ⟨c, B, hBX, hBL, _, rfl⟩ := M.outer_elementary_transport h htL ht A hA hout
  have hreal := M.coordinates_pure_involution ht2 ht
  refine ⟨c, B, hBX, hBL, rfl, ?_, ?_⟩
  · intro hr
    rw [rank_map_conj] at hr
    obtain ⟨u, hu, hP⟩ := M.localOuter_rank_one_fixed_space h ht2 htL ht hreal hBX hBL hr
    exact ⟨u, hu, (M.fixedModelSpace_conj B c).trans (congrArg (Submodule.map _) hP)⟩
  · intro hr
    rw [rank_map_conj] at hr
    rw [M.fixedModelSpace_conj,
      M.localOuter_noncyclic_fixedModelSpace h ht2 htL ht hreal hBX hBL hr]

/-- Complete fixed dimensions and action ratios of all outer elementary actors. -/
theorem outer_elementary_calculation (h : SourceHypotheses ρ L)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ L) :
    IsQuadratic ρ A ∧ rank A ≤ s + 1 ∧
      (rank A = 1 → Module.finrank (fixedField s) (M.fixedModelSpace A) = 3 ∧
        fixedCodim ρ A = s ∧ actionRatio ρ A = s) ∧
      (2 ≤ rank A → Module.finrank (fixedField s) (M.fixedModelSpace A) = 2 ∧
        fixedCodim ρ A = 2 * s ∧ actionRatio ρ A = (2 * s : ℕ) / (rank A : ℝ≥0∞)) := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  obtain ⟨c, B, hBX, hBL, _, rfl⟩ := M.outer_elementary_transport h htL ht A hA hout
  have hreal := M.coordinates_pure_involution ht2 ht
  simp only [InnerTransport.quadratic_conj_iff, rank_map_conj,
    M.fixedModelSpace_conj_Kfinrank, fixedCodim_map_conj, InnerTransport.ratio_conj]
  refine ⟨M.localOuter_quadratic ht2 htL ht hreal hBX,
    M.localOuter_rank_le ht2 htL ht hBX, ?_, ?_⟩
  · intro hr
    exact ⟨M.localOuter_rank_one_Kfinrank h ht2 htL ht hreal hBX hBL hr,
      M.localOuter_rank_one_fixedCodim h ht2 htL ht hreal hBX hBL hr,
      M.localOuter_rank_one_actionRatio h ht2 htL ht hreal hBX hBL hr⟩
  · intro hr
    exact ⟨M.localOuter_noncyclic_Kfinrank h ht2 htL ht hreal hBX hBL hr,
      M.localOuter_noncyclic_fixedCodim h ht2 htL ht hreal hBX hBL hr,
      M.localOuter_noncyclic_actionRatio h ht2 htL ht hreal hBX hBL hr⟩

/-- The corrected global outer threshold family. Rank-one actors at s=2
are included, as are the proper rank-s subgroups of X. -/
theorem outer_threshold_iff (h : SourceHypotheses ρ L) (hs : 1 < s)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ L) :
    (IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      rank A = s ∨ rank A = s + 1 ∨ (s = 2 ∧ rank A = 1) := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  obtain ⟨c, B, hBX, hBL, hB, rfl⟩ := M.outer_elementary_transport h htL ht A hA hout
  rw [InnerTransport.quadratic_conj_iff, InnerTransport.ratio_conj, rank_map_conj]
  simpa only [hB, true_and] using M.localOuter_threshold_iff h ht2 htL ht
    (M.coordinates_pure_involution ht2 ht) hBX hBL hs

/-- The minimum in the outer elementary family is attained exactly on the
actual layer conjugates of X, separately from the threshold classification. -/
theorem outer_minimum (h : SourceHypotheses ρ L) (hs : 1 < s)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ L) :
    (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ≤ actionRatio ρ A ∧
      (actionRatio ρ A = (2 * s : ℕ) / (s + 1 : ℝ≥0∞) ↔
        ∃ c : L, A = (M.outerActor t).map (MulAut.conj (c : G)).toMonoidHom) := by
  let : FiniteDimensional (ZMod 2) V :=
    FiniteDimensional.of_injective M.coordinates.toLinearMap M.coordinates.injective
  obtain ⟨c, B, hBX, hBL, _, he⟩ := M.outer_elementary_transport h htL ht A hA hout
  have hreal := M.coordinates_pure_involution ht2 ht
  have hm := M.localOuter_minimum h ht2 htL ht hreal hBX hBL hs
  have hr : actionRatio ρ A = actionRatio ρ B := he ▸ InnerTransport.ratio_conj ρ B c
  refine ⟨hr.symm ▸ hm.1, ?_⟩
  constructor
  · intro hratio
    have hB := hm.2.mp (hr.symm.trans hratio)
    exact ⟨c, he.trans (congrArg (Subgroup.map _) hB)⟩
  · rintro ⟨d, rfl⟩
    rw [InnerTransport.ratio_conj, M.outerActor_actionRatio ht2 htL ht hreal]

/-- Explicitly retain the cyclic outer transvections in the s=2 threshold family. -/
theorem outer_rank_one_at_two (h : SourceHypotheses ρ L) (hs : s = 2)
    {t : G} (ht2 : t ^ 2 = 1) (htL : t ∉ L)
    (ht : M.ambientAut t = Theory.PSL2.fieldAut (conjugation s))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hout : ¬ A ≤ L) (hr : rank A = 1) :
    IsQuadratic ρ A ∧ actionRatio ρ A = 2 := by
  have hc := M.outer_elementary_calculation h ht2 htL ht A hA hout
  exact ⟨hc.1, (hc.2.2.1 hr).2.2.trans (by rw [hs]; norm_num)⟩

end OrthogonalModel
end CFSG.Quasithin.ChapterK.RankOne
