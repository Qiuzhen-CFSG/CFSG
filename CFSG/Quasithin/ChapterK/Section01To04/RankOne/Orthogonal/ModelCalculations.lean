module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Model
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Orthogonal root actors in the original source representation

The marked group equivalence embeds the fixed-field and full root groups in
the original layer. The binary intertwiner preserves their displacement
identities, fixed codimensions and ratios. Thus the concrete calculations
supply quadratic and cubic actors of ratios two and 3/2 in the actual ambient
representation. No normalizer hypothesis, module recognition or global
minimum statement is assumed in this transport.

Source: Aschbacher–Smith, K.3.1.2 and Table B.4.5, printed pp.454 and 87.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.RankOne
open Matrix.SpecialLinearGroup
open scoped ENNReal
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))
namespace OrthogonalModel
variable (M : OrthogonalModel s ρ L)

/-- A model actor embedded in the original group, along the marked layer equivalence. -/
def modelImage (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) : Subgroup G :=
  A.map M.modelEmbedding

theorem modelImage_le_layer (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
    M.modelImage A ≤ L := by
  rintro _ ⟨g, _, rfl⟩
  exact (M.groupEquiv.symm g).property

theorem modelImage_rank (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
    rank (M.modelImage A) = rank A :=
  rank_map_injective M.modelEmbedding M.modelEmbedding_injective A

theorem modelImage_fixedCodim (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
    fixedCodim ρ (M.modelImage A) = fixedCodim (SL2.BinarySmall.hermitian s) A := by
  symm
  apply fixedCodim_map_equivariant (SL2.BinarySmall.hermitian s) ρ
    M.modelEmbedding M.coordinates.symm
  intro g v
  apply M.coordinates.injective
  rw [M.coordinates.apply_symm_apply, M.modelEmbedding_intertwines,
    M.coordinates.apply_symm_apply]

theorem modelImage_actionRatio (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
    actionRatio ρ (M.modelImage A) = actionRatio (SL2.BinarySmall.hermitian s) A := by
  rw [actionRatio, actionRatio, M.modelImage_fixedCodim, M.modelImage_rank]

theorem modelImage_elementary {A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))}
    (hA : IsElementaryTwo A) : IsElementaryTwo (M.modelImage A) := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map M.modelEmbedding⟩
  intro hz
  apply hA.1
  exact (Subgroup.map_eq_bot_iff_of_injective A M.modelEmbedding_injective).mp hz

theorem displacement_intertwines (g : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (v : V) :
    M.coordinates (displacement ρ (M.modelEmbedding g) v) =
      displacement (SL2.BinarySmall.hermitian s) g (M.coordinates v) := by
  simp only [displacement, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
    M.modelEmbedding_intertwines]

theorem modelImage_quadratic_iff (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
    IsQuadratic ρ (M.modelImage A) ↔ IsQuadratic (SL2.BinarySmall.hermitian s) A := by
  constructor
  · intro h a ha b hb X
    obtain ⟨v, rfl⟩ := M.coordinates.surjective X
    apply sub_eq_zero.mp
    change displacement (SL2.BinarySmall.hermitian s) a
      (displacement (SL2.BinarySmall.hermitian s) b (M.coordinates v)) = 0
    rw [← M.displacement_intertwines, ← M.displacement_intertwines]
    have hz := sub_eq_zero.mpr (h _ (Subgroup.mem_map_of_mem _ ha) _
      (Subgroup.mem_map_of_mem _ hb) v)
    exact (congrArg M.coordinates hz).trans M.coordinates.map_zero
  · intro h a ha b hb v
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    apply sub_eq_zero.mp
    apply M.coordinates.injective
    change M.coordinates (displacement ρ (M.modelEmbedding a)
      (displacement ρ (M.modelEmbedding b) v)) = M.coordinates 0
    rw [M.displacement_intertwines, M.displacement_intertwines, map_zero]
    exact sub_eq_zero.mpr (h a ha b hb _)

theorem modelImage_cubic_iff (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s))) :
    IsCubic ρ (M.modelImage A) ↔ IsCubic (SL2.BinarySmall.hermitian s) A := by
  constructor
  · intro h a ha b hb c hc X
    obtain ⟨v, rfl⟩ := M.coordinates.surjective X
    rw [← M.displacement_intertwines, ← M.displacement_intertwines, ← M.displacement_intertwines]
    rw [h _ (Subgroup.mem_map_of_mem _ ha) _ (Subgroup.mem_map_of_mem _ hb) _
      (Subgroup.mem_map_of_mem _ hc) v, map_zero]
  · intro h a ha b hb c hc v
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    obtain ⟨c, hc, rfl⟩ := hc
    apply M.coordinates.injective
    rw [M.displacement_intertwines, M.displacement_intertwines, M.displacement_intertwines,
      h a ha b hb c hc _, map_zero]

/-- The fixed-field root group supplies the source's quadratic actor of ratio two,
on the original representation and in the original layer. -/
theorem fixedRoot_calculation :
    IsElementaryTwo (M.modelImage (fixedRootGroup s)) ∧
    IsQuadratic ρ (M.modelImage (fixedRootGroup s)) ∧
    rank (M.modelImage (fixedRootGroup s)) = s ∧
    fixedCodim ρ (M.modelImage (fixedRootGroup s)) = 2 * s ∧
    actionRatio ρ (M.modelImage (fixedRootGroup s)) = 2 := by
  exact ⟨M.modelImage_elementary (fixedRoot_elementary s),
    (M.modelImage_quadratic_iff _).mpr (fixedRoot_quadratic s),
    (M.modelImage_rank _).trans (fixedRoot_rank s),
    (M.modelImage_fixedCodim _).trans (fixedRoot_fixedCodim s),
    (M.modelImage_actionRatio _).trans (fixedRoot_actionRatio s)⟩

/-- The full root actor is cubic but not quadratic, with the claimed ratio 3/2. -/
theorem upper_calculation :
    IsElementaryTwo (M.modelImage (upperUnipotent (Field s))) ∧
    IsCubic ρ (M.modelImage (upperUnipotent (Field s))) ∧
    ¬ IsQuadratic ρ (M.modelImage (upperUnipotent (Field s))) ∧
    rank (M.modelImage (upperUnipotent (Field s))) = 2 * s ∧
    fixedCodim ρ (M.modelImage (upperUnipotent (Field s))) = 3 * s ∧
    actionRatio ρ (M.modelImage (upperUnipotent (Field s))) = 3 / 2 := by
  exact ⟨M.modelImage_elementary (upper_elementary s),
    (M.modelImage_cubic_iff _).mpr (root_subgroup_cubic s _ le_rfl),
    fun h => upper_not_quadratic s ((M.modelImage_quadratic_iff _).mp h),
    (M.modelImage_rank _).trans (upper_rank s),
    (M.modelImage_fixedCodim _).trans (upper_fixedCodim s),
    (M.modelImage_actionRatio _).trans (upper_actionRatio s)⟩

include M in
/-- The upper bounds in B.4.5's orthogonal row hold in every actual ambient
extension of the marked action. No full-normalizer SQTK hypothesis is used. -/
theorem ratio_upper_bounds : quadraticRatio ρ ≤ 2 ∧ cubicRatio ρ ≤ 3 / 2 := by
  have hR := M.fixedRoot_calculation
  have hU := M.upper_calculation
  constructor
  · exact iInf_le_of_le _ (iInf_le_of_le ⟨hR.1, hR.2.1⟩ (le_of_eq hR.2.2.2.2))
  · exact iInf_le_of_le _ (iInf_le_of_le ⟨hU.1, hU.2.1⟩ (le_of_eq hU.2.2.2.2.2))

end OrthogonalModel
end
end CFSG.Quasithin.ChapterK.RankOne
