module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.ModelCalculations
public import Theory.Representation.OrthogonalFourMinusRankOne.InnerClassification
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Inner orthogonal actors in the original representation

The marked layer equivalence pulls an actual subgroup of L back to SL₂(F),
and the supplied linear intertwiner preserves its fixed codimension, rank,
and displacement identities. This transports the complete inner actor
classification to the source action. The global ambient conclusion has the
explicit premise that all elementary two-subgroups lie in L; proving this
premise for the allowed extensions is a separate group-theoretic obligation.

Source: Aschbacher–Smith, K.3.1.2, p.454, and D.2.1, p.178.
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

/-- Pull an actual source subgroup into the marked SL₂ model. -/
def innerActor (A : Subgroup G) : Subgroup SL :=
  (A.subgroupOf L).map M.groupEquiv.toMonoidHom

theorem modelImage_innerActor (A : Subgroup G) (hAL : A ≤ L) :
    M.modelImage (M.innerActor A) = A := by
  unfold modelImage innerActor
  rw [Subgroup.map_map]
  have he : M.modelEmbedding.comp M.groupEquiv.toMonoidHom = L.subtype := by
    ext g
    exact congrArg Subtype.val (M.groupEquiv.symm_apply_apply g)
  rw [he, Subgroup.map_subgroupOf_eq_of_le hAL]

theorem innerActor_elementary (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A) :
    IsElementaryTwo (M.innerActor A) := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  refine ⟨?_, IsElementaryAbelian.map M.groupEquiv.toMonoidHom⟩
  intro he
  have hh := M.modelImage_innerActor A hAL
  rw [he] at hh
  apply hA.1
  simpa [modelImage] using hh.symm

/-- Images of model conjugates are literal ambient conjugates by layer elements. -/
theorem modelImage_conj (A : Subgroup SL) (g : SL) :
    M.modelImage (A.map (MulAut.conj g).toMonoidHom) =
      (M.modelImage A).map (MulAut.conj (M.modelEmbedding g)).toMonoidHom := by
  unfold modelImage
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- Every elementary actor in the marked layer is cubic. -/
theorem inner_cubic {A : Subgroup G} (hAL : A ≤ L) (hA : IsElementaryTwo A) : IsCubic ρ A := by
  rw [← M.modelImage_innerActor A hAL, M.modelImage_cubic_iff]
  exact inner_elementary_cubic s _ (M.innerActor_elementary A hAL hA)

theorem inner_quadratic_calculation {A : Subgroup G} (hAL : A ≤ L)
    (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A) :
    fixedCodim ρ A = 2 * s ∧ 2 ≤ actionRatio ρ A := by
  have he := M.modelImage_innerActor A hAL
  have hq' := (M.modelImage_quadratic_iff (M.innerActor A)).mp (he.symm ▸ hq)
  have hh := inner_quadratic_bound s _ (M.innerActor_elementary A hAL hA) hq'
  rw [← he, M.modelImage_fixedCodim, M.modelImage_actionRatio]
  exact hh

theorem inner_actionRatio_bound {A : Subgroup G} (hAL : A ≤ L) (hA : IsElementaryTwo A) :
    3 / 2 ≤ actionRatio ρ A := by
  rw [← M.modelImage_innerActor A hAL, M.modelImage_actionRatio]
  exact inner_ratio_bound s _ (M.innerActor_elementary A hAL hA)

/-- The nonquadratic fixed codimension on the literal source representation. -/
theorem inner_nonquadratic_calculation {A : Subgroup G} (hAL : A ≤ L)
    (hA : IsElementaryTwo A) (hn : ¬ IsQuadratic ρ A) :
    fixedCodim ρ A = 3 * s ∧ 3 / 2 ≤ actionRatio ρ A := by
  have he := M.modelImage_innerActor A hAL
  have hn' : ¬ IsQuadratic (SL2.BinarySmall.hermitian s) (M.innerActor A) := by
    intro hq
    exact hn (he ▸ (M.modelImage_quadratic_iff _).mpr hq)
  have hh := inner_nonquadratic_bound s _ (M.innerActor_elementary A hAL hA) hn'
  rw [← he, M.modelImage_fixedCodim, M.modelImage_actionRatio]
  exact hh

/-- The inner quadratic threshold family on the actual source action. -/
theorem inner_quadratic_threshold {A : Subgroup G} (hAL : A ≤ L) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      ∃ g : SL, A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom) := by
  constructor
  · rintro ⟨hA, hq, hr⟩
    have he := M.modelImage_innerActor A hAL
    have hq' := (M.modelImage_quadratic_iff _).mp (he.symm ▸ hq)
    have hr' : actionRatio (SL2.BinarySmall.hermitian s) (M.innerActor A) ≤ 2 := by
      rwa [← M.modelImage_actionRatio, he]
    obtain ⟨g, hg⟩ := (inner_quadratic_threshold_iff s _).mp
      ⟨M.innerActor_elementary A hAL hA, hq', hr'⟩
    exact ⟨g, he.symm.trans (congrArg M.modelImage hg)⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨he, hq, hr⟩ := (inner_quadratic_threshold_iff s _).mpr ⟨g, rfl⟩
    exact ⟨M.modelImage_elementary he, (M.modelImage_quadratic_iff _).mpr hq,
      (M.modelImage_actionRatio _).trans_le hr⟩

/-- The global minima in any ambient action whose elementary actors are inner. -/
theorem ambient_inner_ratios
    (hinner : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ L) :
    quadraticRatio ρ = 2 ∧ cubicRatio ρ = 3 / 2 := by
  have hu := M.ratio_upper_bounds
  constructor
  · apply le_antisymm hu.1
    exact le_iInf fun A => le_iInf fun hA =>
      (M.inner_quadratic_calculation (hinner A hA.1) hA.1 hA.2).2
  · apply le_antisymm hu.2
    exact le_iInf fun A => le_iInf fun hA =>
      M.inner_actionRatio_bound (hinner A hA.1) hA.1

/-- Ambient quadratic threshold actors, retaining the explicit inner-actor premise. -/
theorem ambient_inner_quadratic_threshold
    (hinner : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ L) (A : Subgroup G) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A ≤ 2) ↔
      ∃ g : SL, A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom) := by
  constructor
  · intro h
    exact (M.inner_quadratic_threshold (hinner A h.1)).mp h
  · rintro ⟨g, rfl⟩
    exact (M.inner_quadratic_threshold (M.modelImage_le_layer _)).mpr ⟨g, rfl⟩

/-- All ambient cubic minimizers are precisely the embedded layer Sylow groups. -/
theorem ambient_inner_cubic_minimizer
    (hinner : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ L) (A : Subgroup G) :
    (IsElementaryTwo A ∧ IsCubic ρ A ∧ actionRatio ρ A = cubicRatio ρ) ↔
      ∃ g : SL, A = M.modelImage
        ((upperUnipotent (Field s)).map (MulAut.conj g).toMonoidHom) := by
  rw [(M.ambient_inner_ratios hinner).2]
  constructor
  · rintro ⟨hA, hc, hr⟩
    have hAL := hinner A hA
    have he := M.modelImage_innerActor A hAL
    have hc' := (M.modelImage_cubic_iff _).mp (he.symm ▸ hc)
    have hr' : actionRatio (SL2.BinarySmall.hermitian s) (M.innerActor A) =
        cubicRatio (SL2.BinarySmall.hermitian s) := by
      rw [(inner_ratios s).2, ← M.modelImage_actionRatio, he, hr]
    obtain ⟨g, hg⟩ := (inner_cubic_minimizer_iff s _).mp
      ⟨M.innerActor_elementary A hAL hA, hc', hr'⟩
    exact ⟨g, he.symm.trans (congrArg M.modelImage hg)⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨he, hc, hr⟩ := (inner_cubic_minimizer_iff s _).mpr ⟨g, rfl⟩
    exact ⟨M.modelImage_elementary he, (M.modelImage_cubic_iff _).mpr hc,
      (M.modelImage_actionRatio _).trans (hr.trans (inner_ratios s).2)⟩

/-- Ambient quadratic minimizers have the same classification as threshold actors. -/
theorem ambient_inner_quadratic_minimizer
    (hinner : ∀ A : Subgroup G, IsElementaryTwo A → A ≤ L) (A : Subgroup G) :
    (IsElementaryTwo A ∧ IsQuadratic ρ A ∧ actionRatio ρ A = quadraticRatio ρ) ↔
      ∃ g : SL, A = M.modelImage ((fixedRootGroup s).map (MulAut.conj g).toMonoidHom) := by
  rw [(M.ambient_inner_ratios hinner).1]
  constructor
  · rintro ⟨he, hq, hr⟩
    exact (M.ambient_inner_quadratic_threshold hinner A).mp ⟨he, hq, hr.le⟩
  · intro h
    obtain ⟨he, hq, hr⟩ := (M.ambient_inner_quadratic_threshold hinner A).mpr h
    exact ⟨he, hq, le_antisymm hr
      (M.inner_quadratic_calculation (hinner A he) he hq).2⟩

end OrthogonalModel
end CFSG.Quasithin.ChapterK.RankOne
