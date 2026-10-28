module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.NativeRestriction
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Models

/-!
# Original unitary-four extensions cannot contain the selected diagram layer

The broad markings identify the native inner endpoint and the image of the
source residual separately. They retain the full common Borel and permit
outer automorphisms, including the degree-two graph extension. Pulling the
native right endpoint back through the same marking puts the selected R and
its normal intermediate layer in that base. The proved point Frattini or
plane irreducibility dichotomy excludes the two noncentral layers.

This treats both orientations and every positive degree. It does not assert
that an arbitrary original unitary extension is ordinary or degree two; that
normalized-Borel restriction and the whole-residual recognition still need
proof. The literal Chapter 12 consumer applies this earlier diagram exclusion
without a pure-model comparison or an assumed two-core equality.

Source: Aschbacher--Smith F.1.12(I)(6), pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalUnitaryFour
open ChapterF.GreenBook.LieModels.UnitaryFour

/-- The native endpoints, in either original orientation. -/
@[expose] def endpoint (m : ℕ) (hm : 1 ≤ m) (point : Bool) : Subgroup (ProjectiveGroup m hm) :=
  if point then pointParabolic m hm else planeParabolic m hm

/-- Broad original extension data: only the intersection with the inner
carrier is the native endpoint. The full Borel maps remain unchanged. -/
abbrev Marking {G : Type*} [Group G] (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (L R S : Subgroup G) :=
  OriginalExtension.Marking L R S
    ((solvableResidual (endpoint m hm point)).map (endpoint m hm point).subtype)
    ((solvableResidual (endpoint m hm (!point))).map (endpoint m hm (!point)).subtype)
    (endpoint m hm point) (endpoint m hm (!point))
end OriginalUnitaryFour

namespace Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
include d h hTH hp

/-- A broad original unitary-four extension is impossible for the selected
factor with two noncentral layers. This retains all positive degrees and both
orientations, including extensions containing the degree-two graph action. -/
theorem not_original_unitaryFour_of_layer
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (m : ℕ) (hm : 1 ≤ m) (point : Bool)
    (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H)) : False := by
  let X := OriginalUnitaryFour.endpoint m hm (!point)
  let j : X →* MulAut (ProjectiveGroup m hm) := MulAut.conj.comp X.subtype
  have hj : Function.Injective j :=
    (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm).comp X.subtype_injective
  have hjrange : j.range = X.map MulAut.conj := by
    rw [MonoidHom.range_comp,range_subtype]
  have hb : j.range ≤ e.right.range := by
    rw [hjrange,←e.right_base]
    exact inf_le_left
  have hr : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map e.right ≤ j.range := by
    have he := d.original_local_eq_residual h hTH hp 1
    change R.subgroupOf _ = _ at he
    rw [he,e.right_residual,hjrange]
    exact map_mono (map_subtype_le _)
  let : Finite (ProjectiveGroup m hm) :=
    Finite.of_equiv (MatrixGroup m hm) (Extension.projectEquiv m hm).toEquiv
  apply d.not_original_right_extension_of_core_dichotomy h hp hN hl
    e.right e.right_injective j hj hb hr
  cases point
  · intro Q hQ hle
    let := hQ
    exact @UnitaryFrattini.projective_point_core_dichotomy m hm Q hQ hle
  · intro Q hQ hle
    let := hQ
    rcases @unitary_plane_core_minimal m hm Q hQ hle with hz | ht
    · left
      have hz' : Q = (⊥ : Subgroup X) := hz
      rw [hz']
      exact commutator_bot_left _
    · exact Or.inr ht
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
