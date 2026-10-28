module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.NativeRestriction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveField
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryFive
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveNative

/-!
# Original unitary-five residual and parameter restrictions

The full native line endpoint embeds through its original marked extension,
so the existing quasithin obstruction forces q=4 before any extension
collapse. Restricting the original residual maps identifies their canonical
quotients with the native SU₃(4) and PSL₂(16) quotients. Consequently the
faithful left factor occupies the plane endpoint, n=4, and the right factor
has the SU₃(4) quotient. A diagram-selected right factor with binary PSL₂
quotient is therefore impossible, in either original orientation.

The general-parameter field filter takes the faithful native inner embedding
explicitly. At q=4 its faithfulness is supplied by the proved native theorem.
All markings retain the entire common Borel. No pure comparison, desired
core identity, S=T, or equality R=O²(H) is assumed. Original extension collapse
and whole-residual completion remain separate duties of the same owner.

Source: Aschbacher--Smith F.1.12(I)(7) and its proof, pp.263--264, and 5.2.6,
pp.650--651 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalUnitaryFive
open ChapterF.GreenBook.UnitaryFive

/-- The actual unitary-five endpoints before field filtering. -/
@[expose] def endpoint {q : ℕ} (M : Model q) (line : Bool) : Subgroup M.Carrier :=
  if line then M.leftParabolic else M.rightParabolic

/-- The native residual and full inner endpoint are marked separately;
outer endpoint elements and the entire common Borel are retained. -/
abbrev Marking {G : Type*} [Group G] {q : ℕ} (M : Model q) (line : Bool)
    (L R S : Subgroup G) :=
  OriginalExtension.Marking L R S
    ((solvableResidual (endpoint M line)).map (endpoint M line).subtype)
    ((solvableResidual (endpoint M (!line))).map (endpoint M (!line)).subtype)
    (endpoint M line) (endpoint M (!line))
end OriginalUnitaryFive

namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)

include h in
/-- The earlier embedding obstruction applies to the original native base,
before outer collapse and in either endpoint orientation. -/
theorem original_unitaryFive_marked_field
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q) (line : Bool)
    (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
    (e : OriginalUnitaryFive.Marking M line L R (sourceS L H)) : q = 4 := by
  let j : M.leftParabolic →* MulAut M.Carrier := MulAut.conj.comp M.leftParabolic.subtype
  have hj : Function.Injective j := hi.comp M.leftParabolic.subtype_injective
  have hjrange : j.range = M.leftParabolic.map MulAut.conj := by
    rw [MonoidHom.range_comp,range_subtype]
  cases line
  · apply original_unitaryFive_extension_field h hq heven M 1 e.right e.right_injective j hj
    rw [hjrange]
    exact e.right_base.symm.le.trans inf_le_left
  · apply original_unitaryFive_extension_field h hq heven M 0 e.left e.left_injective j hj
    rw [hjrange]
    exact e.left_base.symm.le.trans inf_le_left

/-- Restrict the literal source residual to the marked native line residual. -/
def originalUnitaryFiveLineEquiv (M : Model 4) (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* MulAut M.Carrier)
    (hf : Function.Injective f)
    (hr : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
      ((solvableResidual M.leftParabolic).map M.leftParabolic.subtype).map MulAut.conj) :
    ![L,R] i ≃* M.leftLocalImage := by
  let j : M.leftParabolic →* MulAut M.Carrier := MulAut.conj.comp M.leftParabolic.subtype
  have hj : Function.Injective j :=
    (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective M.form
      M.local_field_card M.conjugation M.matrix).comp M.leftParabolic.subtype_injective
  have hr' : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
      (solvableResidual M.leftParabolic).map j := by
    rw [hr,map_map]
  exact (d.originalEndpointResidualEquiv h hTH hp i f hf j hj hr').trans M.leftLocalImageEquiv

include d h hTH hp in
/-- A binary PSL₂ source quotient cannot occupy the original U₅(4) line
endpoint, even when the endpoint has additional outer automorphisms. -/
theorem not_original_unitaryFive_line
    (M : Model 4) (i : Fin 2) {f₀ : ℕ}
    (hlin : ClassicalGroup.IsPSL (![L,R] i ⧸ pCore 2 (![L,R] i)) 2 (2^f₀))
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* MulAut M.Carrier)
    (hf : Function.Injective f)
    (hr : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
      ((solvableResidual M.leftParabolic).map M.leftParabolic.subtype).map MulAut.conj) : False := by
  let a := d.originalUnitaryFiveLineEquiv h hTH hp M i f hf hr
  let q := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  apply binary_quotient_not_special_unitary hlin (m := 2) (by decide)
  obtain ⟨F,iF,iFin,J,hF,hJ,⟨b⟩⟩ := M.source_quotient_models.1
  exact ⟨F,iF,iFin,J,hF,hJ,⟨q.trans b⟩⟩

include d h hTH hp in
/-- The original faithful left factor forces the plane-first orientation,
without assuming a pure-amalgam comparison. -/
theorem original_unitaryFive_marked_orientation
    (M : Model 4) (line : Bool)
    (e : OriginalUnitaryFive.Marking M line L R (sourceS L H)) : line = false := by
  cases line
  · rfl
  · exact (d.not_original_unitaryFive_line h hTH hp M 0 h.linear
      e.left e.left_injective e.left_residual).elim

include d h hTH hp in
/-- Both marked original U₅ orientations are excluded for a diagram factor
with binary PSL₂ quotient. The unrestricted whole-residual row is retained. -/
theorem not_original_unitaryFive_of_binary_right
    {f : ℕ} (hlin : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f))
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q) (line : Bool)
    (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
    (e : OriginalUnitaryFive.Marking M line L R (sourceS L H)) : False := by
  have hq4 := original_unitaryFive_marked_field h hq heven M line hi e
  subst q
  have hline := d.original_unitaryFive_marked_orientation h hTH hp M line e
  subst line
  exact d.not_original_unitaryFive_line h hTH hp M 1 hlin
    e.right e.right_injective e.right_residual
end Preparation
namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
include d h hTH hp

/-- The original plane residual fixes n = 4 before the U₅ extension is
removed. The right source quotient is the literal SU₃(4) quotient. -/
theorem original_unitaryFive_marked_parameters
    (M : Model 4) (line : Bool)
    (e : OriginalUnitaryFive.Marking M line L R (sourceS L H)) :
    n = 4 ∧ ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 := by
  have hline := d.original_unitaryFive_marked_orientation h hTH hp M line e
  subst line
  let j : M.rightParabolic →* MulAut M.Carrier := MulAut.conj.comp M.rightParabolic.subtype
  have hj : Function.Injective j :=
    (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective M.form
      M.local_field_card M.conjugation M.matrix).comp M.rightParabolic.subtype_injective
  have hr : (solvableResidual (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)).map e.left =
      (solvableResidual M.rightParabolic).map j := by
    rw [e.left_residual,map_map]
    rfl
  let a : L ≃* M.rightLocalImage :=
    (d.originalEndpointResidualEquiv h hTH hp 0 e.left e.left_injective j hj hr).trans
      M.rightLocalImageEquiv
  let b := d.originalUnitaryFiveLineEquiv h hTH hp M 1 e.right e.right_injective e.right_residual
  let aQ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let bQ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  constructor
  · obtain ⟨F,_,_,hF,⟨c⟩⟩ := h.linear
    obtain ⟨E,_,_,hE,⟨g⟩⟩ := M.source_quotient_models.2
    let := Fintype.ofFinite F
    let := Fintype.ofFinite E
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4)
      (by simpa only [Nat.card_eq_fintype_card, Nat.reducePow] using hE)
    have hc := binary_psl_field_card_eq (c.symm.trans (aQ.trans g))
    rw [hF,hE] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc
  · obtain ⟨F,iF,iFin,J,hF,hJ,⟨c⟩⟩ := M.source_quotient_models.1
    exact ⟨F,iF,iFin,J,hF,hJ,⟨bQ.trans c⟩⟩
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
