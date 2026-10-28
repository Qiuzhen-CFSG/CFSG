module



public import CFSG.Quasithin.ChapterI.Section04To05.Residues.PolarPointResidues.Base
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.LocalCounts

/-!
# Transporting the polar residue to every original point

Conjugation identifies the base point stabilizer with the stabilizer of an
arbitrary point. The quotient actor, line and plane fibers, incidence, and
action formulas are transported along this literal group isomorphism.
Source: Aschbacher–Smith, I.5.4 and I.5.9, pp.420–422.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace PolarPointResidues
variable {G : Type*} [Group G] (S : DSystem .C3 G)

structure Mark (x : S.Point) (dual : Bool) where
  actor : MulAction.stabilizer G x →* S6
  actor_ker : actor.ker=pCore 2 (MulAction.stabilizer G x)
  actor_range : actor.range=A6 ∨ actor.range=⊤
  lines : PolarOrientation.Point dual ≃ {l : S.Line // S.Inc x l}
  planes : PolarOrientation.Line dual ≃ {π : S.Plane // S.Inc x π}
  incident : ∀ p l, S.Inc (lines p).val (planes l).val ↔ PolarOrientation.Inc dual p l
  lines_smul : ∀ (a : MulAction.stabilizer G x) p, (lines (actor a • p)).val=(a:G) • (lines p).val
  planes_smul : ∀ (a : MulAction.stabilizer G x) l, (planes (actor a • l)).val=(a:G) • (planes l).val

def pointGroupEquiv (g : G) : S.family 0 ≃* MulAction.stabilizer G (g • S.basePoint) :=
  (MulEquiv.subgroupCongr S.stabilizer_basePoint.symm).trans
    (MulAction.stabilizerEquivStabilizer (show g • S.basePoint=g • S.basePoint from rfl))

theorem pointGroupEquiv_apply (g : G) (a : S.family 0) :
    (pointGroupEquiv S g a:G)=g*(a:G)*g⁻¹ := by
  rw [pointGroupEquiv,MulEquiv.trans_apply,MulAction.stabilizerEquivStabilizer_apply]
  rfl

theorem pointGroupEquiv_symm_apply (g : G) (a : MulAction.stabilizer G (g • S.basePoint)) :
    (a:G)=g*(pointGroupEquiv S g|>.symm a:G)*g⁻¹ := by
  rw [←pointGroupEquiv_apply S g, MulEquiv.apply_symm_apply]

namespace BaseMark
variable {S} {dual : Bool} (m : BaseMark S dual)

def atTranslate (g : G) : Mark S (g • S.basePoint) dual := by
  let e := pointGroupEquiv S g
  let ep := S.incidentFiberTranslation 0 1 S.basePoint g
  let el := S.incidentFiberTranslation 0 2 S.basePoint g
  refine {
    actor := m.actor.comp e.symm.toMonoidHom
    actor_ker := ?_
    actor_range := ?_
    lines := m.lines.trans ep
    planes := m.planes.trans el
    incident := ?_
    lines_smul := ?_
    planes_smul := ?_ }
  · ext a
    change e.symm a ∈ m.actor.ker ↔ a ∈ pCore 2 (MulAction.stabilizer G (g • S.basePoint))
    rw [m.actor_ker, ←pCore_map_iso 2 e, Subgroup.mem_map_equiv]
  · rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,←MonoidHom.range_eq_map]
    exact m.actor_range
  · intro p l
    change S.Inc (g • (m.lines p).val) (g • (m.planes l).val) ↔ _
    rw [←m.incident]
    exact ⟨fun h=>by simpa only [inv_smul_smul] using h.smul S g⁻¹,fun h=>h.smul S g⟩
  · intro a p
    dsimp [e]
    change g • (m.lines (m.actor ((pointGroupEquiv S g).symm a) • p)).val=(a:G) • (g • (m.lines p).val)
    rw [m.lines_smul,pointGroupEquiv_symm_apply S g a]
    simp only [mul_smul,inv_smul_smul]
  · intro a l
    dsimp [e]
    change g • (m.planes (m.actor ((pointGroupEquiv S g).symm a) • l)).val=(a:G) • (g • (m.planes l).val)
    rw [m.planes_smul,pointGroupEquiv_symm_apply S g a]
    simp only [mul_smul,inv_smul_smul]
end BaseMark

/-- Every original C₃ point residue is the actual binary polar quadrangle or
its dual, equivariantly for the actual point-stabilizer A₆/S₆ quotient. -/
theorem exists_mark (x : S.Point) : ∃ dual : Bool, Nonempty (Mark S x dual) := by
  obtain ⟨dual,⟨m⟩⟩ := exists_baseMark S
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq G S.basePoint x
  exact ⟨dual,⟨BaseMark.atTranslate m g⟩⟩

end PolarPointResidues
end Quasithin.I5.DSystem
