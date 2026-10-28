module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedInverter

/-!
# Neighbors for the commuting-five smallness argument

An order-five element fixing a point moves every neighbor: otherwise it
would be conjugate into the literal edge group of order4096. This provides
the moving first edge in the final J.4.10 smallness argument.

Source: Aschbacher–Smith J.4.10, printed p.445.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
open Subgroup Subgroup.CosetGeometry.RankTwo
open ChapterF.SourceCompletion.BinaryRee
open FiveHexagon.MarkedInverter
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
variable {K:Type*} [Group K] (q:Completion K)

 theorem five_element_moves_neighbor (r:K) (hr:orderOf r=5)
    (hrx:r•base q.family false=base q.family false)
    (v:q.Vertex) (hv:q.graph.Adj (base q.family false) v) : r•v≠v := by
  intro hrv
  obtain ⟨a,ha,hav⟩:=incident_common_translate q.family hv.2
  have ht:v.type=true:=by
    have hn:=hv.1
    change false≠v.type at hn
    cases he:v.type
    · exact (hn he.symm).elim
    · rfl
  change a•base q.family false=base q.family false at ha
  rw [ht] at hav
  let t:K:=a⁻¹*r*a
  have ht0:t•base q.family false=base q.family false:=by
    simp only [t,mul_smul]
    rw [ha,hrx]
    exact (congrArg (fun v=>a⁻¹•v) ha).symm.trans (inv_smul_smul a _)
  have ht1:t•base q.family true=base q.family true:=by
    simp only [t,mul_smul]
    rw [hav,hrv]
    exact (congrArg (fun v=>a⁻¹•v) hav).symm.trans (inv_smul_smul a _)
  have htm:t∈q.middle.range:=by
    rw [←q.overlap]
    constructor
    · change t∈q.family false
      rw [←Subgroup.CosetGeometry.stabilizer_base q.family false]
      exact ht0
    · change t∈q.family true
      rw [←Subgroup.CosetGeometry.stabilizer_base q.family true]
      exact ht1
  have ho:orderOf t=5:=by
    have hh:=orderOf_injective (MulAut.conj a⁻¹).toMonoidHom (MulAut.conj a⁻¹).injective r
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,hr] using hh
  let : Finite q.middle.range:=Nat.finite_of_card_ne_zero (by rw [q.middle_card];decide)
  let z:q.middle.range:=⟨t,htm⟩
  have hz:orderOf z=5:=by rw [←orderOf_coe];exact ho
  have hd:=orderOf_dvd_natCard z
  rw [hz,q.middle_card] at hd
  norm_num at hd

 theorem rotation_moves_neighbor (v:q.Vertex) (hv:q.graph.Adj (base q.family false) v) :
    q.left modelRotation•v≠v := by
  apply five_element_moves_neighbor q (q.left modelRotation) ?_ ?_ v hv
  · rw [orderOf_injective q.left q.left_injective,←orderOf_coe]
    exact rotation_order
  · change q.left modelRotation∈MulAction.stabilizer K (base q.family false)
    rw [Subgroup.CosetGeometry.stabilizer_base]
    exact ⟨modelRotation,rfl⟩
end CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
