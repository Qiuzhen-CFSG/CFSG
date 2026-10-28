module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.Marked

/-!
# The original V-plane and its opposite span U

MarkedSpans supplies representatives in the original V of every vector on
the marked F₄-line. A Weyl lift exchanges the two natural coordinate lines.
Their representatives therefore generate U modulo the original U₀. With
U₀=V₁≤V, the remaining kernel lies in the same join, proving the literal
ambient equality V∨Vⁿ=U. The conjugation Vⁿ is n⁻¹Vn.

The upper marking and local actors are the compatible earlier qt-14-03/
qt-14-07 data. Module separation is 14.7.2(1), and action descent uses
14.5.15(4). This proof makes no rechoice of the critical path or quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.64–65, printed pp.1069–1070, and 14.7.72, printed p.1076.
-/

public section
noncomputable section
open Subgroup Representation Matrix.SpecialLinearGroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

open SourceEndgame.ChiefFactors

private theorem seed_preimages (hc : d.SectionCentralizer)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : MarkedSpans.LocalActors d)
    (a : SL2FourNatural.F) :
    ∃ v : F.U, (v : G) ∈ V ∧ (naturalMap d v).toAdd = ![a, 0] := by
  let s : d.ActionDescent := {
    action := d.descendedAction hc
    original := d.descendedAction_apply hc }
  let w := MarkedSpans.cover d s (MarkedPartitions.point 0 a)
  have hw : w ∈ Rechoice.LocalGeometry.tilde d V := by
    rw [MarkedSpans.seed_eq_marked d s mark sep actors]
    exact ⟨a, rfl⟩
  obtain ⟨v, hv, hcoord⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
  refine ⟨v, hv, ?_⟩
  change d.projection (d.conjugationSection.coordinates v).toAdd = _
  rw [hcoord]
  exact (MarkedSpans.cover_projection d s (MarkedPartitions.point 0 a)).trans
    (MarkedPartitions.point_projection 0 a)

/-- A lift of the original Weyl matrix carries V to an opposite plane.
The conjugation here is literally the source right conjugation n⁻¹Vn. -/
theorem opposite_span (hc : d.SectionCentralizer)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : MarkedSpans.LocalActors d)
    (hU0 : d.U₀ = F.Vi 1) (n : F.H)
    (hn : d.qH n = alternatingActor d.naturalQuotient weyl) :
    V ⊔ conjugate V (n : G) = F.U := by
  let B := V ⊔ conjugate V (n : G)
  have hVU := Data.V_le_U F
  have hconjU : conjugate V (n : G) ≤ F.U := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_normalizer_iff.mp (d.conjugationSection.normalized n⁻¹.property) v).mp (hVU hv)
  have hBU : B ≤ F.U := sup_le hVU hconjU
  apply le_antisymm hBU
  intro u hu
  let x : F.U := ⟨u, hu⟩
  obtain ⟨v, hv, hfv⟩ := seed_preimages d hc mark sep actors ((naturalMap d x).toAdd 0)
  obtain ⟨w, hw, hfw⟩ := seed_preimages d hc mark sep actors ((naturalMap d x).toAdd 1)
  let w' : F.U := ⟨((n⁻¹ : F.H) : G) * w * ((n⁻¹ : F.H) : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized n⁻¹.property) w).mp w.property⟩
  have hw' : (w' : G) ∈ conjugate V (n : G) :=
    mem_map_of_mem (MulAut.conj (n : G)⁻¹).toMonoidHom hw
  have hfw' : (naturalMap d w').toAdd = ![0, (naturalMap d x).toAdd 1] := by
    have hh := (naturalSection d).equivariant n⁻¹ w
    change (naturalMap d w').toAdd = d.naturalQuotient.action (d.qH n⁻¹)
      (naturalMap d w).toAdd at hh
    rw [map_inv, hn, ← map_inv, weyl_inv, hfw] at hh
    exact hh.trans ((d.naturalQuotient.restriction _ _).trans (by
      rw [weyl_action]
      rfl))
  have hprod : naturalMap d (v * w') = naturalMap d x := by
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    change (naturalMap d v).toAdd + (naturalMap d w').toAdd = _
    rw [hfv, hfw']
    funext i
    fin_cases i <;> simp
  let z := x * (v * w')⁻¹
  have hz : naturalMap d z = 1 := by
    dsimp only [z]
    rw [map_mul, map_inv, hprod, mul_inv_cancel]
  have hz0 : (z : G) ∈ d.U₀ := ((naturalSection d).coordinates_eq_one_iff z).mp hz
  have hzB : (z : G) ∈ B := Subgroup.mem_sup_left (F.le_seed 1 (hU0 ▸ hz0))
  have hprodB : ((v * w' : F.U) : G) ∈ B := B.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hw')
  have hm := B.mul_mem hzB hprodB
  simpa only [z, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right] using hm


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
