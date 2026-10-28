module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Outside

/-!
# The radical bound in the fixed-preimage case

If the original displacement lies in B_c, its whole G_c-normal closure
also lies in B_c. The literal fixed-preimage criterion then proves
[[W,Q_c],Ltilde_c] ≤ Z_c for W = <Z_a^{G_c}>. This supplies the triple
bound required for the marked natural-section conclusion in the second
case of MS93 (4.4.1), claim (2), p.891. Recognition and splitting of the
remaining quotient are separate obligations.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : Geometry R}

/-- In the inside-B case, the whole span displacement lies in the same literal fixed preimage. -/
theorem span_displacement_le_B {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) (hb : 2 < geometry.b R)
    (hB : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅localZSpan R a c, Q R c⁆ ≤ B R c (geometry.Z_normal c) := by
  rw [span_commutator_eq_conjugates hc hd hb]
  apply iSup_le
  intro g
  change (⁅Z R a, Q R c⁆).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
  have hn := Escape.PairingControl.Geometry.Selection.fixedPreimage_normalized hb c hc
  have heq := mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R c).inv_mem g.property))
  exact (map_mono hB).trans heq.le

/-- This is the radical triple bound in the actual source span, with no natural-section assumption. -/
theorem span_triple_le_Z_of_displacement_le_B {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) (hb : 2 < geometry.b R)
    (hB : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c)) :
    ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  have hV : V R c ≤ stabilizer R c := (V_le_Q R hc hb).trans (fun _ hy => hy.1)
  exact ((mem_B_iff R c _ hV x).mp (span_displacement_le_B hc hd hb hB hx)).2 l hl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
