module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFixedTransfer
public import Theory.ThreeSubgroups

/-!
# The full fixed preimage centralizes the moved radius

In the actual fixed-radius branch, [V_a,B_a] lies in D_a and hence
centralizes L_a. The definition of the full fixed preimage gives
[B_a,L_a] <= Z_a, which centralizes V_a <= Q_a. The three-subgroups
lemma therefore makes B_a centralize the full Vcirc_a = [V_a,L_a].

This is the kernel-centrality step of MS93 (3.10)(i), printed p.880,
as used in (5.12)(2), printed p.926. The full B_a and D_a are retained.
No natural-action, splitting or central-kernel premise is imposed.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

/-- Under the literal fixed-radius branch, the whole original fixed
preimage centralizes the whole original moved radius. -/
theorem radius_moving_centralizes_full_B
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a=false)
    (hfixed : ⁅V R a,Q R a⁆ ≤ fixedCore R a) :
    ⁅Vcirc R a,B R a (geometry.Z_normal a)⁆ = ⊥ := by
  let D := B R a (geometry.Z_normal a)
  have hVQ := geometry.V_le_Q hb a ha
  have hVS : V R a ≤ stabilizer R a := hVQ.trans (fun _ hx => hx.1)
  have hDV : D ≤ V R a := fun x hx =>
    ((mem_B_iff R a (geometry.Z_normal a) hVS x).mp hx).1
  have hDL : ⁅D,Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a) hVS x).mp hx).2 l hl
  have hLDV : ⁅⁅Ltilde R a,D⁆,V R a⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [commutator_comm (Ltilde R a)]
    exact (commutator_mono hDL hVQ).trans_eq (Z_centralizes_Q R a ha)
  have hDVL : ⁅⁅D,V R a⁆,Ltilde R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hDV hVQ).trans hfixed).trans inf_le_right)
  exact commutator_commutator_eq_bot_of_rotate hLDV hDVL

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
