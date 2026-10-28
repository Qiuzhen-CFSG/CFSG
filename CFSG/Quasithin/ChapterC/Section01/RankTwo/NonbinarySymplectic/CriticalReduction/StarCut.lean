module
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.OuterRemoval

/-!
# The remaining star inclusion suffices for outer removal

The moving natural layer centralizes the local core, and the fixed core is
normalized by the vertex stabilizer. Consequently every subgroup of their
join has core displacement inside the fixed core. This discharges the second
premise of the existing cut theorem from the first star inclusion itself.

The actual characteristic-replacement consumer therefore requires only
Z-star-beta <= U-alpha D-alpha. That inclusion, and the subsequent Section 5
large-distance exclusion, remain separate source obligations.
Source: MS93 (3.4), final paragraph, p.869, and Section 7, p.933.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-- No additional star displacement estimate is needed once the star lies
in the join of the moving layer and the full fixed core. -/
theorem star_core_commutator_le_fixed_of_le
    {M : Type*} [Group M] [Finite M] (R : Subgroup M) {a : Vertex R}
    (ha : color R a = false) (S : Subgroup (FreeAmalgam R))
    (hS : S ≤ U R a ⊔ fixedCore R a) :
    ⁅S,Q R a⁆ ≤ fixedCore R a := by
  have hD : stabilizer R a ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
    have hQ : (Q R a).map (MulAut.conj g).toMonoidHom = Q R a := by
      simpa only [hga,inv_inv] using (Q_act R g⁻¹ a).symm
    have hL : (Ltilde R a).map (MulAut.conj g).toMonoidHom = Ltilde R a := by
      simpa only [hga,inv_inv] using (Ltilde_act R g⁻¹ a).symm
    have hh := map_inf_centralizer_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective (Q R a) (Ltilde R a)
    rw [hQ,hL] at hh
    exact hh.symm
  apply (commutator_mono hS le_rfl).trans
  apply commutator_sup_le_of_relative_normal (stabilizer R a) (U R a) (fixedCore R a)
    (Q R a) (fixedCore R a) hD
    ((U_le_Z a).trans (Z_le_stabilizer R a)) (fun _ hx => hx.1.1)
  · exact (commutator_mono (U_le_Z a) le_rfl).trans_eq (Z_centralizes_Q R a ha)
      |>.trans bot_le
  · exact le_normalizer_iff_commutator_le_left.mp
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans hD)

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual outer-removal consumer with its displacement premise derived;
only the star's moving-plus-fixed inclusion remains to be supplied. -/
theorem Input.replacement_inner_of_seed_star_inclusion
    (P : Sylow 2 (Ltilde d.radical (alpha d.radical))) (Y : Subgroup d.radical)
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hZ : ((starSpan d.radical Y).map d.radical.subtype).map (embedM d.radical) ≤
      U d.radical (alpha d.radical) ⊔ fixedCore d.radical (alpha d.radical)) :
    K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤ := by
  apply h.replacement_inner_of_seed_star_bounds d P Y hY hZ
  exact (commutator_mono le_rfl inf_le_right).trans
    (star_core_commutator_le_fixed_of_le d.radical rfl _ hZ)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
