module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Borel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson

/-!
# Exact Borel fixed subgroups on the original cubic graph

The Borel fixes a two-dimensional subspace of the five-dimensional binary
augmentation core. The existing lower bound from its natural quotient
therefore makes its fixed index exactly eight on either full moving cover.
For distinct Thompson choices on one edge, maximality gives an index
greater than four; divisibility forces the same index eight. Their fixed
subgroup is consequently the entire edge's fixed subgroup. Restoring the
full central attachment identifies the fixed subgroup in the whole seed
with the original edge seed.

These comparisons retain both cover orders and the cubic kernel E. They
supply a local fixed-subgroup comparison used in MS93 (5.5); the compatible
selectors, backward critical paths and terminal contradictions are separate
steps, and no core-exhaustion assertion is made here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.3)--(5.5), printed pp.915--917; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull

private def borelFixedVector (c : ZMod 2 × ZMod 2) : core (Fin 6) :=
  ⟨![c.1,c.1,c.2,c.2,c.2,c.2],by rw [mem_core]; decide +revert⟩

private theorem borelFixedVector_fixed (c : ZMod 2 × ZMod 2) :
    borelFixedVector c ∈ fixedSpace (coreRepresentation (Fin 6)) borel := by
  intro g
  change coreRepresentation (Fin 6) (g : S) (borelFixedVector c) = borelFixedVector c
  obtain ⟨i,hi⟩ := BorelCalculation.words_complete g g.property
  rw [←hi]
  have hc : ∀ i : Fin 16, ∀ c : ZMod 2 × ZMod 2,
      coreRepresentation (Fin 6) (BorelCalculation.words i) (borelFixedVector c) =
        borelFixedVector c := by decide
  exact hc i c

private theorem borel_core_fixedCodim_le :
    fixedCodim (coreRepresentation (Fin 6)) borel ≤ 3 := by
  let F := fixedSpace (coreRepresentation (Fin 6)) borel
  let f : (ZMod 2 × ZMod 2) → F := fun c => ⟨borelFixedVector c,borelFixedVector_fixed c⟩
  have hi : Function.Injective f := by
    intro c d he
    have hh := congrArg (fun v : F => (v.val : Fin 6 → ZMod 2)) he
    exact Prod.ext (congrFun hh 0) (congrFun hh 2)
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_prod,Nat.card_zmod,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hd : 2 ≤ Module.finrank (ZMod 2) F := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hc
  have he := fixedCodim_add_finrank (coreRepresentation (Fin 6)) borel
  rw [finrank_core] at he
  change fixedCodim (coreRepresentation (Fin 6)) borel + Module.finrank (ZMod 2) F = 5 at he
  omega

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem borel_radical_fixed_index (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (centralizer (Rg : Set M)).relIndex W = 8 := by
  have hn : 3 ≤ fixedCodim (naturalRepresentation (Fin 6)) borel := by
    by_contra! hlt
    have he := BorelCalculation.large_small_codim_eq_plane borel le_rfl
      (by rw [borel_order]; decide) (by omega)
    have hh := congrArg (fun A : Subgroup S => Nat.card A) he
    rw [borel_order,D_card] at hh
    contradiction
  have hb := cubic_cover_movement_bounds h e hz hk Rg
  rw [hR,fixedCodim_map_conj,fixedCodim_map_conj] at hb
  have hlo := (Nat.pow_le_pow_right (by decide : 0 < 2) hn).trans hb.1
  have hhi := hb.2.trans (Nat.pow_le_pow_right (by decide : 0 < 2) borel_core_fixedCodim_le)
  exact le_antisymm hhi hlo

include h e hz hk in
/-- The entire original Borel edge fixes index eight on either full moving cover. -/
theorem borel_edge_fixed_index (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    (centralizer (Q Rg t : Set (FreeAmalgam Rg))).relIndex (U Rg a) = 8 := by
  obtain ⟨i,hi,_,hiR,_,hiU⟩ := remaining_edge_coordinates h e hz ha hat
  rw [←hiR,←hiU,←inf_relIndex_right,inf_comm,
    map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
    inf_relIndex_left]
  exact borel_radical_fixed_index h e hz hk u hR

include h e hz hk in
/-- A distinct Thompson choice has the same exact cross-fixed index as the edge. -/
theorem borel_cross_thompson_fixed_index_eq_eight (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t) :
    (centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg))).relIndex (U Rg a) = 8 := by
  obtain ⟨Jc,_,hJc,_,hCT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hct
  have hgt := borel_cross_thompson_fixed_index h e hz hk u hR ha hc hat hct hne
  rw [hJc] at hgt ⊢
  have hd := relIndex_dvd_of_le_left (U Rg a) (centralizer_le hCT)
  rw [borel_edge_fixed_index h e hz hk u hR ha hat] at hd
  have hh : ∀ n : ℕ, n ∣ 8 → 4 < n → n = 8 := by
    intro n hn hgt
    have hle := Nat.le_of_dvd (by decide : 0 < 8) hn
    interval_cases n <;> norm_num at *
  exact hh _ hd hgt

include h e hz hk in
/-- Its fixed subgroup on the full moving cover equals the edge fixed subgroup. -/
theorem borel_cross_thompson_moving_fixed (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t) :
    U Rg a ⊓ centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg)) =
      U Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
  obtain ⟨Jc,_,hJc,_,hCT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hct
  have he := borel_cross_thompson_fixed_index_eq_eight h e hz hk u hR ha hc hat hct hne
  have ht := borel_edge_fixed_index h e hz hk u hR ha hat
  rw [hJc] at he ⊢
  let F := U Rg a ⊓ centralizer (Jc : Set (FreeAmalgam Rg))
  let E := U Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))
  have hEF : E ≤ F := inf_le_inf_left _ (centralizer_le hCT)
  have hmul := relIndex_mul_relIndex E F (U Rg a) hEF inf_le_left
  have hF : F.relIndex (U Rg a) = 8 := by
    simpa only [F,inf_relIndex_left] using he
  have hE : E.relIndex (U Rg a) = 8 := by
    simpa only [E,inf_relIndex_left] using ht
  rw [hF,hE] at hmul
  exact le_antisymm (relIndex_eq_one.mp (by omega : E.relIndex F = 1)) hEF

omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc

include h e hz hk in
/-- In the full seed, a distinct Thompson choice fixes exactly the original edge seed. -/
theorem borel_cross_thompson_seed_fixed (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t) :
    Z Rg a ⊓ centralizer (edgeOffenderJoin c t : Set (FreeAmalgam Rg)) = Z Rg t := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hseed : Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedN : Z Rg t ≤ normalizer (U Rg a : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg ha hat).trans (Z_le_stabilizer Rg a)).trans (U_normalized a)
  obtain ⟨Jc,_,hJc,_,hCT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hct
  have hm := borel_cross_thompson_moving_fixed h e hz hk u hR ha hc hat hct hne
  rw [hJc] at hm ⊢
  have hfixed : Z Rg a ⊓ centralizer (Jc : Set (FreeAmalgam Rg)) =
      Z Rg a ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    rw [vertex_seed_eq_moving_sup_edge h e hz ha hat,sup_comm (U Rg a),
      inf_centralizer_sup_of_centralizing _ _ _ hseedN (hseed.trans (centralizer_le hCT)),
      inf_centralizer_sup_of_centralizing _ _ _ hseedN hseed,hm]
  rw [hfixed]
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    rw [Z,if_neg (by simp [ht])]
    have hZX := Z_le_X_of_positive Rg a ha ((sourceGeometry h).exists_critical a ha)
      (by rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)
    have hZQt : Z Rg a ≤ Q Rg t := by
      apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a ha)
      rw [(sourceGeometry h).distance_constant a ha,
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hat)]
      exact lt_trans (by decide : 1 < 2) (distance_gt_two h e hz hk)
    exact mem_omegaCenter_iff.mpr ⟨hZQt hx,(mem_omegaCenter_iff.mp (hZX hx)).2.1,hxc⟩
  · exact le_inf (adjacent_Z_le Rg ha hat) hseed

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
