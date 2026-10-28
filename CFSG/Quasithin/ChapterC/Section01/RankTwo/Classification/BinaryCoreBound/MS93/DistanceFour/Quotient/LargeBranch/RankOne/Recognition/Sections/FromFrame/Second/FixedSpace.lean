module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Second.Geometry
public import Theory.ThreeSubgroups

/-!
# Cubic fixed-space reduction for the literal second section

The residual acts trivially on `(Z_c Z_alpha)/Z_alpha`. For a subgroup T
whose displacement generates `Q_beta/Q_alpha`, the relative three-subgroups
lemma shows that an element of K fixed by T modulo Z_alpha commutes with
Q_beta modulo Z_alpha. Thus its actual commutator preimage is contained in Y.
This is the commutator form of the source pairing argument.

For an actual subgroup of order three, summing its conjugate vectors lifts
invariants through the literal quotient `(K/Z_alpha)/(Y/Z_alpha)`: the
sum has the same quotient image because three equals one in characteristic
two. The ambient action and exact projection kernel then apply the preceding
fixed-preimage inclusion. The conditional theorems in this module explicitly
retain the cubic edge-movement premise. `FromFrame.Second` discharges it
using the marked-model proof in `Second.CubicEdge`; the final natural-module
construction remains with the FromFrame owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(2), printed p.910.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections

private theorem mem_commutatorPreimage_of {G : Type*} [Group G]
    (K A Z : Subgroup G) (hn : K ≤ normalizer Z) (x : G) (hx : x ∈ K)
    (hc : ∀ a ∈ A, ⁅x,a⁆ ∈ Z) : x ∈ commutatorPreimage K A Z := by
  let D : Subgroup G := {
    carrier := {x | x ∈ K ∧ ∀ a ∈ A, ⁅x,a⁆ ∈ Z}
    one_mem' := ⟨K.one_mem, by simp⟩
    mul_mem' := by
      rintro x y ⟨hx,hxc⟩ ⟨hy,hyc⟩
      refine ⟨K.mul_mem hx hy, fun a ha => ?_⟩
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact Z.mul_mem (le_normalizer_iff.mp hn x hx _ (hyc a ha)) (hxc a ha)
    inv_mem' := by
      rintro x ⟨hx,hxc⟩
      refine ⟨K.inv_mem hx, fun a ha => ?_⟩
      rw [commutatorElement_inv_left]
      have hh : ⁅a,x⁆ ∈ Z := by
        rw [← commutatorElement_inv]
        exact Z.inv_mem (hxc a ha)
      simpa only [inv_inv] using le_normalizer_iff.mp hn x⁻¹ (K.inv_mem hx) _ hh }
  exact (le_commutatorPreimage (show D ≤ K from fun _ h => h.1)
    (commutator_le.mpr fun _ h => h.2)) ⟨hx,hc⟩

private theorem cubic_quotient_invariants {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (N : Subrepresentation ρ) (T : Subgroup G) (hT : Nat.card T = 3)
    (hfixed : Representation.invariants (ρ.comp T.subtype) ≤ N.toSubmodule) :
    Representation.invariants N.quotientRepresentation = ⊥ := by
  classical
  let : Finite T := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype T := Fintype.ofFinite T
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨v, rfl⟩ := N.toSubmodule.mkQ_surjective z
  let w : V := ∑ t : T, ρ t v
  have hw : w ∈ Representation.invariants (ρ.comp T.subtype) := by
    intro t
    change ρ (t : G) (∑ a : T, ρ a v) = ∑ a : T, ρ a v
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft t) _ _ (fun _ => rfl)
  have he : N.toSubmodule.mkQ w = N.toSubmodule.mkQ v := by
    change N.toSubmodule.mkQ (∑ t : T, ρ t v) = _
    rw [map_sum]
    have ht (t : T) : N.toSubmodule.mkQ (ρ t v) = N.toSubmodule.mkQ v := hz t
    simp only [ht, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, hT, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
    change (3 : ZMod 2) • N.toSubmodule.mkQ v = N.toSubmodule.mkQ v
    rw [show (3 : ZMod 2) = 1 by decide, one_smul]
  rw [← he]
  exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr (hfixed hw)

open Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
  (f : Frame source) (hb : geometry.b R = 4) (s : CriticalSegment geometry)
  (hbc : Adjacent R (beta R) s.middle)

include common radius f hbc in
/-- The original residual fixes the codomain of the source commutator pairing. -/
theorem midpoint_sup_commutator_residual_le_Z :
    ⁅Z R s.middle ⊔ Z R (alpha R), flagResidual source f.orientation⁆ ≤ Z R (alpha R) := by
  have hZcV : Z R s.middle ≤ V R (alpha R) :=
    le_iSup_of_le s.middle (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, s.first_distance]) le_rfl)
  have hpre : Z R s.middle ⊔ Z R (alpha R) ≤
      commutatorPreimage (stabilizer R (alpha R)) (flagResidual source f.orientation)
        (Z R (alpha R)) := by
    apply sup_le
    · exact le_commutatorPreimage
        (hZcV.trans (geometry.V_local _ rfl common.large_distance))
        (residual_commutator_le_Z common radius f hbc)
    · apply le_commutatorPreimage (Z_le_stabilizer R _)
      exact le_normalizer_iff_commutator_le_left.mp
        (((flagResidual_le source f.orientation).trans (flagParabolic_le source f.orientation)).trans
          (Z_normalized R _))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (Z_normalized R _))

include common radius f hb hbc in
/-- Full cubic displacement on the actual edge quotient gives the source fixed-preimage inclusion. -/
theorem cubic_fixedPreimage_le_of_edge_movement
    (T : Subgroup (flagResidual source f.orientation))
    (hmove : ⁅Q R (beta R), T.map (flagResidual source f.orientation).subtype⁆ ⊔
      Q R (alpha R) = Q R (beta R)) :
    commutatorPreimage (intersection s.middle)
      (T.map (flagResidual source f.orientation).subtype) (Z R (alpha R)) ≤
        fixedPreimage s.middle := by
  let A := T.map (flagResidual source f.orientation).subtype
  let C := commutatorPreimage (intersection s.middle) A (Z R (alpha R))
  have hCK : C ≤ intersection s.middle := commutatorPreimage_le _ _ _
  have hKN : intersection s.middle ≤ normalizer (Z R (alpha R)) :=
    inf_le_left.trans ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _))
  have hQN : Q R (beta R) ≤ normalizer (Z R (alpha R)) :=
    (show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Z_normalized R _)
  have hAN : A ≤ normalizer (Z R (alpha R)) :=
    (map_subtype_le _).trans (((flagResidual_le source f.orientation).trans
      (flagParabolic_le source f.orientation)).trans (Z_normalized R _))
  have htriple : ⁅⁅Q R (beta R), A⁆, C⁆ ≤ Z R (alpha R) := by
    apply commutator_commutator_le_of_rotate_of_le_normalizer hQN hAN (hCK.trans hKN)
    · rw [commutator_comm A C]
      exact (commutator_mono (commutator_commutatorPreimage_le _ _ _ hKN) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hQN)
    · exact (commutator_mono
        ((commutator_mono hCK le_rfl).trans
          (intersection_commutator_edge_le_sup common radius f hb s hbc))
        (map_subtype_le _)).trans (midpoint_sup_commutator_residual_le_Z common radius f s hbc)
  have hpre : Q R (beta R) ≤ commutatorPreimage (Q R (beta R)) C (Z R (alpha R)) := by
    rw [← hmove]
    apply sup_le
    · exact le_commutatorPreimage le_sup_left htriple
    · apply le_commutatorPreimage le_sup_right
      rw [commutator_comm]
      exact (commutator_mono (hCK.trans inf_le_left) le_rfl).trans
        (radius.toEarlyFacts.commutator_le_Z _ rfl)
  apply le_commutatorPreimage hCK
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hQN)

/-- Averaging over the supplied actual subgroup of order three kills invariants of the literal second section. -/
theorem secondRepresentation_invariants_eq_bot_of_cubic_fixedPreimage
    (T : Subgroup (flagResidual source f.orientation)) (hT : Nat.card T = 3)
    (hfixed : commutatorPreimage (intersection s.middle)
      (T.map (flagResidual source f.orientation).subtype) (Z R (alpha R)) ≤
        fixedPreimage s.middle)
    (d : LayerModule source (V R (alpha R))) :
    Representation.invariants (secondRepresentation common radius f s hbc d) = ⊥ := by
  let A := rankOne (parabolic source.projection source.flag f.orientation)
  have hS : A.map (embedM R) ≤ normalizer (V R (alpha R)) :=
    (flagResidual_le source f.orientation).trans
      ((flagParabolic_le source f.orientation).trans (DistanceEight.V_normalized R _))
  have hK : A.map (embedM R) ≤ normalizer (intersection s.middle) :=
    residual_normalizes_intersection common radius f s.first_distance hbc
  have hY : A.map (embedM R) ≤ normalizer (fixedPreimage s.middle) :=
    residual_normalizes_fixedPreimage common radius f s.first_distance hbc
  let e := (residualEquiv source f.orientation).symm.toMonoidHom
  let W := d.invariantSubspace A (intersection s.middle) hS hK
  let ρ := W.toRepresentation.comp e
  let N0 := d.invariantSection A (intersection s.middle) (fixedPreimage s.middle) hS hK hY
  let N : Subrepresentation ρ := {
    toSubmodule := N0.toSubmodule
    apply_mem_toSubmodule g := N0.apply_mem_toSubmodule (e g) }
  change Representation.invariants N.quotientRepresentation = ⊥
  apply cubic_quotient_invariants ρ N T hT
  intro v hv
  obtain ⟨k, hk⟩ := d.subspaceMap_surjective (intersection s.middle) inf_le_left
    (Multiplicative.ofAdd v)
  have hval : (d.projection (inclusion inf_le_left k)).toAdd = (v : d.Space) :=
    congrArg (fun u : Multiplicative (d.subspace (intersection s.middle)) => (u.toAdd : d.Space)) hk
  have hKN : intersection s.middle ≤ normalizer (Z R (alpha R)) :=
    inf_le_left.trans ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _))
  have hkC : (k : FreeAmalgam R) ∈ commutatorPreimage (intersection s.middle)
      (T.map (flagResidual source f.orientation).subtype) (Z R (alpha R)) := by
    apply mem_commutatorPreimage_of _ _ _ hKN _ k.property
    rintro a ⟨t, ht, rfl⟩
    let m : A := e t
    have hv' := congrArg (fun u : d.subspace (intersection s.middle) => (u : d.Space)) (hv ⟨t,ht⟩)
    have hp : d.representation (source.projection m) (d.projection (inclusion inf_le_left k)).toAdd =
        (d.projection (inclusion inf_le_left k)).toAdd := by
      rw [hval]
      exact hv'
    have hc := (d.fixed_iff_commutator_mem m
      (hS (mem_map_of_mem _ m.property)) (inclusion inf_le_left k)).mp hp
    change ⁅embedM R ((residualEquiv source f.orientation).symm t), (k : FreeAmalgam R)⁆ ∈
      Z R (alpha R) at hc
    rw [residualEquiv_symm_apply] at hc
    rw [← commutatorElement_inv]
    exact (Z R (alpha R)).inv_mem hc
  change (v : d.Space) ∈ d.subspace (fixedPreimage s.middle)
  rw [← hval]
  exact (d.projection_mem_subspace_iff (fixedPreimage s.middle)
    (Z_le_fixedPreimage common s.first_distance) _).mpr (hfixed hkC)

include hb in
/-- The remaining marked edge-movement premise suffices for second-section vanishing. -/
theorem secondRepresentation_invariants_eq_bot_of_edge_movement
    (T : Subgroup (flagResidual source f.orientation)) (hT : Nat.card T = 3)
    (hmove : ⁅Q R (beta R), T.map (flagResidual source f.orientation).subtype⁆ ⊔
      Q R (alpha R) = Q R (beta R))
    (d : LayerModule source (V R (alpha R))) :
    Representation.invariants (secondRepresentation common radius f s hbc d) = ⊥ :=
  secondRepresentation_invariants_eq_bot_of_cubic_fixedPreimage common radius f s hbc T hT
    (cubic_fixedPreimage_le_of_edge_movement common radius f hb s hbc T hmove) d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
