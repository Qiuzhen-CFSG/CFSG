module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.LocalAction.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.LocalAction.FixedPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Nonmoving displacement equality in MS93 (4.3.4)

The edge indices select the actual marked parabolic whose two-core is the
edge kernel. Its two-residual normalizes B: the defining commutator of B
lies in Z. Residual commutator idempotence sharpens this to the index-two
edge Z-layer. Therefore it normalizes each neighboring Z-layer contained
in B and its edge displacement.

The natural action splits the edge Z-layer into its moving four-group and
the part central in the whole vertex stabilizer. A normalized noncentral
four-group equals that moving plane. Transport through the actual amalgam
action gives the result at every oriented edge. All normalization is relative
to a finite parabolic; neither the amalgam nor its graph is assumed finite.

The imported marked-parabolic helpers concern intrinsic finite-group algebra.
No CommonFacts, CriticalEscape, or conclusions of (4.4)--(4.6) are inputs.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.3.3)--(4.3.4), printed p.886.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity.LocalAction
open DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The fixed preimage has residual commutator in the actual Z-layer. -/
private theorem B_commutator_le_Z (hb : 2 < geometry.b R) :
    ⁅B R (alpha R) (geometry.Z_normal _), Ltilde R (alpha R)⁆ ≤ Z R (alpha R) := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl x hx
  exact ((mem_B_iff R _ (geometry.Z_normal _)
    ((geometry.V_le_Q hb _ rfl).trans (fun _ hv => hv.1)) x).mp hx).2 l hl

/-- Two-perfectness sharpens the B-commutator to the index-two edge layer. -/
theorem residual_B_commutator_le_edge
    (hb : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hindex : (Z R (beta R)).relIndex (Z R (alpha R)) = 2) :
    ⁅B R (alpha R) (geometry.Z_normal _), flagResidual source i⁆ ≤ Z R (beta R) := by
  let D := B R (alpha R) (geometry.Z_normal _)
  let H := flagResidual source i
  have hHL : H ≤ Ltilde R (alpha R) := by
    rw [← flagResidual_sup source]
    cases i
    · exact le_sup_left
    · exact le_sup_right
  have hDZ : ⁅D, H⁆ ≤ Z R (alpha R) :=
    (commutator_mono le_rfl hHL).trans (B_commutator_le_Z hb)
  have hnorm : H ≤ normalizer D :=
    le_normalizer_iff_commutator_le_left.mpr (hDZ.trans (EdgeTransfer.Z_le_B hb _ rfl))
  have hDQ : D ≤ Q R (alpha R) :=
    (EdgeTransfer.B_le_radius hb _ rfl).trans (geometry.V_le_Q hb _ rfl)
  have hDP : D ≤ flagParabolic source i := hDQ.trans
    ((Q_le_adjacent_h R rfl (base_adjacent R)).trans (hkernel ▸ flagKernel_le source i))
  have hp : IsPGroup 2 D :=
    (Q_isPGroup R source.two_group source.core_le _ rfl).to_le hDQ
  rw [← flag_two_idempotent source i D hDP hp hnorm]
  apply (commutator_mono hDZ le_rfl).trans
  exact commutator_le_of_normalized_index_two _ _ _
    (EdgeTransfer.edge_Z_le _ _ rfl (base_adjacent R)) hindex
    ((flagResidual_le source i).trans ((flagParabolic_le source i).trans (Z_normalized R _)))
    ((flagResidual_le source i).trans (flagParabolic_normalizes_edge_Z source i hkernel))

/-- The actual selected edge residual normalizes the neighboring displacement. -/
theorem nonmoving_displacement_normalized
    (hb : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hindex : (Z R (beta R)).relIndex (Z R (alpha R)) = 2)
    (d : Vertex R) (hdt : Adjacent R d (beta R))
    (hB : Z R d ≤ B R (alpha R) (geometry.Z_normal _)) :
    flagResidual source i ≤ normalizer (edgeDisplacement d (beta R)) := by
  have hd := neighbor_color (show color R (alpha R) = false from rfl) (base_adjacent R) hdt
  have hnZ : flagResidual source i ≤ normalizer (Z R d) :=
    le_normalizer_iff_commutator_le_left.mpr (((commutator_mono hB le_rfl).trans
      (residual_B_commutator_le_edge hb i hkernel hindex)).trans
      (EdgeTransfer.edge_Z_le d _ hd hdt))
  have hnQ : flagResidual source i ≤ normalizer (Q R (beta R)) := by
    rw [← hkernel]
    exact (flagResidual_le source i).trans (flagKernel_normalized source i)
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, edgeDisplacement, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hnZ hg),
    mem_normalizer_iff_map_conj_eq.mp (hnQ hg)]

/-- At the base edge, the noncentral invariant four-group is the natural plane. -/
theorem nonmoving_displacement_eq_base
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (d : Vertex R) (hdt : Adjacent R d (beta R))
    (hB : Z R d ≤ B R (alpha R) (geometry.Z_normal _))
    (hn : ¬ edgeDisplacement d (beta R) ≤ localCenter (alpha R)) :
    edgeDisplacement d (beta R) = edgeDisplacement (alpha R) (beta R) := by
  have hindices := edge_indices hb modules p initial control edge _ _ rfl (base_adjacent R)
  obtain ⟨i, hi⟩ := select_flag_kernel source geometry modules hindices.1 hindices.2
  have hz := edge_le_Z p hb control edge _ _ rfl (base_adjacent R)
  have hcard := edge_card p (by omega) initial (alpha R) (beta R) rfl (base_adjacent R)
  obtain ⟨hmove, hfixed⟩ := edgeFixedLayerAction source geometry hb modules hz hcard hindices.1 i hi
  let D := edgeDisplacement d (beta R)
  let H := flagResidual source i
  have hd := neighbor_color (show color R (alpha R) = false from rfl) (base_adjacent R) hdt
  have hDZ : D ≤ Z R (beta R) := edge_le_Z p hb control edge d _ hd hdt
  have hDcard : Nat.card D = 4 := edge_card p (by omega) initial d _ hd hdt
  have hnorm : H ≤ normalizer D := nonmoving_displacement_normalized hb i hi hindices.1 d hdt hB
  have hDP : D ≤ flagParabolic source i :=
    (hDZ.trans (show Z R (beta R) ≤ Q R (beta R) from omegaCenter_le _)).trans
      (hi ▸ flagKernel_le source i)
  have hne : ⁅D,H⁆ ≠ ⊥ := by
    intro heq
    exact hn ((le_inf hDZ (commutator_eq_bot_iff_le_centralizer.mp heq)).trans hfixed)
  have hidem := flag_two_idempotent source i D hDP (IsPGroup.of_card (n := 2) hDcard) hnorm
  have heq := (MarkedAction.moving_four_fixed_free D D H hDcard hnorm
    (le_normalizer_iff_commutator_le_left.mp hnorm) hne hidem).1
  have hle : D ≤ edgeDisplacement (alpha R) (beta R) := by
    change ⁅Z R (beta R), H⁆ = edgeDisplacement (alpha R) (beta R) at hmove
    rw [← hmove, ← heq]
    exact commutator_mono hDZ le_rfl
  let : Finite (edgeDisplacement (alpha R) (beta R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact eq_of_le_of_card_ge hle (by rw [hDcard, hcard])

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity.LocalAction

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- MS93 (4.3.4), middle local-action step: a noncentral displacement from
an unmoving neighbor is the original edge displacement. All residual action
and normalization premises are constructed from the preceding witnesses. -/
theorem nonmoving_displacement_eq
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (_transfer : NormalizationTransfer R) (p : Counterexample geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a t d : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (hdt : Adjacent R d t) (hB : Z R d ≤ B R a (geometry.Z_normal a))
    (hn : ¬ edgeDisplacement d t ≤ localCenter a) :
    edgeDisplacement d t = edgeDisplacement a t := by
  obtain ⟨g, hga, hgt⟩ := exists_edge_transport ha
    (show color R (alpha R) = false from rfl) hat (base_adjacent R)
  change act R g t = beta R at hgt
  have hd : Adjacent R (act R g d) (beta R) :=
    hgt ▸ (adjacent_act_iff R g d t).mpr hdt
  have hB' : Z R (act R g d) ≤ B R (alpha R) (geometry.Z_normal _) := by
    rw [← hga, PairingControl.FirstPairing.B_act hb g a ha, Z_act]
    exact map_mono hB
  have hcenter : localCenter (act R g a) =
      (localCenter a).map (MulAut.conj g⁻¹).toMonoidHom := by
    unfold localCenter
    rw [stabilizer_act, ← DistanceFour.Flags.RankOne.centerImage_map]
  have hn' : ¬ edgeDisplacement (act R g d) (beta R) ≤ localCenter (alpha R) := by
    rw [← hga, ← hgt, hcenter, PairingControl.FirstPairing.edgeDisplacement_act,
      map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
    exact hn
  have heq := LocalAction.nonmoving_displacement_eq_base hb modules p initial control edge
    (act R g d) hd hB' hn'
  rw [← hga, ← hgt, PairingControl.FirstPairing.edgeDisplacement_act,
    PairingControl.FirstPairing.edgeDisplacement_act] at heq
  exact (Subgroup.map_injective (MulAut.conj g⁻¹).injective) heq

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity
