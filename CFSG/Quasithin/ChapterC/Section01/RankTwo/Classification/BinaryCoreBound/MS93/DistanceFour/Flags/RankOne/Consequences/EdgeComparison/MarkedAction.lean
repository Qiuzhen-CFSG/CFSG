module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison.MarkedAction.Core
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison.MarkedAction.Algebra

/-!
# The marked moving plane and central fixed layer

The natural subgroup U_alpha has order eight through its actual NaturalU
isomorphism. The source edge commutator has order four and lies in both
U_alpha and Z_beta. The edge fixed-subgroup identity and nontriviality then
identify it exactly with U_alpha intersect Z_beta. The supplied splitting of
Z_alpha gives Z_beta as this plane joined with the summand central in the
whole vertex stabilizer.

The intrinsic marked parabolic core lies in its source-ordered residual
modulo Q_alpha. Consequently the residual acts nontrivially on U_alpha.
The index-two quotient puts its displacement in the identified plane;
finite-parabolic commutator idempotence makes that displacement the whole
plane and excludes nonidentity fixed points there. Thus the fixed part in
Z_beta is central in the whole stabilizer.

This argument retains both literal flag orientations and the arbitrary
NaturalU marking. It needs no choice of coordinates beyond the genuine
natural carrier, and uses no FlagControl, Bzero equality, edge comparison,
core containment or radius conclusion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the rank-one step in (4.6.9), printed p.908; flag notation pp.905--907.
These are precisely the two conditional action facts needed by the separate
edge-generator comparison assembly.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem central_split (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) :
    Z R (alpha R) = U R (alpha R) ⊔
      (Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))) := by
  let s : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  exact s.decomposition_at (alpha R) rfl

private theorem Z_alpha_le_edgeKernel (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) : Z R (alpha R) ≤ Q R (beta R) := by
  apply le_trans ?_ (Q_le_adjacent_h R rfl (base_adjacent R))
  rw [← common.X_eq_Z (alpha R) rfl]
  exact omegaCenter_le _

private theorem edge_commutator_natural (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) :
    ⁅Z R (alpha R), Q R (beta R)⁆ = ⁅U R (alpha R), Q R (beta R)⁆ := by
  rw [commutator_comm (Z R (alpha R)), commutator_comm (U R (alpha R))]
  apply (commutator_eq_of_centralizing_sup
    (show (Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))) ⊔
      U R (alpha R) = Z R (alpha R) from
      (sup_comm _ _).trans (central_split source geometry common).symm)
    (inf_le_right.trans (centralizer_le
      (show Q R (beta R) ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 (alpha R) (adjacent_symm R (base_adjacent R)))))
    (((U_le_Z (alpha R)).trans (Z_alpha_le_edgeKernel source geometry common)).trans
      (Q R (beta R)).le_normalizer)).symm

/-- The source commutator is the actual fixed plane inside the marked natural
subgroup, rather than just an abstract subgroup with the same order. -/
theorem edge_natural_fixed_plane (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    ⁅Z R (alpha R), Q R (beta R)⁆ =
      U R (alpha R) ⊓ Z R (beta R) := by
  let D := ⁅Z R (alpha R), Q R (beta R)⁆
  let W := U R (alpha R) ⊓ Z R (beta R)
  have hU : Nat.card (U R (alpha R)) = 8 := common.natural.card_at (alpha R) rfl
  let : Finite (U R (alpha R)) := Nat.finite_of_card_ne_zero (by omega)
  have hQstab : Q R (beta R) ≤ stabilizer R (alpha R) :=
    fun _ hx => hx.2 (alpha R) (adjacent_symm R (base_adjacent R))
  have hDU : D ≤ U R (alpha R) := by
    change ⁅Z R (alpha R), Q R (beta R)⁆ ≤ U R (alpha R)
    rw [edge_commutator_natural source geometry common]
    exact le_normalizer_iff_commutator_le_left.mp (hQstab.trans (U_normalized (alpha R)))
  have hDZ : D ≤ Z R (beta R) := by
    apply commutator_le_of_normalized_index_two _ _ _
      (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
      (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R))
      (hQstab.trans (Z_normalized R (alpha R)))
    exact (hkernel ▸ flagKernel_le source i).trans
      (flagParabolic_normalizes_edge_Z source i hkernel)
  have hDW : D ≤ W := le_inf hDU hDZ
  have hWU : W ≤ U R (alpha R) := inf_le_left
  let : Finite D := Finite.of_injective (inclusion hDU) (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWU) (inclusion_injective _)
  have hD : Nat.card D = 4 := early.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)
  have hWne : W ≠ U R (alpha R) := by
    intro he
    have hUC : U R (alpha R) ≤ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
      have hw : W ≤ Z R (beta R) := inf_le_right
      rw [he, Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)] at hw
      exact hw.trans inf_le_right
    have hd : D = ⊥ := (edge_commutator_natural source geometry common).trans
      (commutator_eq_bot_iff_le_centralizer.mpr hUC)
    have hc := card_eq_one.mpr hd
    omega
  have hW : Nat.card W = 4 := by
    have hd := card_dvd_of_le hWU
    rw [hU] at hd
    have hm : Nat.card W ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hm
    have hc : Nat.card W = 1 ∨ Nat.card W = 2 ∨ Nat.card W = 4 ∨ Nat.card W = 8 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hge := card_le_of_le hDW
    have hne : Nat.card W ≠ 8 := fun he =>
      hWne (eq_of_le_of_card_ge hWU (by rw [hU, he]))
    omega
  exact eq_of_le_of_card_ge hDW (by rw [hW, hD])

private theorem flag_two_idempotent (source : LocalSource L R) (i : Bool)
    (Y : Subgroup (FreeAmalgam R)) (hYP : Y ≤ flagParabolic source i)
    (hp : IsPGroup 2 Y)
    (hn : flagResidual source i ≤ normalizer (Y : Set (FreeAmalgam R))) :
    ⁅⁅Y, flagResidual source i⁆, flagResidual source i⁆ = ⁅Y, flagResidual source i⁆ := by
  let P := flagParabolic source i
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion (flagParabolic_le source i))
    (inclusion_injective _)
  let W := Y.subgroupOf P
  have hW : W.map P.subtype = Y := map_subgroupOf_eq_of_le hYP
  have hres : (pResidual 2 P).map P.subtype = flagResidual source i :=
    (flagResidual_eq source i).symm
  have hWN : pResidual 2 P ≤ normalizer (W : Set P) := by
    apply le_normalizer_iff.mpr
    intro h hh w hw
    exact le_normalizer_iff.mp hn h (hres ▸ mem_map_of_mem P.subtype hh) w hw
  have hi := commutator_isPPerfect_idempotent (pResidual 2 P) W
    (isPPerfect_pResidual 2) hp.comap_subtype hWN
  have hm := congrArg (Subgroup.map P.subtype) hi
  simpa only [map_commutator, hW, hres] using hm

/-- The marked residual moves precisely the natural edge plane, and its
fixed part in the whole edge layer is central in the whole vertex stabilizer.
The proof uses the genuine natural carrier and the intrinsic marked core;
it is uniform in both flag orientations and every natural marking. -/
theorem edgeFixedLayerAction (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    ⁅Z R (beta R), flagResidual source i⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ ∧
      Z R (beta R) ⊓ centralizer (flagResidual source i : Set (FreeAmalgam R)) ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  let D := ⁅Z R (alpha R), Q R (beta R)⁆
  let F := Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))
  let H := flagResidual source i
  have hD : Nat.card D = 4 := early.edge_commutator_card (alpha R) (beta R) rfl (base_adjacent R)
  have hU : Nat.card (U R (alpha R)) = 8 := common.natural.card_at (alpha R) rfl
  have hplane : D = U R (alpha R) ⊓ Z R (beta R) :=
    edge_natural_fixed_plane source geometry common early i hkernel
  have hDU : D ≤ U R (alpha R) := hplane ▸ inf_le_left
  have hQstab : Q R (beta R) ≤ stabilizer R (alpha R) :=
    fun _ hx => hx.2 (alpha R) (adjacent_symm R (base_adjacent R))
  have hHstab : H ≤ stabilizer R (alpha R) :=
    (flagResidual_le source i).trans (flagParabolic_le source i)
  have hHU : H ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) :=
    hHstab.trans (U_normalized (alpha R))
  have hHZ : H ≤ normalizer (Z R (beta R) : Set (FreeAmalgam R)) :=
    (flagResidual_le source i).trans (flagParabolic_normalizes_edge_Z source i hkernel)
  have hHD : H ≤ normalizer (D : Set (FreeAmalgam R)) := by
    rw [hplane]
    exact le_normalizer_inf hHU hHZ
  have hFstab : F ≤ stabilizer R (alpha R) :=
    inf_le_left.trans (Z_le_stabilizer R (alpha R))
  have hFH : F ≤ centralizer (H : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le hHstab)
  have hFQ : F ≤ centralizer (Q R (beta R) : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le hQstab)
  have hFUnorm : F ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) :=
    hFstab.trans (U_normalized (alpha R))
  have hsplit : Z R (beta R) = D ⊔ F := by
    have hfixed := Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)
    have hplaneC : D = U R (alpha R) ⊓ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
      rw [hplane, hfixed, ← inf_assoc, inf_eq_left.mpr (U_le_Z (alpha R))]
    calc
      Z R (beta R) = (U R (alpha R) ⊔ F) ⊓
          centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
        rw [hfixed, central_split source geometry common]
      _ = (U R (alpha R) ⊓ centralizer (Q R (beta R) : Set (FreeAmalgam R))) ⊔ F :=
        MarkedAction.fixed_sup_of_centralizing _ _ _ hFUnorm hFQ
      _ = D ⊔ F := by rw [← hplaneC]
  have hUP : U R (alpha R) ≤ flagParabolic source i :=
    ((U_le_Z (alpha R)).trans (Z_alpha_le_edgeKernel source geometry common)).trans
      (hkernel ▸ flagKernel_le source i)
  have himage : ⁅U R (alpha R), H⁆ ≤ D := by
    rw [hplane]
    apply le_inf (le_normalizer_iff_commutator_le_left.mp hHU)
    apply (commutator_mono (U_le_Z (alpha R)) le_rfl).trans
    exact commutator_le_of_normalized_index_two _ _ _
      (edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
      (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R))
      (hHstab.trans (Z_normalized R (alpha R))) hHZ
  have hne : ⁅U R (alpha R), H⁆ ≠ ⊥ := by
    intro hz
    have hcH : H ≤ centralizer (U R (alpha R) : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hcQ : Q R (alpha R) ≤ centralizer (U R (alpha R) : Set (FreeAmalgam R)) :=
      le_centralizer_iff.mp ((U_le_Z (alpha R)).trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)))
    have hcEdge : Q R (beta R) ≤ centralizer (U R (alpha R) : Set (FreeAmalgam R)) :=
      (hkernel ▸ flagKernel_le_residual_sup_vertexKernel source i).trans (sup_le hcH hcQ)
    have hd : D = ⊥ := (edge_commutator_natural source geometry common).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcEdge))
    have hc := card_eq_one.mpr hd
    omega
  have hidem : ⁅⁅U R (alpha R),H⁆,H⁆ = ⁅U R (alpha R),H⁆ :=
    flag_two_idempotent source i _ hUP (IsPGroup.of_card (n := 3) hU) hHU
  obtain ⟨_, hmove, hfixed⟩ :=
    MarkedAction.moving_four_fixed_free (U R (alpha R)) D H hD hHD himage hne hidem
  have hFD : F ≤ centralizer (D : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le ((hDU.trans (U_le_Z (alpha R))).trans
      (Z_le_stabilizer R (alpha R))))
  constructor
  · have he : ⁅H,D⁆ = ⁅H,Z R (beta R)⁆ :=
      commutator_eq_of_centralizing_sup ((sup_comm F D).trans hsplit.symm) hFH
        ((hDU.trans hUP).trans (flagResidual_normalized source i))
    rw [commutator_comm H D, commutator_comm H (Z R (beta R))] at he
    exact he.symm.trans hmove
  · have hf : Z R (beta R) ⊓ centralizer (H : Set (FreeAmalgam R)) = F := by
      rw [hsplit, MarkedAction.fixed_sup_of_centralizing D F H
        (hFD.trans (Subgroup.centralizer_le_normalizer _)) hFH, hfixed, bot_sup_eq]
    rw [hf]
    intro x hx
    refine ⟨⟨x, hFstab hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hx.2 y y.property

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
