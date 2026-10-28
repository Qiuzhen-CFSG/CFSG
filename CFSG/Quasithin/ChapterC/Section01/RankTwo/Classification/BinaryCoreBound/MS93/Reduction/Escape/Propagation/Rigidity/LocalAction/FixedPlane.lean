module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Equality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison.MarkedAction.Core
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.EdgeComparison.MarkedAction.Algebra

/-!
# Residual action on the binary fixed plane

Adapted from the independent calculation in DistanceFour/Flags/RankOne/
Consequences/EdgeComparison/MarkedAction. The inputs here are only the natural
module and the edge containment, order and index of (4.3.3). Residual
idempotence is computed inside the finite actual parabolic.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.4), p.886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity.LocalAction
open DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem central_split (source : LocalSource L R) (geometry : Geometry R)
    (modules : ModuleFacts source geometry) :
    Z R (alpha R) = U R (alpha R) ⊔
      (Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))) := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  exact s.decomposition_at (alpha R) rfl

private theorem Z_alpha_le_edgeKernel (source : LocalSource L R) (geometry : Geometry R)
    (modules : ModuleFacts source geometry) : Z R (alpha R) ≤ Q R (beta R) := by
  apply le_trans ?_ (Q_le_adjacent_h R rfl (base_adjacent R))
  rw [← modules.X_eq_Z (alpha R) rfl]
  exact omegaCenter_le _

private theorem edge_commutator_natural (source : LocalSource L R) (geometry : Geometry R)
    (modules : ModuleFacts source geometry) :
    ⁅Z R (alpha R), Q R (beta R)⁆ = ⁅U R (alpha R), Q R (beta R)⁆ := by
  rw [commutator_comm (Z R (alpha R)), commutator_comm (U R (alpha R))]
  apply (commutator_eq_of_centralizing_sup
    (show (Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))) ⊔
      U R (alpha R) = Z R (alpha R) from
      (sup_comm _ _).trans (central_split source geometry modules).symm)
    (inf_le_right.trans (centralizer_le
      (show Q R (beta R) ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 (alpha R) (adjacent_symm R (base_adjacent R)))))
    (((U_le_Z (alpha R)).trans (Z_alpha_le_edgeKernel source geometry modules)).trans
      (Q R (beta R)).le_normalizer)).symm

theorem flag_two_idempotent (source : LocalSource L R) (i : Bool)
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
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hZ : edgeDisplacement (alpha R) (beta R) ≤ Z R (beta R))
    (hcard : Nat.card (edgeDisplacement (alpha R) (beta R)) = 4)
    (hindex : (Z R (beta R)).relIndex (Z R (alpha R)) = 2)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    ⁅Z R (beta R), flagResidual source i⁆ = ⁅Z R (alpha R), Q R (beta R)⁆ ∧
      Z R (beta R) ⊓ centralizer (flagResidual source i : Set (FreeAmalgam R)) ≤
        (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  let D := ⁅Z R (alpha R), Q R (beta R)⁆
  let F := Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))
  let H := flagResidual source i
  have hD : Nat.card D = 4 := hcard
  have hU : Nat.card (U R (alpha R)) = 8 := modules.natural.card_at (alpha R) rfl
  have hplane : D = U R (alpha R) ⊓ Z R (beta R) :=
    (edge_fixed_natural_eq_commutator hb modules (alpha R) (beta R) rfl (base_adjacent R) hZ hcard).symm
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
    have hfixed := EdgeTransfer.edge_Z_eq_fixed hb modules (alpha R) (beta R) rfl (base_adjacent R)
    have hplaneC : D = U R (alpha R) ⊓ centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
      rw [hplane, hfixed, ← inf_assoc, inf_eq_left.mpr (U_le_Z (alpha R))]
    calc
      Z R (beta R) = (U R (alpha R) ⊔ F) ⊓
          centralizer (Q R (beta R) : Set (FreeAmalgam R)) := by
        rw [hfixed, central_split source geometry modules]
      _ = (U R (alpha R) ⊓ centralizer (Q R (beta R) : Set (FreeAmalgam R))) ⊔ F :=
        MarkedAction.fixed_sup_of_centralizing _ _ _ hFUnorm hFQ
      _ = D ⊔ F := by rw [← hplaneC]
  have hUP : U R (alpha R) ≤ flagParabolic source i :=
    ((U_le_Z (alpha R)).trans (Z_alpha_le_edgeKernel source geometry modules)).trans
      (hkernel ▸ flagKernel_le source i)
  have himage : ⁅U R (alpha R), H⁆ ≤ D := by
    rw [hplane]
    apply le_inf (le_normalizer_iff_commutator_le_left.mp hHU)
    apply (commutator_mono (U_le_Z (alpha R)) le_rfl).trans
    exact commutator_le_of_normalized_index_two _ _ _
      (EdgeTransfer.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R))
      hindex
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
    have hd : D = ⊥ := (edge_commutator_natural source geometry modules).trans
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

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Rigidity.LocalAction
