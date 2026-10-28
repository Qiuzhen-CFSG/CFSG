module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallCoreSpan
public import Theory.GroupTheory.PResidual.ConjugateSpanCore
public import CFSG.Quasithin.ChapterB.Section06To07.NormalActor
/-!
# Full residual movement of the marked seed span

In the solvable source configuration, P≤O₂(H)∩O²(H) and P≤⟨(P∩V)ᴴ⟩.
The marked intersection is O₂(H)∩V. The normal-actor theorem gives
O²(H)=[O²(H),V], and B.6.8 gives odd residual order modulo O₂(H).
The general span-core theorem therefore identifies the actual global span
with O₂(H)∩O²(H) and proves its full movement by O²(H).

Source: Aschbacher--Smith, E.2.17, printed p.229. No premise about the
ambient normalization of the original pair core is used.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}
theorem OriginalWitness.small_span_residual_of_solvable
    {κ : GroupClass} (hH : IsSQTK κ H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (w : OriginalWitness S (ChapterB.minimalParabolicMax S hP) W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ ChapterB.minimalParabolicCore S hP)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk))
    : let L := conjugateSpanBy (pCore 2 H ⊓ W) ⊤
      w.pair.subgroup.pCoreIn 2 ≤ L ∧
      L = pCore 2 H ⊓ pResidual 2 H ∧ ⁅L,pResidual 2 H⁆ = L := by
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hplacement := w.small_core_placement_of_solvable hH hP hs hWS hSW hcore hout
    hfit hW hSU hU q hq hk hD hratio
  have hPL := w.small_core_le_span hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  rw [hplacement.2] at hPL
  have hPK : w.pair.subgroup.pCoreIn 2 ≤ pResidual 2 H :=
    (map_mono (w.small_core_le_residual hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio)).trans
      (map_pResidual_le 2 w.pair.subgroup.subtype)
  have hBK : pCore 2 H ⊓ W ≤ pResidual 2 H := by
    rw [←hplacement.2]
    exact inf_le_left.trans hPK
  have hQV : ⁅pCore 2 H,W⁆ ≤ pCore 2 H ⊓ W := by
    refine le_inf (commutator_le_left _ _) ?_
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((pCore_isPGroup.le_sylow_of_normal S).trans hSW)
  have hKV := ChapterB.minimalParabolic_residual_commutator_of_normalized_two_actor
    S hP W hWS hSW (fun hh => hout (hh.trans (ChapterB.minimalParabolicTwoCore_le_core S hP)))
  have hodd : Nat.Coprime 2 (Nat.card (pResidual 2 (H ⧸ pCore 2 H))) := by
    obtain ⟨p,hp,ho,he,_⟩ := ChapterB.minimalParabolic_solvable_structure S hP hs
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨m,hm⟩ := (pCore_isPGroup (p := p) (G := H ⧸ pCore 2 H)).exists_card_eq
    rw [he,hm]
    exact ho.coprime_two_left.pow_right m
  exact ⟨hPL,conjugateSpan_core_eq_core_inf_residual W hQV hBK hKV hodd⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
