module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Transfer.Second
public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.TransferData

/-!
# Construction of the two transfers for the supplied second involution

For the original second elementary subgroup F and the supplied Q-fixed
involution v, Thompson transfer gives M of index two in C_G(v), with
Sylow image W = Ω₁(O₂(N_G(F))). The derived-line calculation proves weak
closure of Z(W) in M. A binary character of its normalizer detects the
compatible order-four root; Grün transfer extends this character to M.
Its kernel L has a Sylow image Y of order 128, with Ω₁(Y) = F and
Z(Y) = Z(W).

Every field below uses the literal subgroup inclusions from the transfer
interface. Only the original derived-core normalizer identity and solvability
of the second elementary normalizers are used; the full second involution
centralizer need not be solvable.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
Lemma 8, printed pp.682–683, the two transfer steps.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottNormalizerFusionData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z}

/-- Construct the actual nested transfer subgroups for the original supplied
F, Sylow two-subgroup, Q and v, without an ambient containment premise. -/
public theorem exists_second_transfer_data_of_local_inputs
    (n : ParrottNormalizerFusionData d)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    Nonempty (ParrottSecondTransferData n) := by
  obtain ⟨M, L, b, hMn, hMi, hMP, hLn, hLi, hb, hb4, hb2, hfix,
      hbL, hYcard, hYomega, hYcenter, S, hS⟩ :=
    d.second_centralizer_second_transfer_of_local_hypotheses h hlocal
      n.sylow_lt_normalizer n.Q n.core_fixed_le_derived n.v n.v_order n.elementary_fixed
  exact ⟨{
    M := M
    L := L
    M_normal := hMn
    M_index := hMi
    M_inf_sylow := hMP
    L_normal := hLn
    L_index := hLi
    b := b
    b_mem_core := hb
    b_order := hb4
    b_sq := hb2
    core_fixed := hfix
    b_not_mem := hbL
    Y_card := hYcard
    Y_omega := hYomega
    Y_center := hYcenter
    S := S
    S_image := hS }⟩

end Stellmacher.Recognition.ParrottNormalizerFusionData
