module

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTransferSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicInvolutionSelection
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicOutsideCentralizer
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Core involutions separated from the normal four

In the large Hall-tail case, the Sylow subgroup has order at least 128. An
involution outside the characteristic rotation product has a centralizer of
order at most 32. Once that centralizer is Sylow in the common centralizer
with the central involution, a characteristic derived-center line promotes it
to a Sylow subgroup of the full ambient centralizer. Its order then excludes
fusion to any element of the normal four.

The final theorem discharges the selection and centralizer geometry using the
large noncyclic Hall factor. It is independent of the maximal-subgroup cover
and weak closure used subsequently for transfer. In particular no bound on
arbitrary elementary subgroups is used.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, Case 1, printed pp.392–393.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The index-two core and the central-product order formula give the actual
Sylow order; large Hall tails make this a lower bound, never an upper bound. -/
public theorem card_sylow_eq_eight_mul_tail_of_core_index_two
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8) (hD : D ≠ ⊥)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hi : (omegaCorePreimage S).index = 2) :
    Nat.card S = 8 * Nat.card D := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  have hprod := card_mul_two_eq_of_extraspecial_of_cyclic_center
    pCore_isPGroup B D hD hc hg
  have hindex := (omegaCorePreimage S).index_mul_card
  rw [hi, card_omegaCorePreimage] at hindex
  rw [hB] at hprod
  omega

/-- Selection outside a rotation product and the derived-center calculation
suffice for the required class-separation witness. The geometry is stated for
every outside core involution so that its proof is independent of selection. -/
public theorem exists_core_involution_separated_of_centralizer_geometry
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (hS : 64 < Nat.card S)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (R : Subgroup S)
    (hchoose : ∃ x : S, x ∈ omegaCorePreimage S ∧ x ∉ R ∧ orderOf x = 2 ∧
      ¬ 2 ∣ ((centralizer ({x} : Set S)).map (S : Subgroup G).subtype).relIndex
        (centralizer ({(z : G)} : Set G) ⊓ centralizer ({(x : G)} : Set G)))
    (hgeometry : ∀ x : S, x ∈ omegaCorePreimage S → x ∉ R → orderOf x = 2 →
      let Q := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
      (commutator Q ⊓ center Q).map Q.subtype = zpowers (z : G) ∧
        Nat.card (centralizer ({x} : Set S)) ≤ 32) :
    ∃ x : S, x ∈ omegaCorePreimage S ∧ orderOf x = 2 ∧ x ≠ z ∧
      ∀ w : S, w ∈ W → w ≠ z → ¬ IsConj (x : G) (w : G) := by
  obtain ⟨x, hxH, hxR, hx, hlocal⟩ := hchoose
  obtain ⟨hline, hcard⟩ := hgeometry x hxH hxR hx
  let C := centralizer ({x} : Set S)
  let Q := C.map (S : Subgroup G).subtype
  have hcontrol : normalizer (Q : Set G) ≤ centralizer ({(z : G)} : Set G) :=
    normalizer_le_centralizer_of_characteristic_involution Q
      (commutator Q ⊓ center Q) (z : G) ((orderOf_coe z).trans hz) hline
  have hsmall : 2 * Nat.card C < Nat.card S := by
    change Nat.card C ≤ 32 at hcard
    omega
  have hne : x ≠ z := by
    intro heq
    have htop : C = ⊤ := centralizer_eq_top_iff_subset.mpr (by
      exact Set.singleton_subset_iff.mpr (heq.symm ▸ hzc))
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hsmall
    omega
  refine ⟨x, hxH, hx, hne, ?_⟩
  intro w hw _
  exact S.not_isConj_mem_normal_four_of_local_centralizer W hW z x
    hlocal hcontrol hsmall w hw

/-- In the large noncyclic Hall-tail case, a core involution distinct from the
central involution avoids the other classes of the normal four. Selection and
centralizer geometry are discharged here, without a class cover or a weak
closure hypothesis. -/
public theorem exists_core_involution_separated_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (z : S) (hzc : z ∈ center S) (hz : orderOf z = 2) :
    ∃ x : S, x ∈ omegaCorePreimage S ∧ orderOf x = 2 ∧ x ≠ z ∧
      ∀ w : S, w ∈ W → w ≠ z → ¬ IsConj (x : G) (w : G) := by
  have hDne : D ≠ ⊥ := by
    intro heq
    rw [heq, card_bot] at hlarge
    omega
  have hcard := card_sylow_eq_eight_mul_tail_of_core_index_two
    S hno W hunique hnormal B D hB hDne hc hg hi
  have hS : 64 < Nat.card S := by omega
  exact exists_core_involution_separated_of_centralizer_geometry S W hW hS z hzc hz
    ((closure {u : omegaCorePreimage S | u ^ 4 ≠ 1}).map (omegaCorePreimage S).subtype)
    (exists_outside_rotation_involution_with_local_sylow_centralizer
      S hno W hunique hnormal B D hD hn hc hg hlarge hZ z hzc hz)
    (outside_rotation_centralizer_geometry
      hN S hno hZ W hW hunique hnormal B D hB hD hn hc hg hlarge hi z hzc hz)

end Stellmacher.Recognition.NormalEightNonnormalImage
