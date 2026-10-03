module

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationSetup
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicNormalizerSelection
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicTransferSetup
public import Theory.GroupTheory.IndexFourCosetFusion
public import Theory.GroupTheory.PGroup.QuaternionHallInvolutionCentralizer

/-!
# Outside fusion from a local normalizer and its centralizer count

The intrinsic rotation subgroup is normal of index four. Once the local
normalizer captures outside involutions and has centralizer of order four
for the chosen representative, orbit–stabilizer fills its rotation coset.
Conjugation in the Sylow group preserves that coset because the quotient
by the rotation subgroup has order four and is abelian.

The large-tail theorem discharges these local geometric inputs: the
odd-complement normalizer selects an invariant Hall factor, core weak closure
makes the Sylow centralizer elementary abelian, and the quaternion–Hall
calculation gives order four for the centralizer in the selected normalizer.
Only the intrinsic rotation subgroup's index-four premise remains explicit.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.392, after
“Choose z₁”; refs/original/n-group-global/odd-core-rank-two-source/
janko-thompson-1970-gdz.pdf, PDF page 8.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- A normalizer covering the rotation quotient, capturing outside involutions,
and having the expected local centralizer yields the requested outside fusion. -/
public theorem exists_outside_coset_fusion_of_local_normalizer
    (S : Sylow 2 G) (hKindex : (noncyclicRotationPreimage S).index = 4)
    (z v : S) (hv : orderOf v = 2) (hout : v ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (v : G))
    (L : Subgroup S) (hvL : v ∈ L)
    (hgen : noncyclicRotationPreimage S ⊔ L = ⊤)
    (hC : Nat.card (centralizer ({(⟨v, hvL⟩ : L)} : Set L)) = 4)
    (hmove : ∀ u : S, orderOf u = 2 → u ∉ omegaCorePreimage S →
      ∃ w : L, IsConj u (w : S)) :
    ∃ v : S, orderOf v = 2 ∧ v ∉ omegaCorePreimage S ∧
      IsConj (z : G) (v : G) ∧
      ∀ u : S, u ∈ noncyclicRotationPreimage S ⊔ zpowers v →
        u ∉ noncyclicRotationPreimage S → orderOf u = 2 →
          IsConj (u : G) (v : G) := by
  refine ⟨v, hv, hout, hconj, ?_⟩
  intro u hu huK huo
  have hcard := card_eq_mul_centralizer_card_of_index_four
    (noncyclicRotationPreimage S) L hKindex hgen ⟨v, hvL⟩ hC
  exact (S : Subgroup G).subtype.map_isConj (isConj_of_index_four_of_local_control
    (noncyclicRotationPreimage S) (omegaCorePreimage S) hKindex
    (noncyclicRotationPreimage_le S) v hv hout L hvL hcard hmove u hu huK huo)

/-- An outside conjugate of the central involution controls every involution
in its nontrivial rotation coset. The odd-complement normalizer and the
quaternion–Hall centralizer calculation discharge all local fusion premises;
the parent supplies the intrinsic rotation subgroup's index four.

Weak closure is needed only for the chosen central involution. -/
public theorem exists_outside_coset_fusion_of_large_noncyclic_tail
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
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
    (hKindex : (noncyclicRotationPreimage S).index = 4)
    (z t : S) (hzc : z ∈ center S) (hz : orderOf z = 2)
    (hweak : ∀ u : S, u ∈ omegaCorePreimage S → IsConj (z : G) (u : G) → u = z)
    (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S)
    (hconj : IsConj (z : G) (t : G)) :
    ∃ v : S, orderOf v = 2 ∧ v ∉ omegaCorePreimage S ∧
      IsConj (z : G) (v : G) ∧
      ∀ u : S, u ∈ noncyclicRotationPreimage S ⊔ zpowers v →
        u ∉ noncyclicRotationPreimage S → orderOf u = 2 →
          IsConj (u : G) (v : G) := by
  obtain ⟨v, B₀, D₀, hv, hvout, hvconj, -, hD₀n, hB₀, hD₀,
      hn₀, hlarge₀, hc₀, hg₀, hvnorm, hgen, hmove⟩ :=
    exists_noncyclic_hall_normalizer_cover hN S hZ hno W hunique hnormal
      B D hB hD hn hc hg hlarge hi z t ht hout hconj
  let : D₀.Normal := hD₀n
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  let : IsCyclic (center (omegaCorePreimage S)) :=
    (centerCongr (omegaCorePreimageEquiv S)).isCyclic.mpr inferInstance
  let : IsElementaryAbelian 2 (centralizer ({v} : Set S)) :=
    elementary_centralizer_of_large_noncyclic_tail_of_core_weak_closure
      hN S hno hZ W hW hunique hnormal B D hD hn hc hg hlarge hi
      z v hzc hz hweak hv hvout hvconj
  exact exists_outside_coset_fusion_of_local_normalizer S hKindex z v hv hvout hvconj
    (D₀.map (omegaCorePreimage S).subtype ⊔ zpowers v)
    (mem_sup_right (mem_zpowers v)) hgen
    (card_centralizer_join_eq_four_of_quaternion_large_hall S.isPGroup'
      (omegaCorePreimage S) B₀ D₀ hB₀ hD₀ hn₀ hlarge₀ hc₀ hg₀ v hv hvout hvnorm)
    hmove

end Stellmacher.Recognition.NormalEightNonnormalImage
