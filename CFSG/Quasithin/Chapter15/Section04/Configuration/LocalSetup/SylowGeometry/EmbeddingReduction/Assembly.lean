module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.InvariantResidual
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SwappedResidual

/-!
# Assembly of the embedding and residual reduction in 15.4.20

Starting with the actual placed contrary configuration, the corrected local
embedding theorem and the component-orbit theorem give either the binary-linear
component or the exchanged rank-one pair. The source X normally generates the
selected component or pair. The binary outer-action calculation proves the
three-prime residual identity directly; the exchanged case uses exact 1.2.2(a)
after proving its orbit and quotient-divisibility premises.

Replacing H by KU preserves the original amalgam, the actual Sylow U, its new
core-normalizer Sylow property and the global maximality bound. Both component
configurations and all raw placed data survive in that replacement. The universal
earlier-result parameters remain explicit for the Chapter 15 source assembly;
no later identification from 15.4.21–23 is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
second paragraph of 15.4.20, printed pp.1163–1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G]
open Chapter1

/-- The invariant branch on p.1164, with an actual binary model and the full
automorphism quotient, including relative normality in the placed overgroup. -/
def BinaryCase (H U K : Subgroup G) : Prop :=
  K ∈ cComponentsIn H ∧ (K.subgroupOf H).Normal ∧
    IsQuasisimple (XiQuotient K) ∧ IsSimpleGroup (XiQuotient K) ∧
    (ClassicalGroup.IsPSL (XiQuotient K) 4 2 ∨ ClassicalGroup.IsPSL (XiQuotient K) 5 2) ∧
    Nonempty (XiQuotient (K ⊔ U) ≃* MulAut (XiQuotient K))

/-- The exchanged branch, retaining the same moving element in both actual
products. Component normality is relative to K, not to H. -/
def ExchangedCase (H U P K : Subgroup G) : Prop :=
  ∃ (L : Subgroup G) (t : G), L ∈ cComponentsIn H ∧
    IsQuasisimple (XiQuotient L) ∧ IsSimpleGroup (XiQuotient L) ∧
    XiEmbedding.SwappedModel 3 (XiQuotient L) ∧
    t ∈ U ⊓ normalizer P ∧ t ∉ normalizer L ∧
    (normalizer (L.subgroupOf H : Set H)).index = 2 ∧
    K = L ⊔ L.conjBy t ∧ (K : Set G) = (L : Set G) * (L.conjBy t : Set G) ∧
    (L.subgroupOf K).Normal ∧
    P = (P ⊓ L) ⊔ (P ⊓ L).conjBy t ∧
    Disjoint (P ⊓ L) ((P ⊓ L).conjBy t) ∧ ⁅P ⊓ L, (P ⊓ L).conjBy t⁆ = ⊥

variable [Finite G] {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}

omit [Finite G] in
/-- An intermediate overgroup containing K retains the invariant component. -/
theorem BinaryCase.restrict {D K : Subgroup G} (hc : BinaryCase H U K)
    (hKD : K ≤ D) (hDH : D ≤ H) : BinaryCase D U K := by
  obtain ⟨hK, hn, hq, hs, hm, ha⟩ := hc
  exact ⟨⟨hKD, hK.2.subgroupOf_of_le hKD hDH⟩,
    (normal_subgroupOf_iff_le_normalizer hKD).mpr
      (hDH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hn)),
    hq, hs, hm, ha⟩

/-- The moving element lies in the replacement, so its component still has
orbit two there. The model and both factorizations are unchanged. -/
theorem ExchangedCase.restrict (hG : IsSimpleQTKE κ G)
    (orbits : ComponentOrbitTheorem κ) {D P K : Subgroup G}
    (hc : ExchangedCase H U P K) (hKD : K ≤ D) (hUD : U ≤ D)
    (hDH : D ≤ H) (hD : D ∈ Chapter1.H G) : ExchangedCase D U P K := by
  obtain ⟨L, t, hL, hq, hs, hm, ht, hmove, _, hK, hprod, hn, hP, hd, hcomm⟩ := hc
  have hLD : L ≤ D := (le_sup_left.trans hK.ge).trans hKD
  have hL' : L ∈ cComponentsIn D := ⟨hLD, hL.2.subgroupOf_of_le hLD hDH⟩
  have hi : (normalizer (L.subgroupOf D : Set D)).index = 2 := by
    have ho := orbits G hG D hD L hL'
    rw [ncard_conjugates_eq_index_normalizer] at ho
    rcases ho with hn | ⟨hi, _⟩
    · exact (hmove (((normal_subgroupOf_iff_le_normalizer hLD).mp hn) (hUD ht.1))).elim
    · exact hi
  exact ⟨L, t, hL', hq, hs, hm, ht, hmove, hi, hK, hprod, hn, hP, hd, hcomm⟩

omit [Finite G] in
/-- The full raw placed configuration survives any replacement satisfying
the proved overgroup, Sylow, and new core-normalizer assertions. -/
theorem PlacedX.replacement_configuration (h : PlacedX d i j H U)
    {D : Subgroup G} (hD : D ∈ Chapter1.HOver G (d.I i j : Set G))
    (hU : IsSylowIn 2 U D)
    (hcore : IsSylowIn 2 U (normalizer (D.pCoreIn 2 : Set G))) :
    Nonempty (PlacedX d i j D U) := by
  obtain ⟨S, hS⟩ := hU
  exact ⟨{
    overgroup := hD
    sylow := S
    sylow_image := hS
    lower := h.lower
    upper := h.upper
    lower_index := h.lower_index
    upper_index := h.upper_index
    maximal := h.maximal
    core_sylow := hcore
    T_normalizes := h.T_normalizes
    baumann_le := h.baumann_le
    permutes := h.permutes
    moves := h.moves
    outside := h.outside
    perfect := h.perfect
    core_nontrivial := h.core_nontrivial
    quotient := h.quotient
    product := h.product
    product_surjective := h.product_surjective
    product_kernel := h.product_kernel
    first_image := h.first_image
    second_image := h.second_image
    first_perfect := h.first_perfect
    other_perfect := h.other_perfect
    first_quotient_card := h.first_quotient_card
    other_quotient_card := h.other_quotient_card }⟩

/-- The source X normally generates exactly the three-prime residual, and
that actual normal closure satisfies one of the two source configurations. -/
theorem PlacedX.normalClosure_branches (hG : IsSimpleQTKE κ G)
    (embedding : LocalEmbeddingTheorem κ) (orbits : ComponentOrbitTheorem κ)
    (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    K = (primeToResidual 3 H).map H.subtype ∧
      (BinaryCase H U K ∨ ExchangedCase H U P₀ K) := by
  obtain ⟨hsq, hlocal, _, _⟩ := h.embedding_input hG P
  obtain ⟨L, hL, hq, hs, hX, _, _, hb⟩ := h.two_branches hG embedding orbits P
  rcases hb with ⟨hswap, hm, hi⟩ | ⟨hn, hXL, hm, haut⟩
  · have hr := swapped_normalClosure_eq_residual hG residual h.overgroup.1
      hlocal hL hs hX hswap hi
    have he := swapped_normalClosure_eq_orbit hlocal hL hs hX hswap hi
    obtain ⟨t, ht, hmove, hP, hdisj, hcomm⟩ := hswap.2
    have hpair : normalClosureIn d.wholeX H = L ⊔ L.conjBy t :=
      he.1.trans (componentOrbit_eq_pair_of_index_two le_rfl hL.1 hi
        ((le_sup_right.trans hlocal.overgroup) ht.1) hmove)
    have hKN : normalClosureIn d.wholeX H ≤ normalizer L :=
      he.1.le.trans (componentOrbit_le_normalizer hL)
    have hLK : L ≤ normalClosureIn d.wholeX H := le_sup_left.trans hpair.ge
    have hproduct : (normalClosureIn d.wholeX H : Set G) =
        (L : Set G) * (L.conjBy t : Set G) := by
      exact (congrArg (fun A : Subgroup G => (A : Set G)) hpair).trans
        (coe_mul_of_right_le_normalizer_left _ _ ((le_sup_right.trans hpair.ge).trans hKN))
    exact ⟨hr, Or.inr ⟨L, t, hL, hq, hs, hm, ht, hmove, hi, hpair, hproduct,
      (normal_subgroupOf_iff_le_normalizer hLK).mpr hKN, hP, hdisj, hcomm⟩⟩
  · have hk := h.normalClosure_eq_component hXL hL.1 hn (cComponent_twoPerfect hL) hs
    have hr : normalClosureIn d.wholeX H = (primeToResidual 3 H).map H.subtype :=
      le_antisymm h.normalClosure_le_residual
        ((binary_residual_le hsq hlocal hL hn hXL hm).trans hk.ge)
    refine ⟨hr, Or.inl ?_⟩
    rw [hk]
    exact ⟨hL, hn, hq, hs, hm, haut⟩

/-- Complete embedding/residual reduction for the placed moved-X orientation.
The replacement KU retains I, H-membership, the actual Sylow U, global maximal
Sylow order and the Sylow assertion in its new core normalizer. The universal
earlier results remain for the source assembly owner to instantiate. -/
theorem PlacedX.embedding_residual_reduction (hG : IsSimpleQTKE κ G)
    (embedding : LocalEmbeddingTheorem κ) (orbits : ComponentOrbitTheorem κ)
    (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    let D := K ⊔ U
    IsSQTK κ H ∧ XiEmbedding.LocalInput 3 U d.wholeX P₀ H ∧
      IsSylowIn 2 U H ∧ Nonempty (P₀ ≃* XiEmbedding.Plane 3) ∧
      Nonempty (XiEmbedding.automizer U P₀ ≃* DihedralGroup 4) ∧
      K = (primeToResidual 3 H).map H.subtype ∧
      (BinaryCase H U K ∨ ExchangedCase H U P₀ K) ∧
      (K.subgroupOf H).Normal ∧ D ≤ H ∧
      D ∈ Chapter1.HOver G (d.I i j : Set G) ∧ IsSylowIn 2 U D ∧
      (∀ J ∈ Chapter1.HOver G (D : Set G), IsSylowIn 2 U J) ∧
      (∀ J ∈ Chapter1.HOver G (D : Set G), ∀ Q : Sylow 2 J,
        Nat.card ((Q : Subgroup J).map J.subtype) ≤ Nat.card U) ∧
      IsSylowIn 2 U (normalizer (D.pCoreIn 2 : Set G)) ∧
      Nonempty (PlacedX d i j D U) ∧
      (BinaryCase D U K ∨ ExchangedCase D U P₀ K) := by
  obtain ⟨hsq, hlocal, hSylow, hD⟩ := h.embedding_input hG P
  obtain ⟨hr, hb⟩ := h.normalClosure_branches hG embedding orbits residual P
  have hplane : Nonempty (((P : Subgroup d.wholeX).map d.wholeX.subtype) ≃*
      XiEmbedding.Plane 3) := by
    obtain ⟨L, _, _, _, he, _, _⟩ := h.component_alternatives hG embedding P
    exact he
  have hrepl := h.residual_replacement
  rw [← hr] at hrepl
  have hDH : normalClosureIn d.wholeX H ⊔ U ≤ H :=
    sup_le (normalClosureIn_le_overgroup _ _) (le_sup_right.trans hlocal.overgroup)
  refine ⟨hsq, hlocal, hSylow, hplane, hD, hr, hb, normalClosureIn_normal _ _,
    hDH, hrepl.1, hrepl.2.1, hrepl.2.2.1, ?_, hrepl.2.2.2,
    h.replacement_configuration hrepl.1 hrepl.2.1 hrepl.2.2.2, ?_⟩
  · intro J hJ Q
    exact h.maximal J ⟨hJ.1, hrepl.1.2.trans hJ.2⟩ Q
  · exact hb.elim (fun hc => Or.inl (hc.restrict le_sup_left hDH))
      (fun hc => Or.inr (hc.restrict hG orbits le_sup_left le_sup_right hDH hrepl.1.1))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
