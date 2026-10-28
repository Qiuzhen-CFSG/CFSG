module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Adequate
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate.OriginalBranches
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate.Held

/-!
# The adequate three-way residual reduction in the contrary configuration

The intrinsic implication retains Held. In that branch, the actual Sylow
subgroup and the full component-orbit theorem give relative normality.
The quotient's proved centerlessness and outer two-group then identify the
original normal closure with the three-prime residual. The two old branches
use only their actual embedding conclusion, not an assumed stronger universal
embedding theorem. The resulting third branch preserves the actual component.

The complete adequate intrinsic theorem, component-orbit theorem and two-orbit
residual theorem remain earlier-source proof obligations. This module does
not claim the upstream component-containment or full intrinsic classification.
Source: Aschbacher--Smith, 1.2.1--2, 1.3.4 and 15.4.20, pp.504--510,1164,
with Held retained as required by the intrinsic source correction.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
open Chapter1
universe u
variable {G : Type u} [Group G]

/-- The retained actual single Held component, normal in the chosen overgroup. -/
def HeldCase (H K : Subgroup G) : Prop :=
  K ∈ cComponentsIn H ∧ (K.subgroupOf H).Normal ∧
    IsQuasisimple (XiQuotient K) ∧ Nonempty (XiQuotient K ≃* Held.He)

theorem HeldCase.restrict {H D K : Subgroup G} (hc : HeldCase H K)
    (hKD : K ≤ D) (hDH : D ≤ H) : HeldCase D K := by
  obtain ⟨hK, hn, hq, he⟩ := hc
  exact ⟨⟨hKD, hK.2.subgroupOf_of_le hKD hDH⟩,
    (normal_subgroupOf_iff_le_normalizer hKD).mpr
      (hDH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hn)), hq, he⟩

variable [Finite G] {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}

/-- All three actual residual branches, using the adequate intrinsic theorem
and retaining Held throughout the reduction. -/
theorem PlacedX.normalClosure_adequate (hG : IsSimpleQTKE κ G)
    (embedding : XiEmbedding.AdequateLocalEmbeddingTheorem κ)
    (orbits : ComponentOrbitTheorem κ) (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    K = (primeToResidual 3 H).map H.subtype ∧
      (BinaryCase H U K ∨ ExchangedCase H U P₀ K ∨ HeldCase H K) := by
  obtain ⟨hsq, hlocal, hSylow, _⟩ := h.embedding_input hG P
  rcases embedding G 3 U d.wholeX _ H hlocal hsq hSylow with hn | ⟨L,hL,hq,hX,ha⟩
  · exact (h.not_normal hn).elim
  rcases ha with ha | ⟨_, _, hn, ⟨e⟩⟩
  · have hc : XiEmbedding.Conclusion 3 U d.wholeX
        ((P : Subgroup d.wholeX).map d.wholeX.subtype) H := Or.inr ⟨L,hL,hq,hX,ha⟩
    obtain ⟨hr, hb⟩ := h.normalClosure_branches_of_conclusion hG orbits residual P hc
    exact ⟨hr, hb.elim Or.inl (Or.inr ∘ Or.inl)⟩
  · have ho := orbits G hG H h.overgroup.1 L hL
    rw [ncard_conjugates_eq_index_normalizer] at ho
    have hLn := normal_of_sylow_normalizes hL.1 hSylow hn (ho.imp_right And.left)
    have hXL : d.wholeX ≤ L := (componentOrbit_eq_of_normalizes hn) ▸ hX
    have hs := simple_of_quasisimple_center_bot hq (held_model_center_bot e)
    have hk := h.normalClosure_eq_component hXL hL.1 hLn (cComponent_twoPerfect hL) hs
    have hr := le_antisymm h.normalClosure_le_residual
      ((held_residual_le hsq hlocal hL hLn hXL e).trans hk.ge)
    refine ⟨hr, Or.inr (Or.inr ?_)⟩
    rw [hk]
    exact ⟨hL, hLn, hq, ⟨e⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
