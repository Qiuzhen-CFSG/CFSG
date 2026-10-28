module

public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Contracts
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.Factors
public import Theory.GroupTheory.CComponent.InvolutionCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.GroupTheory.Fitting.Core

/-!
# The ordinary exchanged-component pair

The odd core of the escaping component is trivial.  If its generalized
Fitting subgroup is not its two-core, the component-layer dichotomy and the
Fitting calculation therefore force the actual carrier `K` to be
quasisimple.  The swapped factorization then gives the two literal
order-`p` intersections `P₀ ∩ K` and its displayed conjugate. The generic
pair construction below retains an explicit permutation premise;
`Swapped.Normalizer` discharges it using the two commuting residual factors
and applies the actual canonical-radical normalizer obstruction.

Source: Aschbacher--Smith, 13.1.12(3), printed pp.874--875.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.RadicalExclusions
open Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

set_option linter.unusedSectionVars false in
/-- In the ordinary branch the escaping component is quasisimple on its
literal carrier.  The proof uses the centralizer's trivial odd core, rather
than replacing `K` by either `K / O₂(K)` or `K / Z(K)`. -/
theorem Escape.quasisimple_of_generalizedFitting_ne {u : G} {K : Subgroup G}
    (e : Escape T L p u K)
    (hf : generalizedFitting K ≠ pCore 2 K) : IsQuasisimple K := by
  rcases e.component.2.component_or_generalizedFitting_eq_pCore e.odd_core with hq | he
  · exact hq.2.of_mulEquiv (subgroupOfEquivOfLe e.component.1)
  · apply (hf ?_).elim
    have hm := congrArg (map (subgroupOfEquivOfLe e.component.1).toMonoidHom) he
    simpa only [map_generalizedFitting_equiv,pCore_map_iso] using hm

/-- The two literal factors supplied by `SwappedFactors` form the pair of
order-`p` subgroups needed by the normalizer endpoint, once the displayed normalizer preserves their two-element family. The
commuting residual-factor proof in `Swapped.Normalizer` supplies this premise. -/
theorem Context.ordinary_line_pair_of_permutation
    {u : G} {K : Subgroup G} (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K
      ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (hperm : let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
      ∀ g ∈ L ⊓ normalizer (P₀ : Set G),
        (P₀ ⊓ K).conjBy g = P₀ ⊓ K ∨
        (P₀ ⊓ K).conjBy g = (P₀ ⊓ K).conjBy (Classical.choose d.factors.2)) :
    Nonempty (NormalizerLinePair L
      ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) := by
  let P₀ : Subgroup G := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  let t : G := Classical.choose d.factors.2
  have htall := Classical.choose_spec d.factors.2
  have ht : t ∈ (T : Subgroup G) ⊓ centralizer ({u} : Set G) ⊓
      normalizer P₀ := by
    simpa [t, P₀] using htall.1
  have htN : t ∉ normalizer K := by
    simpa [t] using htall.2.1
  have hgen : P₀ = (P₀ ⊓ K) ⊔ (P₀ ⊓ K).conjBy t := by
    simpa [t, P₀] using htall.2.2.1
  have hdis : Disjoint (P₀ ⊓ K) ((P₀ ⊓ K).conjBy t) := by
    simpa [t, P₀] using htall.2.2.2.1
  have hcomm : ⁅P₀ ⊓ K, (P₀ ⊓ K).conjBy t⁆ = ⊥ := by
    simpa [t, P₀] using htall.2.2.2.2
  let A : Subgroup G := P₀ ⊓ K
  let B : Subgroup G := A.conjBy t
  have hconj : B = P₀ ⊓ K.conjBy t := by
    change (P₀ ⊓ K).map (MulAut.conj t).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj t).injective]
    change P₀.conjBy t ⊓ K.conjBy t = P₀ ⊓ K.conjBy t
    rw [show P₀.conjBy t = P₀ from mem_normalizer_iff_map_conj_eq.mp ht.2]
  have hBP : B ≤ P₀ := hconj ▸ inf_le_left
  have hcardA : Nat.card A = p := by
    simpa [A, P₀] using
      (ModelReduction.swapped_intersection_card d.plane d.factors)
  have hcardB : Nat.card B = p := by
    exact (card_map_of_injective (MulAut.conj t).injective).trans hcardA
  have hne : A ≠ B := by
    intro he
    have hbot : A = ⊥ := by
      apply bot_unique
      intro x hx
      have hxb : x ∈ B := he ▸ (show x ∈ A from hx)
      exact hdis.le_bot ⟨hx, hxb⟩
    have hc := hcardA
    rw [hbot, Subgroup.card_bot] at hc
    exact (Fact.out : p.Prime).ne_one hc.symm
  refine ⟨⟨A, B, inf_le_left, hBP, hcardA, hcardB, hne, ?_⟩⟩
  intro g hg
  simpa [A, B, P₀, t] using hperm g hg

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
