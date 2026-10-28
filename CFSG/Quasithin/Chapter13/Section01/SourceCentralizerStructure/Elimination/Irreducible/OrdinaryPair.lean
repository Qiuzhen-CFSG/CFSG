module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Preparation
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs

/-!
# The actual odd-complement Sylow pair inside the escaping component

The component Sylow normalizes the canonical radical. Its two-core lies in
that Sylow, so either factorization of the radical by its odd complement
shows that the complement permutes with the Sylow. The complement retains
its elementary-square or extraspecial-cube structure. Quotient transport
preserves it through the genuine two-core kernel.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding.InvariantLarge
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- Construct the actual complement and full component Sylow pair. -/
theorem Context.component_oddSylowPair (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) :
    HasOddSylowPair p K := by
  let X := XiP p L
  have hXK : X ≤ K := h.radical_le_component s e hi
  have hshape := (RadicalConjugateRigidity.maximal_radical_structure
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides).1
  let P : Sylow p X := default
  let B₀ := (P : Subgroup X).map X.subtype
  have hBX : B₀ ≤ X := map_subtype_le _
  have hB : XiOddQuotient p B₀ := hshape.of_mulEquiv
    (RadicalActions.ambientSylowQuotientEquiv h.odd hshape.isPGroup P).symm
  obtain ⟨S,hS,hSX⟩ := h.component_sylow e
  let U := (S : Subgroup K).map K.subtype
  have hUK : U ≤ K := map_subtype_le _
  have hUS : IsSylowIn 2 U K := ⟨S,rfl⟩
  have hUJ : IsSylowIn 2 U (X ⊔ U) := hUS.restrict le_sup_right (sup_le hXK hUK)
  have hQ : X.pCoreIn 2 ≤ U := by
    obtain ⟨R,hR⟩ := hUJ
    exact (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le X.le_normalizer hSX)).trans ((pCoreIn_le_sylow (X ⊔ U) R).trans_eq hR)
  have hNQ : B₀ ≤ normalizer (X.pCoreIn 2 : Set G) :=
    hBX.trans (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
  have hfactor : (B₀ : Set G) * (X.pCoreIn 2 : Set G) = X := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hNQ, sup_comm]
    exact congrArg (fun A : Subgroup G => (A : Set G)) (RadicalActions.sylow_sup hshape.isPGroup P)
  have hfactor' : (X.pCoreIn 2 : Set G) * (B₀ : Set G) = X := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hNQ]
    exact congrArg (fun A : Subgroup G => (A : Set G)) (RadicalActions.sylow_sup hshape.isPGroup P)
  have hQU : (X.pCoreIn 2 : Set G) * (U : Set G) = U := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ (hQ.trans U.le_normalizer),sup_eq_right.mpr hQ]
  have hUQ : (U : Set G) * (X.pCoreIn 2 : Set G) = U := by
    rw [← set_mul_normalizer_comm _ U (hQ.trans U.le_normalizer),hQU]
  have hperm : (B₀ : Set G) * (U : Set G) = (U : Set G) * (B₀ : Set G) := by
    calc
      (B₀ : Set G) * (U : Set G) = (X : Set G) * (U : Set G) := by
        rw [← hfactor,mul_assoc,hQU]
      _ = (U : Set G) * (X : Set G) := (set_mul_normalizer_comm _ X hSX).symm
      _ = (U : Set G) * (B₀ : Set G) := by rw [← hfactor',← mul_assoc,hUQ]
  refine ⟨S,B₀.subgroupOf K,hB.of_mulEquiv (subgroupOfEquivOfLe (hBX.trans hXK)).symm,?_⟩
  change (B₀.subgroupOf K : Set K) * ((S : Subgroup K) : Set K) =
    ((S : Subgroup K) : Set K) * (B₀.subgroupOf K : Set K)
  apply Set.image_injective.mpr K.subtype_injective
  simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le (hBX.trans hXK)] using hperm


/-- The odd complement survives the actual quotient K → K/O₂(K). -/
theorem Context.component_quotient_oddSylowPair (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u) : HasOddSylowPair p (XiQuotient K) := by
  apply (h.component_oddSylowPair s e hi).map (QuotientGroup.mk' (pCore 2 K))
    (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  rw [hn]
  exact (h.odd.coprime_two_right).pow_right n

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
