module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowResidualsComponentsSetup
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses

/-!
# The actual C.2.7 enlargement obstruction in the fixed coset

The six-point residual has three-rank two, so its normal containing
C-component has quasisimple two-core quotient. A container inside N(L)
equals the residual, by comparison of components in the local intersection.
Any proper container therefore gives the genuine C.2.7 input with the
original radical, a normal container, and the A6 residual as a component
of its intersection with N(L).

The final theorem applies the equal-component branch to the literal
prime-to-three residual consumer. The proper-enlargement branch remains
to be excluded using the C.2.7 alternatives. This reduction does not
construct CosetComponents or prove the complete source theorem.

Source: Aschbacher--Smith, 3.3.22, printed p.597; C.2.7, pp.145--147.
Final source assembly belongs to qt-d-1235-a7-sylow-ambient-residuals.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)


lemma six_three_rank
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    2 ≤ primeRank 3 P.sixGroup := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 P.sixGroup) pCore_isPGroup,
    primeRank_equiv 3 e6,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]

lemma coset_containing_component_quasisimple
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed) :
    ∃ K : Subgroup (centralizer ({c * (P.six : G)} : Set G)),
      K.IsCComponent ∧ K.Normal ∧
      P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K ∧
      generalizedFitting K = pCore 2 K ∧ IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨K,hK,hn,hBK,hf⟩ := P.coset_containing_component structural M e6 hc
  refine ⟨K,hK,hn,hBK,hf,?_⟩
  apply ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank
    (S.hypothesis.simpleQTKE.twoLocal_sqtk (P.coset_isTwoLocal hc)) hK
  have hr := P.six_three_rank e6
  have he := primeRank_equiv 3 (subgroupOfEquivOfLe (P.sixGroup_le_coset_centralizer hc))
  exact (he ▸ hr).trans
    (_root_.primeRank_le_of_injective 3 (inclusion hBK) (inclusion_injective hBK))

lemma coset_container_eq_of_le_local
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6))
    {c : G} (hc : c ∈ P.fixed)
    {K : Subgroup (centralizer ({c * (P.six : G)} : Set G))}
    (hK : K.IsCComponent)
    (hBK : P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G)) ≤ K)
    (hKM : K.map (centralizer ({c * (P.six : G)} : Set G)).subtype ≤ normalizer (L : Set G)) :
    K.map (centralizer ({c * (P.six : G)} : Set G)).subtype = P.sixGroup := by
  let H := centralizer ({c * (P.six : G)} : Set G)
  let N := H ⊓ normalizer (L : Set G)
  have hKH : (K.map H.subtype).subgroupOf H = K :=
    comap_map_eq_self_of_injective H.subtype_injective K
  have hKN : K.map H.subtype ≤ N := le_inf (map_subtype_le _) hKM
  have hKcomp : ((K.map H.subtype).subgroupOf N).IsCComponent :=
    (hKH.symm ▸ hK).subgroupOf_of_le hKN inf_le_left
  have hBKm : P.sixGroup ≤ K.map H.subtype := by
    intro x hx
    exact ⟨⟨x, P.sixGroup_le_coset_centralizer hc hx⟩, hBK hx, rfl⟩
  have he := (P.coset_local_component e6 hc).eq_of_le hKcomp (comap_mono hBKm)
  apply le_antisymm ?_ hBKm
  intro x hx
  have hxN : (⟨x, hKN hx⟩ : N) ∈ P.sixGroup.subgroupOf N := by
    rw [he]
    exact hx
  exact hxN

/-- The remaining obstruction is an actual proper C.2.7 enlargement,
with the A₆ residual still a component of the literal intersection. -/
theorem coset_components_or_C27_enlargement
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    P.CosetComponents ∨ ∃ c ∈ P.fixed, ∃ K : Subgroup G,
      P.sixGroup < K ∧
      Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
        KnownSimple.IsKnownSimple
        (centralizer ({c * (P.six : G)} : Set G))
        ((L ⊔ (T : Subgroup G)).pCoreIn 2)
        (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
      centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
      (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent := by
  classical
  by_cases hC : P.CosetComponents
  · exact Or.inl hC
  right
  have hbad : ∃ c ∈ P.fixed,
      ¬ (centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (P.sixGroup : Set G) ∧
        (P.sixGroup.subgroupOf (centralizer ({c * (P.six : G)} : Set G))).IsCComponent) := by
    by_contra! h
    exact hC ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩
  obtain ⟨c,hc,hbad⟩ := hbad
  let H := centralizer ({c * (P.six : G)} : Set G)
  obtain ⟨K,hK,hn,hBK,hf,hq⟩ := P.coset_containing_component_quasisimple structural M e6 hc
  let A := K.map H.subtype
  have hAH : A ≤ H := map_subtype_le _
  have hKA : A.subgroupOf H = K := comap_map_eq_self_of_injective H.subtype_injective K
  have hAc : (A.subgroupOf H).IsCComponent := hKA.symm ▸ hK
  have hAn : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hAH).mp (hKA.symm ▸ hn)
  have hBA : P.sixGroup ≤ A := by
    intro x hx
    exact ⟨⟨x, P.sixGroup_le_coset_centralizer hc hx⟩, hBK hx, rfl⟩
  have hne : A ≠ P.sixGroup := by
    intro he
    exact hbad (he ▸ ⟨hAn,hAc⟩)
  have hout : ¬ A ≤ normalizer (L : Set G) := fun hh =>
    hne (P.coset_container_eq_of_le_local e6 hc hK hBK hh)
  have hAf : generalizedFitting A = pCore 2 A := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2
      (K.equivMapOfInjective H.subtype H.subtype_injective)).mp
    rw [← hf]
    exact centralizer_generalizedFitting_le K
  have hAq : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _
      (K.equivMapOfInjective H.subtype H.subtype_injective) (pCore_map_iso 2 _))
  refine ⟨c,hc,A,lt_of_le_of_ne hBA (Ne.symm hne),
    ⟨P.coset_pushingUp_setup structural M hc,⟨hAH,hAc⟩,hAq,hAf,
      fun hh => hout (hh.trans inf_le_right),(P.coset_core_le hc).trans hAn⟩,hAn,?_⟩
  have hBN : P.sixGroup ≤ normalizer (L : Set G) ⊓ A :=
    le_inf ((pointResidual_le L (P.six : G)).trans (inf_le_left.trans L.le_normalizer)) hBA
  exact (P.coset_local_component e6 hc).subgroupOf_of_le hBN
    (le_inf (inf_le_right.trans hAH) inf_le_left)

/-- Apply the genuine fixed-coset component branch to the exact ambient
three-residual consumer. The other branch retains all C.2.7 source inputs. -/
theorem six_residuals_or_C27_enlargement
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) (M : P.Models)
    (e6 : (P.sixGroup ⧸ pCore 2 P.sixGroup) ≃* alternatingGroup (Fin 6)) :
    (∀ c ∈ P.fixed, pointThreeResidual (c * (P.six : G)) = P.sixGroup) ∨
      ∃ c ∈ P.fixed, ∃ K : Subgroup G,
        P.sixGroup < K ∧
        Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
          KnownSimple.IsKnownSimple
          (centralizer ({c * (P.six : G)} : Set G))
          ((L ⊔ (T : Subgroup G)).pCoreIn 2)
          (centralizer ({c * (P.six : G)} : Set G) ⊓ normalizer (L : Set G)) K ∧
        centralizer ({c * (P.six : G)} : Set G) ≤ normalizer (K : Set G) ∧
        (P.sixGroup.subgroupOf (normalizer (L : Set G) ⊓ K)).IsCComponent := by
  rcases P.coset_components_or_C27_enlargement structural M e6 with h | h
  · exact Or.inl (fun _ hc => P.six_residual_of_coset_components h e6 hc)
  · exact Or.inr h

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
