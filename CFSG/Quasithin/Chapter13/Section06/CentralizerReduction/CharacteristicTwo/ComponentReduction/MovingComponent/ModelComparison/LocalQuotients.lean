module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import Theory.SpecificGroups.ProjectiveLinearThree

/-!
# The three component quotients in the moving branch

For a component K of H with O(H) = 1, subnormal inheritance gives O(K) = 1,
so Z(K) = O₂(K). We compare its intrinsic two-core quotient, its actual
image in H/O₂(H), and its actual image in N_H(K)/C_H(K). The last comparison
is the normalizer action's central-quotient equivalence, including its
formula on elements of K. No central cover is discarded.

The moving hypothesis removes the normal case of the genuine 1.2.1(3)
conclusion. The PSL₂ model then supplies three-divisibility on all three
quotients, in particular the literal image used in 1.2.2(a).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.2.1(3) and 1.2.2(a), printed p.504; proof of 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open Chapter1.Section02
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
/-- Simplicity is inherited from the component's central quotient. -/
theorem componentImage_simple {K : Subgroup H} (hK : IsComponent H K) :
    IsSimpleGroup (NormalizerAction.componentImage K) := by
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  exact (NormalizerAction.componentCentralQuotientEquiv K).symm.isSimpleGroup

omit [Finite H] in
/-- Perfectness also passes through the actual component-image equivalence. -/
theorem componentImage_perfect {K : Subgroup H} (hK : IsComponent H K) :
    Group.IsPerfect (NormalizerAction.componentImage K) := by
  let := hK.2
  let : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  exact Group.IsPerfect.ofSurjective
    (f := (NormalizerAction.componentCentralQuotientEquiv K).toMonoidHom)
    (NormalizerAction.componentCentralQuotientEquiv K).surjective

/-- Odd-core vanishing identifies the entire center, including nontrivial covers. -/
theorem component_center_eq_twoCore (hodd : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) : center K = pCore 2 K := by
  let := hK.2
  exact IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hodd K)

/-- The intrinsic two-core quotient is the literal component image in N/C. -/
noncomputable def componentTwoCoreEquivImage (hodd : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) :
    (K ⧸ pCore 2 K) ≃* NormalizerAction.componentImage K :=
  (QuotientGroup.quotientMulEquivOfEq
    (component_center_eq_twoCore hodd hK).symm).trans
      (NormalizerAction.componentCentralQuotientEquiv K)

/-- Both quotient maps send an element of K to the same normalizer action. -/
theorem componentTwoCoreEquivImage_mk (hodd : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (k : K) :
    (componentTwoCoreEquivImage hodd hK (QuotientGroup.mk' (pCore 2 K) k) :
      NormalizerAction.Star K) = NormalizerAction.componentMap K k := rfl

/-- Comparison with the actual component image in the ambient two-core quotient. -/
noncomputable def ambientTwoCoreImageEquiv (hodd : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) :
    K.map (QuotientGroup.mk' (pCore 2 H)) ≃* NormalizerAction.componentImage K :=
  (cComponentTwoCoreQuotientEquiv hK.isCComponent).symm.trans
    (componentTwoCoreEquivImage hodd hK)

/-- The ambient-quotient comparison also respects the literal maps from K. -/
theorem ambientTwoCoreImageEquiv_mk (hodd : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) (k : K) :
    (ambientTwoCoreImageEquiv hodd hK
      ⟨QuotientGroup.mk' (pCore 2 H) (k : H), mem_map_of_mem _ k.property⟩ :
        NormalizerAction.Star K) = NormalizerAction.componentMap K k := by
  change ((componentTwoCoreEquivImage hodd hK)
    ((cComponentTwoCoreQuotientEquiv hK.isCComponent).symm
      ((cComponentTwoCoreQuotientEquiv hK.isCComponent)
        (QuotientGroup.mk' (pCore 2 K) k))) : NormalizerAction.Star K) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [Finite H] in
/-- The moving hypothesis selects the two-conjugate clause, with its actual models. -/
theorem moving_index_and_model (U K : Subgroup H)
    (hmove : ¬ U ≤ normalizer (K : Set H))
    (h121 : K.Normal ∨
      (Set.range fun g : H => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
        NonnormalCComponentModel (K ⧸ pCore 2 K)) :
    (normalizer (K : Set H)).index = 2 ∧
      NonnormalCComponentModel (K ⧸ pCore 2 K) := by
  rcases h121 with hn | ⟨hi, hm⟩
  · let := hn
    exact (hmove le_normalizer_of_normal).elim
  · exact ⟨(ncard_conjugates_eq_index_normalizer K).symm.trans hi, hm⟩

/-- Transport the full nonnormal model list to the faithful component image. -/
theorem moving_index_and_image_model (hodd : pPrimeCore 2 H = ⊥)
    (U K : Subgroup H) (hK : IsComponent H K)
    (hmove : ¬ U ≤ normalizer (K : Set H))
    (h121 : K.Normal ∨
      (Set.range fun g : H => K.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
        NonnormalCComponentModel (K ⧸ pCore 2 K)) :
    (normalizer (K : Set H)).index = 2 ∧
      NonnormalCComponentModel (NormalizerAction.componentImage K) := by
  obtain ⟨hi, hm⟩ := moving_index_and_model U K hmove h121
  exact ⟨hi, hm.of_mulEquiv (componentTwoCoreEquivImage hodd hK).symm⟩

/-- PSL₂ has a genuine cubic element; this is independent of its field parameter. -/
theorem psl2_three_divides {Q : Type*} [Group Q] {q : ℕ}
    (hmodel : ClassicalGroup.IsPSL Q 2 q) : 3 ∣ Nat.card Q := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hmodel
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)

/-- The divisibility input for 1.2.2(a), on its actual ambient quotient image. -/
theorem psl2_three_divides_quotients (hodd : pPrimeCore 2 H = ⊥)
    {K : Subgroup H} (hK : IsComponent H K) {m : ℕ}
    (hmodel : ClassicalGroup.IsPSL (NormalizerAction.componentImage K) 2 (2 ^ m)) :
    3 ∣ Nat.card (NormalizerAction.componentImage K) ∧
      3 ∣ Nat.card (K ⧸ pCore 2 K) ∧
      3 ∣ Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  have hthree := psl2_three_divides hmodel
  refine ⟨hthree, ?_, ?_⟩
  · rwa [Nat.card_congr (componentTwoCoreEquivImage hodd hK).toEquiv]
  · rwa [Nat.card_congr (ambientTwoCoreImageEquiv hodd hK).toEquiv]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
