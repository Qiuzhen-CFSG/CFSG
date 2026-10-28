module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Moved
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Held
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Small
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Binary
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Assembly

/-!
# Assembly of the replacement model-generation branches

All small-prime and invariant binary linear rows are discharged. The
odd-prime and Held generation obligations apply inside the
literal I∨T, which equals the component-orbit Sylow join. C-component
inheritance and the exact two-core equivalence preserve the quotient
marking. SQTK is inherited from the original maximal two-local subgroup.

The Held obligation and normal odd-prime row are also discharged below.
The moved odd-prime obligation remains explicit; this is conditional
assembly, not a proof that ModelGenerationAt has been discharged. It does
not assume ClosureAlternativesAt. The last theorem connects this result to
the existing source span assembly, which still needs that independent input.

Source: Aschbacher--Smith 10.3.3 and its final reuse, pp.756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem generation_of_remaining_models
    (hodd : OddPrimeOrbitGeneration.{u}) (hheld : InvariantHeldGeneration.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {M I : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) (hI : I ∈ Chapter1.cComponentsIn M)
    (hq : IsQuasisimple (I ⧸ pCore 2 I))
    (hm : (∃ p : ℕ, p.Prime ∧ Odd p ∧ 7 ≤ p ∧
        ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 p) ∨
      ((T : Subgroup G) ≤ normalizer (I : Set G) ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Held.He))) :
    ChapterE.IsEGenerated 1
      (componentOrbit I (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) := by
  rw [componentOrbit_sup]
  let Y := I ⊔ (T : Subgroup G)
  have hYM : Y ≤ M := sup_le hI.1 hTM
  have hY : IsSQTK KnownSimple.IsKnownSimple Y :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hYM)).mp ((hG.twoLocal_sqtk hM.1).subgroup _)
  let K := I.subgroupOf Y
  let S := T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right)
  have hK : K.IsCComponent := hI.2.subgroupOf_of_le le_sup_left hYM
  let a := subgroupOfEquivOfLe (show I ≤ Y from le_sup_left)
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hqK : IsQuasisimple (K ⧸ pCore 2 K) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv b.symm
  have hKS : K ⊔ (S : Subgroup Y) = ⊤ := by
    change I.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤
    rw [← subgroupOf_sup (show I ≤ Y from le_sup_left)
      (show (T : Subgroup G) ≤ Y from le_sup_right)]
    exact subgroupOf_self Y
  rcases hm with ⟨p, hp, ho, hlarge, hm⟩ | ⟨hn, ⟨e⟩⟩
  · exact hodd Y hY S K hK hqK hKS p hp ho hlarge (hm.of_mulEquiv b)
  · have hnK : K.Normal := normal_subgroupOf_of_le_normalizer (sup_le I.le_normalizer hn)
    exact hheld Y hY S K hK hnK hqK hKS ⟨b.trans e⟩

/-- The exact original contract, conditional only on the two remaining
model branches. No normal-closure classification premise is used. -/
theorem modelGeneration_of_remaining_models
    (hodd : OddPrimeOrbitGeneration.{u}) (hheld : InvariantHeldGeneration.{u}) :
    ModelGenerationAt T := by
  intro _ L D _ _ _ _ _ _ M hM hJM I hI hq _ hm
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hJM
  rcases hm with ⟨n, _, _, hn⟩ | ⟨p, hp, ho, hm⟩ | ⟨hn, k, hk, hm, _⟩ | hh
  · exact Or.inl ⟨n, hn⟩
  · let := hq
    rcases prime_model_binary_or_ge_seven hp ho hm with hb | hlarge
    · exact Or.inl ⟨2, hb⟩
    · exact Or.inr (generation_of_remaining_models hodd hheld D.simpleQTKE hM hTM hI hq
        (Or.inl ⟨p, hp, ho, hlarge, hm⟩))
  · exact Or.inr (invariant_binary_component_isEGenerated D.simpleQTKE T hM hTM hI hn hk hm)
  · exact Or.inr (generation_of_remaining_models hodd hheld D.simpleQTKE hM hTM hI hq
      (Or.inr hh))

/-- Application to the existing span consumer; its separate normal-closure
input remains with its source producer. -/
theorem overgroupSpan_of_remaining_models (hclosure : ClosureAlternativesAt T)
    (hodd : OddPrimeOrbitGeneration.{u}) (hheld : InvariantHeldGeneration.{u}) :
    OvergroupSpanAt T :=
  overgroupSpan_of_source_inputs hclosure (modelGeneration_of_remaining_models hodd hheld)

/-- Only the nonnormal odd-prime component remains: all invariant rows,
including Held and the actual binary-linear automorphism quotients, and
all small primes have been discharged. -/
theorem modelGeneration_of_moved (hmoved : MovedOddPrimeGeneration.{u}) :
    ModelGenerationAt T :=
  modelGeneration_of_remaining_models (oddPrimeOrbitGeneration_of_moved hmoved)
    invariantHeldGeneration

/-- The exact span consumer now retains only its independent closure
classification and the moved odd-prime model input. -/
theorem overgroupSpan_of_moved (hclosure : ClosureAlternativesAt T)
    (hmoved : MovedOddPrimeGeneration.{u}) : OvergroupSpanAt T :=
  overgroupSpan_of_source_inputs hclosure (modelGeneration_of_moved hmoved)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration
