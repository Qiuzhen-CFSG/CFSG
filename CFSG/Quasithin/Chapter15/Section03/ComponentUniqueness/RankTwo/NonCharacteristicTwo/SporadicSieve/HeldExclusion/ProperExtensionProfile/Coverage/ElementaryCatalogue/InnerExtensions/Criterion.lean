module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.Coverage.ElementaryCatalogue.InnerExtensions.Members

/-!
# Soundness of the outer Held extension checker

An elementary binary extension consists of two cosets of its initial node.
Normality inside the full stabilizer forces all five tested conjugates into
these cosets. Faithfulness of the permutation-normalizer action transports
this necessary condition without a realization or quotient-order premise.
An accepted check proves both inclusions against its proposed node.
Source: Aschbacher--Smith 15.3.41--42, p.1138; GLS3 Table 5.3p.
The two-coset proof follows the existing intrinsic ExtensionChecks.Criterion;
its separate 22-row enumeration is not used.
-/

@[expose] public section
open Subgroup Held Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue.InnerExtensions
open Exhaustion.CandidateOrderCertificate.Factors
private theorem mem_join_iff {G : Type*} [Group G] (H : Subgroup G) (g : G)
    [IsElementaryAbelian 2 ↥(H ⊔ Subgroup.zpowers g)] (x : G) :
    x ∈ H ⊔ Subgroup.zpowers g ↔ x ∈ H ∨ g * x ∈ H := by
  let E := H ⊔ Subgroup.zpowers g
  have hg : g ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hH : H ≤ E := le_sup_left
  have hs (y : G) (hy : y ∈ E) : y * y = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy
  have hc (y : G) (hy : y ∈ E) : g * y = y * g := setLike_mul_comm hg hy
  have hmem (y : G) (hy : y ∈ H ∨ g * y ∈ H) : y ∈ E := by
    rcases hy with hy | hy
    · exact hH hy
    · have hm := E.mul_mem hg (hH hy)
      simpa only [← mul_assoc, hs g hg, one_mul] using hm
  let K : Subgroup G :=
    { carrier := {y | y ∈ H ∨ g * y ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        intro a b ha hb
        have haE := hmem a ha
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (H.mul_mem ha hb)
        · right
          have hm := H.mul_mem ha hb
          rw [← mul_assoc, ← hc a haE, mul_assoc] at hm
          exact hm
        · right
          simpa only [mul_assoc] using H.mul_mem ha hb
        · left
          have hm := H.mul_mem ha hb
          have he : (g * a) * (g * b) = a * b := by
            rw [hc a haE, mul_assoc, ← mul_assoc g g b, hs g hg, one_mul]
          rwa [he] at hm
      inv_mem' := by
        intro a ha
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hs a (hmem a ha))
        rwa [hai] }
  constructor
  · intro hx
    have hle : E ≤ K := sup_le (fun y hy => Or.inl hy)
      (Subgroup.zpowers_le.mpr (Or.inr (by simpa only [hs g hg] using H.one_mem)))
    exact hle hx
  · exact hmem x


private theorem inner_injective : Function.Injective inner := by
  intro x y h
  have he : innerEmbedding x.val = innerEmbedding y.val := by
    apply normalizerAction_injective
    rw [normalizerAction_innerEmbedding, normalizerAction_innerEmbedding]
    exact congrArg Subtype.val h
  have hp : representation x.val = representation y.val :=
    congrArg (fun z : PermutationNormalizer => z.val) he
  exact Subtype.ext (Held.representation_injective hp)

private theorem memberCheck_of_lift_mem (i : Option (Fin 4))
    (x : PermutationNormalizer) (y : outerRepresentative)
    (hxy : permutationGroup.normalizerMonoidHom x = y.val) (hy : y ∈ node i) :
    memberCheck i x.val = true := by
  obtain ⟨n, hn, rfl⟩ := (node_members i y).mp hy
  have he : x = elementLift (false, n) := by
    apply normalizerAction_injective
    rw [elementLift_action]
    exact hxy
  rw [he, elementLift_val]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
  exact List.any_eq_true.mpr ⟨n, hn, same_refl _⟩

theorem memberCheck_rho (i : Option (Fin 4)) (x : pureTwo) :
    memberCheck i (rho x) = true ↔ inner x ∈ node i := by
  constructor
  · intro h
    obtain ⟨n, hn, he⟩ := List.any_eq_true.mp h
    rw [normalTable_eq] at he
    rw [same_rho.mp he]
    exact (node_members i _).mpr ⟨n, hn, element_inner n⟩
  · intro h
    exact memberCheck_of_lift_mem i (innerEmbedding x.val) (inner x)
      (normalizerAction_innerEmbedding x.val) h

private theorem cosetCheck_of_lift_mem (i : Option (Fin 4)) (n : Fin 1024)
    [IsElementaryAbelian 2 (extension i (false, n))]
    (x : PermutationNormalizer) (y : outerRepresentative)
    (hxy : permutationGroup.normalizerMonoidHom x = y.val)
    (hy : y ∈ extension i (false, n)) : cosetCheck i n x.val = true := by
  let : IsElementaryAbelian 2 ↥(node i ⊔ zpowers (element (false, n))) :=
    inferInstanceAs (IsElementaryAbelian 2 (extension i (false, n)))
  rcases (mem_join_iff (node i) (element (false, n)) y).mp hy with hy | hy
  · simp only [cosetCheck, Bool.or_eq_true]
    exact Or.inl (memberCheck_of_lift_mem i x y hxy hy)
  · simp only [cosetCheck, Bool.or_eq_true]
    right
    have hm := memberCheck_of_lift_mem i (elementLift (false, n) * x)
      (element (false, n) * y) (by rw [map_mul, elementLift_action, hxy]; rfl) hy
    change memberCheck i ((elementLift (false, n)).val * x.val) = true at hm
    simpa only [elementLift_val, Bool.false_eq_true, ↓reduceIte, mul_one] using hm

theorem cosetCheck_rho (i : Option (Fin 4)) (n : Fin 1024)
    [IsElementaryAbelian 2 (extension i (false, n))] (x : pureTwo) :
    cosetCheck i n (rho x) = true ↔ inner x ∈ extension i (false, n) := by
  let : IsElementaryAbelian 2 ↥(node i ⊔ zpowers (element (false, n))) :=
    inferInstanceAs (IsElementaryAbelian 2 (extension i (false, n)))
  rw [cosetCheck, Bool.or_eq_true, normalTable_eq, ← map_mul,
    memberCheck_rho, memberCheck_rho, map_mul, ← element_inner]
  exact (mem_join_iff (node i) (element (false, n)) (inner x)).symm

/-- The literal node equality follows from the finite check and precisely the two
hypotheses in the final extension contract. -/
theorem eq_target_of_check (i : Option (Fin 4)) (n : Fin 1024)
    (hc : branchCheck i n = true)
    (hn : (extension i (false, n)).Normal)
    (he : IsElementaryAbelian 2 (extension i (false, n))) :
    extension i (false, n) = node (target i n) := by
  let := he
  have hs : squareCheck n = true := by
    rw [squareCheck, normalTable_eq, ← map_mul, ← map_one rho]
    apply same_rho.mpr
    apply inner_injective
    rw [map_mul, map_one, ← element_inner]
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (element (false, n)) (element_mem_extension i (false, n))
  have hcomm : commuteCheck i n = true := by
    apply List.all_eq_true.mpr
    intro w hw
    rw [normalTable_eq, wordAction_eq, ← map_mul, ← map_mul]
    apply same_rho.mpr
    apply inner_injective
    rw [map_mul, map_mul, ← element_inner]
    exact setLike_mul_comm (element_mem_extension i (false, n))
      (mem_sup_left (word_mem_node i w hw))
  have hconj : conjugateCheck i n = true := by
    apply List.all_eq_true.mpr
    intro k _
    have ht := cosetCheck_of_lift_mem i n
      ((testLift k)⁻¹ * elementLift (false, n) * testLift k)
      ((testActor k)⁻¹ * element (false, n) * testActor k)
      (by simp only [map_mul, map_inv, elementLift_action, testLift_action,
            Subgroup.coe_mul, Subgroup.coe_inv])
      (hn.conj_mem' _ (element_mem_extension i (false, n)) (testActor k))
    change cosetCheck i n
      ((testLift k).val⁻¹ * (elementLift (false, n)).val * (testLift k).val) = true at ht
    simpa only [← testAction_eq, elementLift_val, Bool.false_eq_true, ↓reduceIte,
      mul_one] using ht
  have ha : acceptedCheck i n (target i n) = true := by
    simpa only [branchCheck, hs, hcomm, hconj, Bool.not_true, Bool.false_or] using hc
  simp only [acceptedCheck, Bool.and_eq_true] at ha
  obtain ⟨⟨hx, hi⟩, hj⟩ := ha
  apply le_antisymm
  · apply sup_le
    · apply node_le_of_generators
      intro w hw
      apply (memberCheck_rho _ _).mp
      rw [← wordAction_eq]
      exact List.all_eq_true.mp hi w hw
    · apply zpowers_le.mpr
      rw [element_inner]
      apply (memberCheck_rho _ _).mp
      rwa [← normalTable_eq]
  · apply node_le_of_generators
    intro w hw
    apply (cosetCheck_rho i n _).mp
    rw [← wordAction_eq]
    exact List.all_eq_true.mp hj w hw

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion.ProperExtensionProfile.CoverageData.ElementaryCatalogue.InnerExtensions
