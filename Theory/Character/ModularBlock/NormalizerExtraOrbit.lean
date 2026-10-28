module

public import Theory.Character.ModularBlock.NormalizerPrincipalFactor

/-!
# Normalizer orbit sums of primitive extra Brauer factors

A primitive augmentation-zero factor below the extra subgroup Brauer factor
has pairwise equal or orthogonal normalizer conjugates. Their distinct orbit
sum is therefore a nonzero central idempotent, remains below the extra factor,
has augmentation zero, and contains its base member as a factor. Invariance
under the normalizer action supplies the fixed idempotent used by the
maximal-obstruction argument. The embedded-orbit assembly remains a consumer
in Glauberman rather than a prerequisite of principal Brauer equality.

This is the final orbit-sum assembly from
`c3503435:glauberman_zStar/Submission/ZStar/NormalizerBrauerAction.lean`.
The generic action, embedding, and principal-factor APIs are imported from
the lower Theory layer; Glauberman re-exports the historical names. Only the explicitly stated primitive-extra-factor
hypotheses enter the final theorem; no 2-subgroup or block-correspondence
assumption is added.
-/

public section
noncomputable section
namespace ModularBlock.NormalizerBrauerAction
open ModularBlock Subgroup PrincipalBlockConstruction
universe u v
attribute [local instance] Fintype.ofFinite

private theorem finset_sum_isIdempotent_of_pairwise_orthogonal
    {A : Type u} [Ring A]
    (s : Finset A)
    (hidem : ∀ a ∈ s, IsIdempotentElem a)
    (horth : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a * b = 0) :
    IsIdempotentElem (∑ a ∈ s, a) := by
  classical
  let I := {a : A // a ∈ s}
  let e : I → A := fun a => a.1
  have he : OrthogonalIdempotents e := by
    refine ⟨?_, ?_⟩
    · intro a
      exact hidem a.1 a.2
    · intro a b hab
      apply horth a.1 a.2 b.1 b.2
      intro h
      apply hab
      exact Subtype.ext h
  have hsum : (∑ a ∈ s.attach, (a.1 : A)) = ∑ a ∈ s, a :=
    Finset.sum_attach s (fun a : A => a)
  rw [← hsum]
  simpa [I, e] using
    (he.isIdempotentElem_sum (s := (Finset.univ : Finset I)))

/-- The normalizer orbit sum of a primitive augmentation-zero extra factor is
central, idempotent, nonzero, augmentation-zero, remains under the same extra
factor, contains the original primitive factor as a left factor, and is fixed
by the normalizer action. -/
theorem normalizerOrbitSum_primitiveExtraFactor_properties
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hbPrimitive : IsCentrallyPrimitive b)
    (hbAug : groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) b = 0)
    (hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b) :
    let B := normalizerOrbitSum
      (BrauerBlockReduction.principalResidueField d) Q b
    B ∈ Set.center
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer (Q : Set G))) ∧
      IsIdempotentElem B ∧
      B ≠ 0 ∧
      groupAlgebraAugmentation
        (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)) B = 0 ∧
      B * SubgroupPrincipalBrauer.extraBrauerFactor d Q = B ∧
      b * B = b ∧
      ∀ n : Subgroup.normalizer (Q : Set G),
        normalizerConjugate
          (BrauerBlockReduction.principalResidueField d) Q n B = B := by
  dsimp only
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let A := MonoidAlgebra K C
  let s : Finset A := normalizerOrbit K Q b
  let B : A := normalizerOrbitSum K Q b
  have horbit : ∀ c ∈ s,
      IsCentrallyPrimitive c ∧
        groupAlgebraAugmentation K C c = 0 ∧
        c * SubgroupPrincipalBrauer.extraBrauerFactor d Q = c := by
    intro c hc
    rcases (mem_normalizerOrbit_iff (R := K) Q b c).mp hc with ⟨n, rfl⟩
    simpa [normalizerConjugate, K, C] using
      (conjugate_primitiveExtraFactor d Q n b hbPrimitive hbAug hbExtra)
  have hcenter : B ∈ Set.center A := by
    apply (Semigroup.mem_center_iff).2
    intro a
    change a * (∑ c ∈ s, c) = (∑ c ∈ s, c) * a
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    exact (Semigroup.mem_center_iff.mp (horbit c hc).1.1) a
  have horth : ∀ c ∈ s, ∀ e ∈ s, c ≠ e → c * e = 0 := by
    intro c hc e he hne
    have hcprim := (horbit c hc).1
    have heprim := (horbit e he).1
    by_contra hnezero
    have hce : c = e :=
      CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
        hcprim heprim hnezero
    exact hne hce
  have hidem : IsIdempotentElem B := by
    change IsIdempotentElem (∑ c ∈ s, c)
    exact finset_sum_isIdempotent_of_pairwise_orthogonal s
      (fun c hc => (horbit c hc).1.2.1)
      horth
  have hne : B ≠ 0 := by
    intro hzero
    apply hbPrimitive.2.2.1
    have hmem : b ∈ s := by
      exact self_mem_normalizerOrbit (R := K) Q b
    have hleft : b * B = b := by
      change b * (∑ c ∈ s, c) = b
      rw [Finset.mul_sum]
      rw [Finset.sum_eq_single b]
      · exact hbPrimitive.2.1.eq
      · intro c hc hcb
        by_contra hnonzero
        have hcprim := (horbit c hc).1
        have hce : b = c :=
          CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
            hbPrimitive hcprim hnonzero
        exact hcb hce.symm
      · intro hnot
        exact (hnot hmem).elim
    rw [hzero, mul_zero] at hleft
    exact hleft.symm
  have haug : groupAlgebraAugmentation K C B = 0 := by
    change groupAlgebraAugmentation K C (∑ c ∈ s, c) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro c hc
    exact (horbit c hc).2.1
  have hextra : B * SubgroupPrincipalBrauer.extraBrauerFactor d Q = B := by
    change (∑ c ∈ s, c) * SubgroupPrincipalBrauer.extraBrauerFactor d Q =
      ∑ c ∈ s, c
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    exact (horbit c hc).2.2
  have hleft : b * B = b := by
    have hmem : b ∈ s := by
      exact self_mem_normalizerOrbit (R := K) Q b
    change b * (∑ c ∈ s, c) = b
    rw [Finset.mul_sum]
    rw [Finset.sum_eq_single b]
    · exact hbPrimitive.2.1.eq
    · intro c hc hcb
      by_contra hnonzero
      have hcprim := (horbit c hc).1
      have hce : b = c :=
        CentralPrimitiveFactor.eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
          hbPrimitive hcprim hnonzero
      exact hcb hce.symm
    · intro hnot
      exact (hnot hmem).elim
  have hfixed : ∀ n : Subgroup.normalizer (Q : Set G),
      normalizerConjugate K Q n B = B := by
    intro n
    exact normalizerConjugate_orbitSum_eq_self Q n b
  exact ⟨by simpa [A, B, K, C] using hcenter,
    by simpa [A, B, K, C] using hidem,
    by simpa [A, B, K, C] using hne,
    by simpa [A, B, K, C] using haug,
    by simpa [A, B, K, C] using hextra,
    by simpa [A, B, K, C] using hleft,
    by simpa [A, B, K, C] using hfixed⟩

end ModularBlock.NormalizerBrauerAction
