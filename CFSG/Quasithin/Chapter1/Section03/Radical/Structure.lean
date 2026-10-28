module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Identification
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.SinglePrime

/-!
# Structural deductions for the radical family

The quotient-shape and single-prime centralizer deductions use the full
A.3.6 alternatives through the actual local quotient equivalence. The
normal-or-quasisimple implication in A.3.8(3) supplies T-invariance. This
module combines those results with the corrected coprime omega normalizer
argument and with maximal two-local uniqueness from 1.2.7(3).

All earlier-source implications remain explicit universal parameters. The
single-prime characteristic-normalizer conclusion below discharges its
quotient-shape and self-centralizer premises; it retains higher homocyclic
exponents. The normalizer equality uses a nontrivial intrinsic two-core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proofs of
Lemma 1.3.3 and Proposition 1.3.8, printed pp.509 and 512–513. Irreducibility,
the quaternion action and identification of the maximal component still
remain for the full radical structure theorem.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter1
open Section02 RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

/-- In the single-prime case, the full A.3.6 structure supplies the hypotheses
of the coprime omega normalizer argument, including the self-centralizer bound.
The earlier uniqueness result is used only after relative normality is proved. -/
theorem radical_singlePrime_normalizers_of_source {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L₀ : Subgroup G}
    (h127 : ∀ K ∈ LStar G T,
      IsMaximalTwoLocal (normalizer (componentOrbit K T : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K T : Set G))
    (hL : L₀ ∈ LStar G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) → q = p) :
    L₀ ≤ normalizer (radicalCore p L₀ T : Set G) ∧
      characteristicNormalizerClosure (radicalCore p L₀ T) ≤ normalizer (L₀ : Set G) := by
  have hT := radicalLocal_invariant_of_A38 hA38 hL.1 hQ hn
  obtain ⟨_, hshape, hcentral⟩ := XiP_singlePrime_structure_of_A36 hA36 hL.1 hQ hn hd hs
  have hnorm := L_normalizes_radicalCore_of_singlePrime_relative p ho L₀ T hL.1.2.1 hT
    hshape hcentral
  exact ⟨hnorm, characteristicNormalizerClosure_le_of_L_normalizes p
    (radical_normalizer_maximal_of_127 h127 hL hT).2 hnorm⟩

/-- The radical of a maximal component has the same normalizer as the component.
The nontrivial intrinsic two-core is obtained from 1.1.3(1) and 1.1.4(6),
so maximal two-locality is applied to an actual two-local overgroup. -/
theorem XiP_normalizer_structure_of_source {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L₀ : Subgroup G}
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (h127 : ∀ K ∈ LStar G T,
      IsMaximalTwoLocal (normalizer (componentOrbit K T : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K T : Set G))
    (hL : L₀ ∈ LStar G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    normalizer (L₀ : Set G) = normalizer (XiP p L₀ : Set G) ∧
      IsMaximalTwoLocal (normalizer (L₀ : Set G)) ∧
      L₀ ⊔ T ≤ normalizer (L₀ : Set G) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → L₀ ⊔ T ≤ M →
        M = normalizer (L₀ : Set G) := by
  have hT := radicalLocal_invariant_of_A38 hA38 hL.1 hQ hn
  have hq := (XiP_oddQuotient_of_A36 hA36 hL.1 hQ hn ho hd).2
  have hcore := XiP_pCoreIn_ne_bot (Fact.out : p.Prime) hL.1 hT hq h113 h114
  obtain ⟨hmax, hunique⟩ := radical_normalizer_maximal_of_127 h127 hL hT
  exact ⟨XiP_normalizer_eq_of_maximalTwoLocal p L₀ hmax hcore, hmax,
    sup_le L₀.le_normalizer hT, hunique⟩

/- The source Lemma 1.3.3: each radical constructed from a nonsimple local
component satisfies the defining conditions of `Xi`. The quotient and action
clauses are discharged through the actual A.3.6 model alternatives, while
normality of the component in the local join supplies the required
`T`-invariance. -/
theorem lemma_1_3_3 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Subgroup G}
    (hQ : ∀ L₀ ∈ L G T,
      IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G))) :
    XiRad G T ⊆ Xi G T := by
  intro X hX
  obtain ⟨L₀, hL, hn, p, hp, ho, hd, rfl⟩ := hX
  let _ : Fact p.Prime := ⟨hp⟩
  have hlocal := hQ L₀ hL
  have hT := radicalLocal_invariant_of_A38 hA38 hL hlocal hn
  refine ⟨XiP_isPPerfect p L₀, XiP_invariant p hT, XiP_join_mem_H p hL, ?_, ?_⟩
  · exact ⟨p, hp, ho,
      (XiP_oddQuotient_of_A36 hA36 hL hlocal hn ho hd).2⟩
  · exact RadicalActions.XiP_irreducible_of_A36 hA36 hL hlocal hn hT ho hd

/- The identification at the beginning of the proof of Proposition 1.3.8,
with the uniform irreducibility premise discharged by Lemma 1.3.3. -/
theorem XiRadStar_identification_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Subgroup G}
    (hQ : ∀ L₀ ∈ L G T,
      IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    {X : Subgroup G} (hXrad : X ∈ XiRadStar G T) :
    ∃ L₀ ∈ LStar G T, ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
      ¬ IsQuasisimple (XiQuotient L₀) ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      X = XiP p L₀ ∧ (X.subgroupOf L₀).Characteristic := by
  have hX : X ∈ Xi G T := lemma_1_3_3 hA36 hA38 hQ hXrad.1
  apply XiRadStar_identification_of_source hA36 hA38 hQ
  · intro K hK hn hTK q hq ho hd
    let _ : Fact q.Prime := ⟨hq⟩
    exact RadicalActions.XiP_irreducible_of_A36 hA36 hK (hQ K hK) hn hTK ho hd
  · exact hXrad
  · exact hX

/- The complete structural package needed by the first reductions in the
proof of Proposition 1.3.8. The single-prime conclusion is retained as an
explicit implication, so the higher-homocyclic case is not collapsed. -/
theorem XiRadStar_structure_of_source {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Subgroup G}
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G)
    (h127 : ∀ K ∈ LStar G T,
      IsMaximalTwoLocal (normalizer (componentOrbit K T : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K T : Set G))
    (hQ : ∀ L₀ ∈ L G T,
      IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    {X : Subgroup G} (hXrad : X ∈ XiRadStar G T) :
    ∃ L₀ ∈ LStar G T, ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
      ¬ IsQuasisimple (XiQuotient L₀) ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      X = XiP p L₀ ∧ (X.subgroupOf L₀).Characteristic ∧
      ∃ P : Sylow p X,
        (let P₀ := (P : Subgroup X).map X.subtype
         (∀ A : Subgroup (P₀ ⧸ frattini P₀),
            (∀ g : (L₀ ⊓ normalizer P₀ : Subgroup G), ∀ a ∈ A,
              frattiniConjugationAction (L₀ ⊓ normalizer P₀) P₀ inf_le_right g a ∈ A) →
              A = ⊥ ∨ A = ⊤) ∧
         ¬ IsCyclic (XiEmbedding.automizer T P₀)) ∧
      normalizer (L₀ : Set G) = normalizer (X : Set G) ∧
      IsMaximalTwoLocal (normalizer (L₀ : Set G)) ∧
      L₀ ⊔ T ≤ normalizer (L₀ : Set G) ∧
      (∀ M : Subgroup G, IsMaximalTwoLocal M → L₀ ⊔ T ≤ M →
        M = normalizer (L₀ : Set G)) ∧
      (∀ _hs : ∀ q : ℕ, q.Prime → Odd q →
          q ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) → q = p,
        pCore p (XiQuotient L₀) = generalizedFitting (XiQuotient L₀) ∧
        (IsMulCommutative (pCore p (XiQuotient L₀)) ∨
          ∀ x : pCore p (XiQuotient L₀), x ^ p = 1) ∧
        centralizer (pCore p (XiQuotient L₀) : Set (XiQuotient L₀)) ≤
          pCore p (XiQuotient L₀) ∧
        L₀ ≤ normalizer (radicalCore p L₀ T : Set G) ∧
        characteristicNormalizerClosure (radicalCore p L₀ T) ≤
          normalizer (L₀ : Set G)) := by
  obtain ⟨L₀, hL, p, hp, ho, hp3, hn, hd, heq, hchar⟩ :=
    XiRadStar_identification_of_A36 hA36 hA38 hQ hXrad
  let _ : Fact p.Prime := ⟨hp⟩
  subst X
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := XiP p L₀)
  have hlocal := hQ L₀ hL.1
  have hnorm := XiP_normalizer_structure_of_source hA36 hA38 h113 h114 h127
    hL hlocal hn ho hd
  have hi := RadicalActions.XiP_normalizer_irreducible_of_A36 hA36 hL.1 hlocal
    hn ho hd P
  have hcyc := RadicalActions.XiP_automizer_not_isCyclic_of_A36 hA36 hL.1
    hlocal hn ho hd P
  refine ⟨L₀, hL, p, hp, ho, hp3, hn, hd, rfl, ?_, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hchar
  · exact ⟨hi, hcyc⟩
  · exact hnorm.1
  · exact hnorm.2.1
  · exact hnorm.2.2.1
  · exact hnorm.2.2.2
  · intro hs
    obtain ⟨hq, hshape, hcentral⟩ := XiP_singlePrime_structure_of_A36 hA36 hL.1
      hlocal hn hd hs
    obtain ⟨hnormR, hcontrol⟩ := radical_singlePrime_normalizers_of_source hA36 hA38
      h127 hL hlocal hn ho hd hs
    exact ⟨hq, hshape, hcentral, hnormR, hcontrol⟩

end CFSG.Quasithin.Chapter1
