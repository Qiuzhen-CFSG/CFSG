module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.Construction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.ModelExclusions
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.DerivedG2Center
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.SingleOvergroup.Classification

/-!
# The single-factor overgroup restriction

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 15.4.15, printed p.1161.

For two distinct maximal two-local overgroups supporting single factors, the
raw 15.4.12 witnesses construct the actual Goldschmidt triple, symmetric-three
quotients, trivial joined two-core, and characteristic two of both generators.
The authorized universal F.6.5 implication retains all eleven alternatives.
Its Fitting clause eliminates the five small cases. The concrete omega-center
calculations exclude five geometric cases, and the surviving symplectic matrix
model identifies both generators with C₂ × S₄, contradicting exact 15.4.13.

`at_most_one_of_raw_witnesses` proves the conditional source conclusion. The
family and its multiplicity remain parameters for the genuine earlier source
objects; this module does not replace their definitions. The parent supplies
15.4.12–13, the order-four conclusion of 15.4.14, and the universal F.6.5 theorem.
It retains assembly from Hypothesis 15.4.1 and the L₃(2)/A₆ exclusions. The
stronger concrete center calculations make the order-four premise sufficient
here; the available fixed-index/noncentrality premise is not additionally needed.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup

universe u
variable {G : Type u} [Group G]

/-- Two single-factor witnesses in distinct unique maximal two-local
overgroups give the two concrete C₂ × S₄ identifications. The hypotheses are
exactly the used clauses of 15.4.12 and the order-four conclusion of 15.4.14. -/
theorem single_factor_identifications [Finite G]
    (classification : GoldschmidtClassification.{u}) (T : Sylow 2 G)
    {Y₁ Y₂ M₁ M₂ : Subgroup G}
    (hEven : IsEvenCharacteristicAt T)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hTM₁ : (T : Subgroup G) ≤ M₁) (hTM₂ : (T : Subgroup G) ≤ M₂)
    (hY₁M₁ : Y₁ ≤ M₁) (hY₂M₂ : Y₂ ≤ M₂)
    (hn₁ : M₁ ≤ normalizer (Y₁ : Set G)) (hn₂ : M₂ ≤ normalizer (Y₂ : Set G))
    (hi₁ : (pCore 2 Y₁).index = 3) (hi₂ : (pCore 2 Y₂).index = 3)
    (hc₁ : Y₁ = ⁅Y₁, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hc₂ : Y₂ = ⁅Y₂, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hu₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (hu₂ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₂ ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hne : M₁ ≠ M₂) :
    Nonempty ((Y₁ ⊔ (T : Subgroup G) : Subgroup G) ≃*
      (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) ∧
    Nonempty ((Y₂ ⊔ (T : Subgroup G) : Subgroup G) ≃*
      (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
  let A := Y₁ ⊔ (T : Subgroup G)
  let B := Y₂ ⊔ (T : Subgroup G)
  let I := A ⊔ B
  obtain ⟨hint, htriple, hcore, hA, hB⟩ := single_factor_goldschmidt T hEven
    hM₁ hM₂ hTM₁ hTM₂ hY₁M₁ hY₂M₂ hn₁ hn₂ hi₁ hi₂ hc₁ hc₂ hu₁ hu₂ hne
  have hint' : A.subgroupOf I ⊓ B.subgroupOf I = (T : Subgroup G).subgroupOf I := by
    change (A ⊓ B).subgroupOf I = _
    rw [hint]
  have hZ' : Nat.card (Stellmacher.omegaOneCenterAmbient
      (A.subgroupOf I ⊓ B.subgroupOf I)) = 4 := by
    rw [hint', omega_center_card_subgroupOf
      (show (T : Subgroup G) ≤ I from le_sup_right.trans le_sup_left)]
    exact hZ
  obtain ⟨⟨eA⟩, ⟨eB⟩⟩ := goldschmidt_identification classification htriple hcore hA hB hZ'
  exact ⟨⟨(subgroupOfEquivOfLe (show A ≤ I from le_sup_left)).symm.trans eA⟩,
    ⟨(subgroupOfEquivOfLe (show B ≤ I from le_sup_right)).symm.trans eB⟩⟩

/-- The at-most-one conclusion of 15.4.15 from raw earlier source witnesses.
`𝒴` and `s` are parameters for the genuine family and multiplicity: this does
not define replacements for their Chapter 15 owners. The caller supplies the
used 15.4.12 clauses, exact 15.4.13 exclusion, and actual order-four conclusion
of 15.4.14. The universal F.6.5 implication is also explicit. All further
quotient, Sylow, two-core, characteristic-two and model hypotheses are proved.

The parent source assembly obtains these premises from genuine Hypothesis
15.4.1 and the L₃(2)/A₆ exclusions. Those hypotheses need not be repeated here:
the conditional deduction uses only their displayed consequences. -/
theorem at_most_one_of_raw_witnesses [Finite G] {K : GroupClass.{u}}
    (hG : IsSimpleQTKE K G) (classification : GoldschmidtClassification.{u})
    (T : Sylow 2 G) (𝒴 : Set (Subgroup G)) (s : Subgroup G → ℕ)
    (hnormal : ∀ Y ∈ 𝒴, ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Y ≤ M → M ≤ normalizer (Y : Set G))
    (hindex : ∀ Y ∈ 𝒴, (pCore 2 Y).index = 3 ^ s Y)
    (hcomm : ∀ Y ∈ 𝒴, Y = ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hunique : ∀ Y ∈ 𝒴, ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Y ≤ M →
      ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M)
    (earlier13 : ∀ Y ∈ 𝒴, ¬ Nonempty ((Y ⊔ (T : Subgroup G) : Subgroup G) ≃*
      (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))))
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4) :
    Set.Subsingleton {M : Subgroup G | IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M ∧
      ∃ Y ∈ 𝒴, Y ≤ M ∧ s Y = 1} := by
  intro M₁ h₁ M₂ h₂
  by_contra hne
  obtain ⟨hM₁, hTM₁, Y₁, hY₁, hY₁M₁, hs₁⟩ := h₁
  obtain ⟨hM₂, hTM₂, Y₂, hY₂, hY₂M₂, hs₂⟩ := h₂
  have hi₁ : (pCore 2 Y₁).index = 3 := by simpa only [hs₁, pow_one] using hindex Y₁ hY₁
  have hi₂ : (pCore 2 Y₂).index = 3 := by simpa only [hs₂, pow_one] using hindex Y₂ hY₂
  have hid := single_factor_identifications classification T (hG.evenCharacteristic T)
    hM₁ hM₂ hTM₁ hTM₂ hY₁M₁ hY₂M₂
    (hnormal Y₁ hY₁ M₁ hM₁ hTM₁ hY₁M₁) (hnormal Y₂ hY₂ M₂ hM₂ hTM₂ hY₂M₂)
    hi₁ hi₂ (hcomm Y₁ hY₁) (hcomm Y₂ hY₂)
    (hunique Y₁ hY₁ M₁ hM₁ hTM₁ hY₁M₁) (hunique Y₂ hY₂ M₂ hM₂ hTM₂ hY₂M₂) hZ hne
  exact earlier13 Y₁ hY₁ hid.1

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
