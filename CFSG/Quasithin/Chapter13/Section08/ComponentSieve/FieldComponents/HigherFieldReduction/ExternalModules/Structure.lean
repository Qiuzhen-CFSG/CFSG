module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Centralizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Action
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelTypes
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Fitting
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic

/-!
# Source structure for the external cubic alternative

The cubic image and its noncontainment retain the genuine two-core kernel.
Ambient SQTK bounds the three-rank of the original component K by one.
The exact earlier Fitting alternatives specialize to the selected source X.
Once the component model calculation supplies centerlessness, the solvable
supplement L₁T and the Fitting bound construct a marked S₃ in C_{H*}(K*).
The cubic seed commutators give the actual tensor and paired restrictions
on all literal invariant sections of U_H/V₁.

The higher-field model reduction is published in the sibling
`Structure.ModelReduction` module, and the even-degree L₂ B_C placement is
published in `Structure.MarkedBorel`.  Centerlessness remains an explicit
model output premise of the source action adapter below. No component
restriction, B-centralization, or full external-X exclusion is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20(a), printed pp.954–955 (PDF pp.971–972), using 13.8.14–17 and
the earlier source seed identity V₃ = [V₃,X].
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem component_twoPerfect (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : IsPPerfect 2 K := by
  have : Group.IsPerfect K := by
    let := hK.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKH).toMonoidHom)
      (subgroupOfEquivOfLe hKH).surjective
  intro N hN hp
  let := hN
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro k _
  exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

/-- The source external alternative retains a cubic subgroup outside K*,
normal in H*, and forces three-rank at most one in the original K. -/
theorem external_cubic_rank (κ : GroupClass.{u}) (H K X : Subgroup G)
    (hH : IsSQTK κ H) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [(K.subgroupOf H).Normal] (hX : IsPPerfect 2 X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) (ha : ExternalXAlternative H K X) :
    Nat.card (Source.starImage H X) = 3 ∧
      ¬ Source.starImage H X ≤ Source.starImage H K ∧
      (Source.starImage H X).Normal ∧ primeRank 3 K ≤ 1 := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hc := star_card_three H X ha.1 hcard
  have hn := star_not_le H K X hKH ha.1 (component_twoPerfect H K hKH hK) hX ha.2.1
  refine ⟨hc, hn, (inferInstance : (X.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _), ?_⟩
  rw [threeRank_eq_star H K hKH hK.subnormal]
  exact star_threeRank_le_one κ H K X hH hc hn ha.2.2.1

omit [Finite G] in
private theorem star_sup (H A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
    Source.starImage H (A ⊔ B) = Source.starImage H A ⊔ Source.starImage H B := by
  unfold Source.starImage
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
private theorem triple_not_ordinary (L : Subgroup G)
    (h : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr (centerCongr e).toEquiv
  rw [h.2.1, alternatingGroup.center_eq_bot (by simp), card_bot] at hc
  omega

omit [Finite G] in
/-- Specialize all three earlier 13.8.14 alternatives to the source choice
X = L₁ in the ordinary case and X = L₁,+ in the covered case. The two
local carriers cannot be confused: their centers have different orders. -/
theorem selected_fitting_alternative (H L L₁ L₁plus X : Subgroup G)
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H)) :
    Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X := by
  rcases hfit with h | ⟨hord,he⟩ | ⟨hcov,he⟩
  · exact Or.inl h
  · rcases hlocal with ⟨_,hx⟩ | ⟨hcov,_⟩
    · exact Or.inr (he.trans hx.symm)
    · exact (triple_not_ordinary L hcov hord).elim
  · rcases hlocal with ⟨hord,_⟩ | ⟨_,hx⟩
    · exact (triple_not_ordinary L hcov hord).elim
    · exact Or.inr (he.trans hx.symm)

/-- The exact earlier Fitting residual and H = KL₁T give the actual marked
S₃ embedding once the model calculation establishes centerlessness of K*.
Normal cubic image, trivial two-core, and the two-group centralizer quotient
are proved, not premises. -/
theorem source_symmetric_embedding (H K X L₁ T : Subgroup G)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (L₁ ⊔ T)) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) (ha : ExternalXAlternative H K X)
    (hz : center (Source.starImage H K) = ⊥)
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X) :
    ∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
      Function.Injective s ∧
      s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hPH : L₁ ⊔ T ≤ H := by rw [hgen]; exact le_sup_right
  let P := Source.starImage H (L₁ ⊔ T)
  let : Group.IsSolvable P := by
    let : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hPH).toMonoidHom) (subgroupOfEquivOfLe hPH).injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((L₁ ⊔ T).subgroupOf H))
  have hGP : Source.starImage H K ⊔ P = ⊤ := by
    rw [← star_sup H K (L₁ ⊔ T) hKH hPH, ← hgen]
    simp [Source.starImage, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hF : fittingSubgroup (Source.Hstar H) ≤ Source.starImage H X := by
    rw [← Components.Fitting.twoFittingResidual_star H]
    rcases hfit with hfit | hfit
    · simp [hfit, Source.starImage]
    · rw [hfit]
  exact symmetric_embedding_of_small_fitting H K X ha.2.2.1 hz
    (star_card_three H X ha.1 hcard) P hGP hF ha.2.2.2.2

open Representation Representation.BinaryOffender
open scoped IsMulCommutative

/-- Connect the derived symmetric-three subgroup to cubic generation in the
literal source module. The equivariant tensor and pair maps on its chief
sections are then `sectionTensorEquiv` and `sectionPairEquiv`. -/
theorem source_cubic_action (H K X L₁ T V₃ V₁ : Subgroup G)
    [(K.subgroupOf H).Normal]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (hgen : H = K ⊔ (L₁ ⊔ T)) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3) (ha : ExternalXAlternative H K X)
    (hz : center (Source.starImage H K) = ⊥)
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ) (hseed : V₃ = ⁅V₃, X⁆) :
    ∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
      Function.Injective s ∧
      s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
      subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤ ∧
      ∀ v, ρ (s InvertedCubicTensor.cubic) v = v → v = 0 := by
  obtain ⟨s,hi,hc,hm⟩ := source_symmetric_embedding H K X L₁ T hgen hcard ha hz hfit
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hg := source_commutator_generation H X V₃ V₁ ha.1 ρ hρ hseed
  exact ⟨s,hi,hc,hm,hg,cubic_fixedFree ρ (Source.starImage H X) s hm hg⟩

/-! The model-reduction and source-action interfaces meet here.  The former
supplies the actual surviving carrier and its center calculation; this adapter
retains the component-rank transport through the literal two-core and then
constructs the commuting inverted-cubic action on the source module. -/

/-- Assemble the source structure from an actual surviving component carrier.

The `ExternalCarrier` and centerlessness hypotheses are the outputs of the
higher-field model sieve.  Keeping them as explicit premises avoids importing
the matrix comparison layer into this source-action module while preserving
the genuine multiplicative model supplied by that sieve. -/
theorem source_external_structure
    (κ : GroupClass.{u}) (H K X L₁ T V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(K.subgroupOf H).Normal]
    (hH : IsSQTK κ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : H = K ⊔ (L₁ ⊔ T)) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hX : IsPPerfect 2 X)
    (hcard : Nat.card (X ⧸ pCore 2 X) = 3)
    (ha : ExternalXAlternative H K X)
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X)
    (hmodel : ExternalCarrier (Source.starImage H K))
    (hz : center (Source.starImage H K) = ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hseed : V₃ = ⁅V₃, X⁆) :
    ExternalCarrier (Source.starImage H K) ∧
      primeRank 3 K ≤ 1 ∧
      primeRank 3 (Source.starImage H K) ≤ 1 ∧
      (∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
        Function.Injective s ∧
        s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
        (alternatingGroup (Fin 3)).map s = Source.starImage H X ∧
        subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤ ∧
        ∀ v, ρ (s InvertedCubicTensor.cubic) v = v → v = 0) := by
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hKH : K ≤ H := by
    rw [hgen]
    exact le_sup_left
  have hr := external_cubic_rank κ H K X hH hKH hK hX hcard ha
  have hrstar : primeRank 3 (Source.starImage H K) ≤ 1 := by
    rw [← threeRank_eq_star H K hKH hK.subnormal]
    exact hr.2.2.2
  have hact := source_cubic_action H K X L₁ T V₃ V₁
    hgen hcard ha hz hfit ρ hρ hseed
  exact ⟨hmodel, hr.2.2.2, hrstar, hact⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure

end
