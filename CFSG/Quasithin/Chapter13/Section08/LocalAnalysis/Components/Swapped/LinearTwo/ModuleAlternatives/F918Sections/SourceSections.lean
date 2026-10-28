module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.SectionDichotomy
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Reduction

/-!
# The maximal-section deduction on the literal source action

The two-core quotient carries the actual conjugate span onto the conjugate
span of the images. Subnormality and the supplied quasisimplicity of K*
make it an ordinary component of H*. The orbit of a perfect subgroup is
perfect. These facts put the literal source representation into the section
argument, and the marked seed supplies full commutator generation and
nontriviality. The selected W retains the nonzero source-seed projection.

The faithful bounded elementary actor and the absence of strong offenders
on the two actual section images remain explicit earlier obligations. This
is a conditional deduction, not the full F.9.18/B.4.2 application in 13.8.16.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
standing setup pp.946–947 and proof of 13.8.16(1), p.952.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
open ComponentSieve.AlternatingAndLinear.FourStructure

variable {G : Type*} [Group G]

/-- Conjugate generation commutes with restriction to an actual overgroup. -/
theorem subgroupOf_conjugateSpan (H K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H) :
    (conjugateSpanBy K T).subgroupOf H =
      conjugateSpanBy (K.subgroupOf H) (T.subgroupOf H) := by
  apply map_injective H.subtype_injective
  rw [Suzuki.map_conjugateSpan, map_subgroupOf_eq_of_le hKH,
    map_subgroupOf_eq_of_le hTH, map_subgroupOf_eq_of_le]
  exact conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)

/-- K₀* is the orbit of K* under the actual T*, with the quotient map retained. -/
theorem star_conjugateSpan (H K T : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H) :
    Source.starImage H (conjugateSpanBy K T) =
      conjugateSpanBy (Source.starImage H K) (Source.starImage H T) := by
  unfold Source.starImage
  rw [subgroupOf_conjugateSpan H K T hKH hTH, Suzuki.map_conjugateSpan]

/-- The source's C-component becomes an ordinary component after its
quasisimplicity in the actual quotient has been supplied. -/
theorem star_isComponent (H K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hq : Theory.GroupTheory.IsQuasisimple (Source.starImage H K)) :
    Theory.GroupTheory.IsComponent (Source.Hstar H) (Source.starImage H K) :=
  ⟨hK.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 H)), hq⟩

/-- An orbit of a perfect subgroup is perfect, without a direct-product assumption. -/
theorem perfect_conjugateSpan (K T : Subgroup G) [Group.IsPerfect K] :
    Group.IsPerfect (conjugateSpanBy K T) := by
  rw [Subgroup.isPerfect_iff]
  apply le_antisymm ((commutator_le_sup _ _).trans (sup_idem _).le)
  apply (closure_le _).mpr
  rintro _ ⟨t, ht, k, hk, rfl⟩
  have hKt : K.conjBy t ≤ conjugateSpanBy K T := by
    rintro _ ⟨x, hx, rfl⟩
    exact subset_closure ⟨t, ht, x, hx, rfl⟩
  have hp : Group.IsPerfect (K.conjBy t) := Group.IsPerfect.map (MulAut.conj t).toMonoidHom
  have he : K.conjBy t ≤ ⁅conjugateSpanBy K T, conjugateSpanBy K T⁆ := by
    rw [← Subgroup.isPerfect_iff.mp hp]
    exact commutator_mono hKt hKt
  exact he (mem_map_of_mem (MulAut.conj t).toMonoidHom hk)

/-- L₁ ≤ K₀ identifies the full actor with K₀*T*, on the actual quotient. -/
theorem star_actor_generated (H K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)) (hL : L₁ ≤ conjugateSpanBy K T) :
    Source.starImage H (conjugateSpanBy K T) ⊔ Source.starImage H T = ⊤ := by
  have he : conjugateSpanBy K T ⊔ T = H := by
    rw [hH, ← sup_assoc, sup_eq_left.mpr hL]
  have hKH : conjugateSpanBy K T ≤ H := he ▸ le_sup_left
  have hTH : T ≤ H := he ▸ le_sup_right
  unfold Source.starImage
  rw [← Subgroup.map_sup, ← subgroupOf_sup hKH hTH, he, subgroupOf_self]
  exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

section Source
variable [Finite G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
  (hρ : ChiefFactors.IsSourceAction H V₃ V₁ ρ)

include hρ

/-- The source-section result used by final assembly. Its two exclusions are
on faithful images of the literal submodule and quotient actions. In branch
(b), I is an actual Irr⁺ section and its whole ambient orbit is Ũ_H.
The T-homogeneous refinement and the model identifications are not asserted. -/
theorem exists_source_section_dichotomy
    (K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)) (hL : L₁ ≤ conjugateSpanBy K T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : Theory.GroupTheory.IsQuasisimple (Source.starImage H K))
    (hLN : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ < V₃)
    (hseed : V₃ ≤ ⁅L₁, V₃⁆ ⊔ V₁)
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : A ⊓ centralizer (Source.starImage H (conjugateSpanBy K T) : Set (Source.Hstar H)) = ⊥)
    (hnW : ∀ W : Subrepresentation ρ, W ≠ ⊤ →
      ¬ W.toSubmodule ≤ fixedSpace ρ (Source.starImage H (conjugateSpanBy K T)) →
      ¬ IsStrongFFModule (imageRepresentation W.toRepresentation))
    (hnQ : ∀ W : Subrepresentation ρ, W ≠ ⊤ →
      ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      (∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W) ∧
      (ChiefFactors.sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
       (subspaceCommutator ρ W.toSubmodule (Source.starImage H (conjugateSpanBy K T)) = ⊥ ∧
        ∃ I, IsIrrPlus ρ (Source.starImage H (conjugateSpanBy K T)) I ∧ seedSpan ρ I = ⊤)) := by
  have hKH : K ≤ H := (le_conjugateSpanBy K T).trans (by rw [hH]; exact le_sup_left)
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_right
  have horbit := star_conjugateSpan H K T hKH hTH
  have hfull := source_moved_eq_top H V₃ V₁ ρ hρ K L₁ T hH hL hLN hline.le hseed
  have htop : (⊤ : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁)) ≠ ⊥ := by
    intro he
    exact seed_ne_bot H V₃ V₁ (not_le_of_gt hline)
      (le_bot_iff.mp (he ▸ (show ChiefFactors.sourceSeedSpace H V₃ V₁ ≤ ⊤ from le_top)))
  obtain ⟨W, havoid, hmax, hproj⟩ := exists_source_maximal_section H V₃ V₁ ρ hρ ⊤ htop
  have hW : W ≠ ⊤ := fun he => havoid (he ▸ le_top)
  have hmax' : ∀ Y : Subrepresentation ρ, W ≤ Y → Y ≠ ⊤ → Y = W := by
    intro Y hWY hY
    apply hmax Y hWY
    intro htopY
    exact hY (Subrepresentation.toSubmodule_injective (top_unique htopY))
  refine ⟨W, hW, hmax', hproj, ?_⟩
  have hd := maximal_section_dichotomy ρ (Source.starImage H K) (Source.starImage H T) A
    (star_isComponent H K hK hq) hA hbound (horbit ▸ hfaith) (horbit ▸ hfull)
    W hW hmax' (horbit ▸ hnW W hW) (hnQ W hW)
  rw [← horbit] at hd
  rcases hd with hff | ⟨hc, hgen⟩
  · exact Or.inl hff
  · refine Or.inr ⟨hc, ?_⟩
    let := hq
    let : Group.IsPerfect (Source.starImage H (conjugateSpanBy K T)) := by
      rw [horbit]
      exact perfect_conjugateSpan _ _
    have hn : ¬ (⊤ : Submodule (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁)) ≤
        fixedSpace ρ (Source.starImage H (conjugateSpanBy K T)) := by
      intro hf
      exact htop (hfull.symm.trans ((subspaceCommutator_eq_bot_iff ρ _ _).mpr hf))
    obtain ⟨I, hI⟩ := exists_isIrrPlus_of_not_fixed ρ _ hn
    exact ⟨I, hI, hgen I hI⟩

end Source
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
