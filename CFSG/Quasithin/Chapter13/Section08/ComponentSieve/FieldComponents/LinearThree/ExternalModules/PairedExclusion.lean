module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
/-!
# Excluding the ordinary-A₆ external component

A noncentral component action supplies a literal noncentral chief section.
The cubic commutator identity, generalized-Fitting product, and full
conjugation image determine its paired restriction and make the section
faithful. The earlier single-factor bounds exclude actors inside the
component; the proved outer-actor calculation excludes the remaining actors.
An actual actor witnessing q ≤ 2 therefore gives a contradiction.

Only the single-Steinberg and natural-dual bounds from B.4 remain earlier
representation inputs. Chief-factor existence, pairing, section faithfulness
and the outer numerical exclusion are proved, rather than assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1), ordinary-A₆ paragraph, printed p.956.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
/-- The complete conditional representation exclusion for the ordinary-A₆
configuration, preserving the actual acting group and its component kernel. -/
theorem paired_configuration_exclusion
    (ρ : Representation (ZMod 2) H U) (K X : Subgroup H) [K.Normal] [X.Normal]
    (eK : K ≃* BinaryLinearThree.Group) (hs : PairedStructure K X)
    (hgen : subspaceCommutator ρ ⊤ X = ⊤)
    (hn : ∃ k : K, ∃ v, ρ k v ≠ v)
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (hsmall : quadraticRatio ρ ≤ 2) : False := by
  obtain ⟨L, N, hLN, hnK⟩ := exists_noncentral_chief_section_of_linearThree ρ K eK hn
  have hp := paired_noncentral_chief_factors ρ K X eK hs hgen L N hLN hnK
  have hfaith := external_chief_section_faithful ρ K X eK hs.card_three
    hs.commute hs.fitting hgen L N hLN hnK
  have hsetup : OuterActors.PairedSetup (sectionRepresentation ρ L N) K X eK :=
    { component_normal := inferInstance
      cyclic_normal := inferInstance
      cyclic := isCyclic_of_prime_card hs.card_three
      cyclic_order := hs.card_three
      commute := fun k hk x hx => hs.commute ⟨k,hk⟩ ⟨x,hx⟩
      disjoint := hs.disjoint.eq_bot
      fitting := hs.fitting
      faithful := hfaith
      irreducible := chief_section_irreducible ρ L N hLN
      moved := section_generated_of_card_three ρ X hs.card_three hgen L N
      full_conjugation := by
        intro α
        obtain ⟨h, hh⟩ := hs.full_conjugation α
        exact ⟨h, fun k => by
          simpa only [MulAut.conjNormal_apply] using congrArg (fun a : MulAut K => (a k : H)) hh⟩
      paired := hp }
  obtain ⟨A, hA, hq, hc, hout⟩ :=
    exists_quadratic_actor_outside_component ρ K eK L N hp hS hND hsmall
  have hl := OuterActors.paired_outer_bound (sectionRepresentation ρ L N) K X eK hsetup
    A hA (quadratic_section ρ L N hq) hout
  have hu := fixedCodim_section_le ρ L N A
  omega

section Source
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
    (J V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH J V₃)).Normal]
    [IsMulCommutative (Source.Utilde J V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde J V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde J V₃ V₁))]

/-- The ordinary-A₆ exclusion on the actual U_H/V₁ conjugation action.
The source owner supplies the structural identifications and earlier B.4
bounds; neither the chief-factor pairing nor its numerical contradiction is
an input. This is one branch of 13.8.21(1), not the containment theorem. -/
theorem source_paired_configuration_exclusion
    (act : SourceAction J V₃ V₁) (K L₁ : Subgroup G)
    [(Source.starImage J K).Normal] [(Source.starImage J L₁).Normal]
    (eK : Source.starImage J K ≃* BinaryLinearThree.Group)
    (hs : PairedStructure (Source.starImage J K) (Source.starImage J L₁))
    (hgen : subspaceCommutator act.representation ⊤ (Source.starImage J L₁) = ⊤)
    (hn : ∃ k : Source.starImage J K, ∃ v, act.representation k v ≠ v)
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (hsmall : quadraticRatio act.representation ≤ 2) : False :=
  paired_configuration_exclusion act.representation _ _ eK hs hgen hn hS hND hsmall
end Source
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
