module
public import Theory.Representation.InvertedCubicTensor.QuadraticOffenders
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.Cubic

/-!
# Faithful multiplicity actions for the outside-component branches

The commuting symmetric-three action halves fixed codimension. A genuine
quadratic actor first centralizes the normal cubic by the dimension bound,
then centralizes the entire symmetric-three action by the common-centralizer
bound. Its action on the literal inverter-fixed multiplicity space is faithful
and FF, with the original component as generalized Fitting subgroup.

Source: Aschbacher–Smith 14.7.42 and F.9.18, printed pp.1061–1062,325–326.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

universe u
variable {D V : Type u} [Group D] [Finite D]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The actual quadratic actor yields a faithful FF multiplicity action of
its join with the component. -/
theorem faithful_ff_multiplicity
    (ρ : Representation (ZMod 2) D V) (hf : Function.Injective ρ)
    (K X : Subgroup D) [K.Normal] [X.Normal] [IsQuasisimple K]
    (hx : Nat.card X = 3)
    (hcommon : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ hsE : ∀ (g : (K ⊔ A : Subgroup D)) t, Commute (g : D) (s t),
      let μ := multiplicity (ρ.comp s) (ρ.comp (K ⊔ A : Subgroup D).subtype)
        (ambient_commute ρ (K ⊔ A : Subgroup D).subtype s hsE)
      Function.Injective μ ∧ IsOffender μ (A.subgroupOf (K ⊔ A)) ∧
      generalizedFitting (K ⊔ A : Subgroup D) = K.subgroupOf (K ⊔ A) := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hfree : ∀ v, (ρ.comp s) cubic v = v → v = 0 :=
    ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg)
  have hd : 4 < Module.finrank (ZMod 2) V :=
    four_lt_finrank_of_perfect (ρ.comp s) (ρ.comp K.subtype)
      (ambient_commute ρ K.subtype s hs) hfree (hf.comp K.subtype_injective)
  have hAX : A ≤ centralizer (X : Set D) := by
    by_contra hn
    obtain ⟨hr,hhalf⟩ := normalThree_quadratic_rank_fixedCodim ρ hf X
      inferInstance hx hg A hA hquad hn
    omega
  have hsc : s.range ≤ centralizer (K : Set D) := by
    rintro _ ⟨g,rfl⟩ k hk
    exact (hs ⟨k,hk⟩ g).eq
  have hAC : A ≤ centralizer (s.range : Set D) :=
    (elementary_centralizes_component_centralizer K X A hx hcommon hA.2 hAX).trans
      (centralizer_le hsc)
  have hKC : K ≤ centralizer (s.range : Set D) := by
    intro k hk t ht
    obtain ⟨g,rfl⟩ := ht
    exact (hs ⟨k,hk⟩ g).symm.eq
  let E := K ⊔ A
  have hsE : ∀ (g : E) t, Commute (g : D) (s t) := by
    intro g t
    exact ((sup_le hKC hAC) g.property (s t) ⟨t,rfl⟩).symm
  have hAE : IsElementaryTwo (A.subgroupOf E) := by
    let := hA.2
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ E from le_sup_right)⟩
    intro he
    exact hA.1 (by rw [← map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right),
      he,Subgroup.map_bot])
  have hb : fixedCodim (ρ.comp E.subtype) (A.subgroupOf E) ≤ 2 * rank (A.subgroupOf E) := by
    rw [fixedCodim_subgroupOf ρ (show A ≤ E from le_sup_right),
      rank_subgroupOf (show A ≤ E from le_sup_right)]
    exact hbound
  have hKX : K ≤ centralizer (X : Set D) := by
    intro k hk x hx'
    rw [← hmark] at hx'
    obtain ⟨g,_,rfl⟩ := hx'
    exact (hs ⟨k,hk⟩ g).symm.eq
  refine ⟨hsE,?_,?_,?_⟩
  · exact multiplicity_injective (ρ.comp s) (ρ.comp E.subtype) _ hfree
      (hf.comp E.subtype_injective)
  · exact offender_multiplicity (ρ.comp s) (ρ.comp E.subtype) _ hfree _ hAE hb
  · exact LinearTwo.NoStrongMoved.generated_fitting K X hx hcommon hKX hA hAX

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideModule
