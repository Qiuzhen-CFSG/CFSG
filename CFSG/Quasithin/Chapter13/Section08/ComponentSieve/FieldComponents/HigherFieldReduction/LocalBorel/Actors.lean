module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction

/-!
# Applying the higher-field torus calculation to the prescribed actor

Conjugation by T* on K* uses its literal kernel C_T*(K*). The source
Sylow T*∩K* is stabilized by every such actor, and its inner image lies
in the actor range. Thus the model theorem applies to the original t*.
An outer actor fixing the residual torus with commutator quotient of
order at most three yields the actual exceptional model isomorphisms.
For the generic parameters, the lifted fixer includes the full kernel.

The final conditional dichotomy records the remaining local fixation,
commutator bound and inner-actor argument explicitly. It does not prove
those premises or the literal source fixer equality.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971.
-/

@[expose] public section

open Subgroup Theory.GroupAction.ModelConjugation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
open TorusModels.Assembly
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Actual conjugation by T* on K*. -/
def starActor (H K T : Subgroup G) [(Source.starImage H K).Normal] :
    Source.starImage H T →* MulAut (Source.starImage H K) :=
  action (Source.starImage H T) (Source.starImage H K) le_normalizer_of_normal
    (MulEquiv.refl _)

omit [Finite G] in
theorem starActor_apply (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (t : Source.starImage H T) (k : Source.starImage H K) :
    (starActor H K T t k : Source.Hstar H) = t * k * t⁻¹ := rfl

omit [Finite G] in
theorem starActor_twoGroup (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) : IsPGroup 2 (starActor H K T).range := by
  obtain ⟨P, hP⟩ := hT
  have hp : IsPGroup 2 (Source.starImage H T) := by
    rw [Source.starImage, ← hP, ← comap_subtype,
      comap_map_eq_self_of_injective H.subtype_injective]
    exact P.isPGroup'.map _
  exact hp.of_surjective _ (starActor H K T).rangeRestrict_surjective

theorem starActor_stable (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) (t : Source.starImage H T) :
    (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      (starActor H K T t).toMonoidHom = sourceSylow H K T hT := by
  rw [sourceSylow_eq]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨k, hk, rfl⟩
    change (starActor H K T t k : Source.Hstar H) ∈ Source.starImage H T
    rw [starActor_apply]
    exact (Source.starImage H T).mul_mem ((Source.starImage H T).mul_mem t.property hk)
      ((Source.starImage H T).inv_mem t.property)
  · rw [card_map_of_injective (starActor H K T t).injective]

theorem starActor_innerSylow (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H) :
    (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map MulAut.conj ≤
      (starActor H K T).range := by
  apply inner_le_action_range
  change (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
    (Source.starImage H K).subtype ≤ Source.starImage H T
  rw [sourceSylow_image]
  exact inf_le_left

omit [Finite G] in
/-- Retain the complete kernel of the source conjugation action. -/
theorem starActor_kernel (H K T : Subgroup G) [(Source.starImage H K).Normal] :
    (starActor H K T).ker.map (Source.starImage H T).subtype =
      Source.starImage H T ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) :=
  action_ker_map _ _ _ _

/-- The prescribed t, without replacing it by a power or another inverter. -/
def markedActor (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (t : H) (ht : t.val ∈ T) : MulAut (Source.starImage H K) :=
  starActor H K T ⟨QuotientGroup.mk' (pCore 2 H) t, ⟨t, ht, rfl⟩⟩

omit [Finite G] in
theorem markedActor_outer_iff (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (t : H) (ht : t.val ∈ T) :
    markedActor H K T t ht ∉ MulAut.innerSubgroup (Source.starImage H K) ↔
      OuterStarAction H K (QuotientGroup.mk' (pCore 2 H) t) := by
  constructor
  · intro h
    exact ⟨by rw [normalizer_eq_top]; trivial, h⟩
  · rintro ⟨ht', h⟩
    exact h

/-- The local fixation and commutator estimate feed the actual model theorem. -/
theorem exceptionalOuter_of_local_calculation {n : ℕ} {unitary four : Bool}
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H)
    (model : Model.{u,v} (Source.starImage H K) n unitary four) (hn : 1 < n)
    (t : H) (ht : t.val ∈ T)
    (hout : markedActor H K T t ht ∉ MulAut.innerSubgroup (Source.starImage H K))
    (hfix : FixesTorus (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht))
    (hsmall : commutatorOrder (residualAt (sourceSylow H K T hT))
      (markedActor H K T t ht) ≤ 3) :
    ExceptionalOuterAlternative.{u,v} H K (QuotientGroup.mk' (pCore 2 H) t) := by
  have hstable : ∀ a ∈ (starActor H K T).range,
      (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map a.toMonoidHom =
        sourceSylow H K T hT := by
    rintro _ ⟨a, rfl⟩
    exact starActor_stable H K T hT a
  have hm := model.small_outer_fixer_models hn (sourceSylow H K T hT)
    (starActor H K T).range (starActor_twoGroup H K T hT)
    (starActor_innerSylow H K T hT) hstable (markedActor H K T t ht)
    ⟨⟨QuotientGroup.mk' (pCore 2 H) t, ⟨t, ht, rfl⟩⟩, rfl⟩ hout hfix hsmall
  exact ⟨exceptionalCarrier_of_torus_models hm, (markedActor_outer_iff H K T t ht).mp hout⟩

/-- In the generic torus case, a fixer lifts to the inner Sylow times the
actual centralizer kernel. No containment of that kernel is assumed. -/
theorem marked_fixer_alternative {n : ℕ} {unitary four : Bool}
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H)
    (model : Model.{u,v} (Source.starImage H K) n unitary four) (hn : 1 < n)
    (t : H) (ht : t.val ∈ T)
    (hfix : FixesTorus (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht)) :
    (QuotientGroup.mk' (pCore 2 H) t ∈
      (Source.starImage H T ⊓ Source.starImage H K) ⊔
        (Source.starImage H T ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)))) ∨
      (unitary = false ∧ (n = 2 ∨ n = 6)) ∨ (unitary = true ∧ n = 3) := by
  have hp : IsPGroup 2 (Source.starImage H T) := by
    obtain ⟨P, hP⟩ := hT
    rw [Source.starImage, ← hP, ← comap_subtype,
      comap_map_eq_self_of_injective H.subtype_injective]
    exact P.isPGroup'.map _
  have hs : (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      ((Source.starImage H K).subtype.comp (MulEquiv.refl _).symm.toMonoidHom) ≤
        Source.starImage H T := by
    change (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
      (Source.starImage H K).subtype ≤ _
    rw [sourceSylow_image]
    exact inf_le_left
  have hh := model.conjugation_alternative hn (Source.starImage H T)
    (Source.starImage H K) hp le_normalizer_of_normal (MulEquiv.refl _)
    (sourceSylow H K T hT) hs (starActor_stable H K T hT)
  rcases hh with h | hex
  · have hmem := (h ⟨QuotientGroup.mk' (pCore 2 H) t, ⟨t, ht, rfl⟩⟩).mp hfix
    change QuotientGroup.mk' (pCore 2 H) t ∈
      (sourceSylow H K T hT : Subgroup (Source.starImage H K)).map
        (Source.starImage H K).subtype ⊔ _ at hmem
    rw [sourceSylow_image] at hmem
    exact Or.inl hmem
  · exact Or.inr hex

/-- Conditional final step: the inner-actor argument remains a separate source
obligation. The outer case is derived using the actual model, Sylow and t. -/
theorem borelAlternative_of_local_calculation {n : ℕ} {unitary four : Bool}
    (H K T X : Subgroup G) [(Source.starImage H K).Normal]
    (hT : Chapter1.IsSylowIn 2 T H)
    (model : Model.{u,v} (Source.starImage H K) n unitary four) (hn : 1 < n)
    (t : H) (ht : t.val ∈ T)
    (hfix : FixesTorus (residualAt (sourceSylow H K T hT)) (markedActor H K T t ht))
    (hsmall : commutatorOrder (residualAt (sourceSylow H K T hT))
      (markedActor H K T t ht) ≤ 3)
    (hinner : markedActor H K T t ht ∈ MulAut.innerSubgroup (Source.starImage H K) →
      ExternalXAlternative H K X) :
    BorelAlternative.{u,v} H K X (QuotientGroup.mk' (pCore 2 H) t) := by
  by_cases htinner : markedActor H K T t ht ∈ MulAut.innerSubgroup (Source.starImage H K)
  · exact Or.inl (hinner htinner)
  · exact Or.inr (exceptionalOuter_of_local_calculation H K T hT model hn t ht
      htinner hfix hsmall)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel

end
