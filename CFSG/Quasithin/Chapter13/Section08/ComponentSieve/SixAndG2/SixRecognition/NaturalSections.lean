module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked.Offenders
public import Theory.Representation.BinaryOffender.FixedQuotientEquality
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.CodimensionSieve

/-!
# Detecting the six-letter action on a genuine subquotient

The faithful section used in 13.8.26 need not be the whole submodule W.
It suffices to have a natural quotient of an invariant subspace, with an
injective map of the original actors. A common commutator line descends to
this quotient and forces the actor to have rank one. If an actor fixes a
hyperplane of the whole module, the fixed-codimension inequalities are sharp,
so fixed vectors lift through the section. Natural transvection rigidity
then computes the pointwise centralizer in the original acting group.

This accommodates central factors and covers without identifying W with a
four-dimensional module. The separate upper-quotient calculation retains the
outer-related action and the same actor map throughout.

Source: Aschbacher–Smith 13.8.26, printed p.962, using B.3.4 and 13.8.23.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
open NaturalSix

variable {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]

/-- An actual natural subquotient. Its actor marking is part of the data;
neither a dimension nor an abstract A₆ group label replaces equivariance. -/
structure NaturalSection (σ : Representation (ZMod 2) J E) where
  actor : J →* Symmetric
  injective : Function.Injective actor
  space : Subrepresentation σ
  projection : space.toSubmodule →ₗ[ZMod 2] Natural
  surjective : Function.Surjective projection
  intertwines : ∀ a v, projection (space.toRepresentation a v) =
    symmetricAction (actor a) (projection v)

namespace NaturalSection
variable {σ : Representation (ZMod 2) J E} (m : NaturalSection σ)
include m

/-- A faithful natural subquotient detects equality of the original actors. -/
theorem faithful : Function.Injective σ := by
  intro a b hab
  apply m.injective
  apply symmetricAction_injective
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := m.surjective v
  rw [← m.intertwines, ← m.intertwines]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun hab w

private theorem commutator_image (A : Subgroup J) :
    (subspaceCommutator m.space.toRepresentation ⊤ A).map m.projection =
      subspaceCommutator symmetricAction ⊤ (A.map m.actor) := by
  -- Use the surjection in its forward direction, with the actor already pulled back.
  have he := subspaceCommutator_map_embedding
    (symmetricAction.comp m.actor) m.space.toRepresentation (MonoidHom.id J)
    m.projection (fun a v => (m.intertwines a v).symm) A ⊤
  rw [Submodule.map_top, LinearMap.range_eq_top.mpr m.surjective, Subgroup.map_id] at he
  have hi := subspaceCommutator_map_embedding
    (symmetricAction.comp m.actor) symmetricAction m.actor
    (LinearMap.id : Natural →ₗ[ZMod 2] Natural) (fun _ _ => rfl) A ⊤
  simp only [Submodule.map_id] at hi
  exact he.symm.trans hi

variable [FiniteDimensional (ZMod 2) E]

/-- Fixed codimension cannot increase on the displayed natural subquotient. -/
theorem fixedCodim_le (A : Subgroup J) :
    fixedCodim symmetricAction (A.map m.actor) ≤ fixedCodim σ A := by
  have h := fixedCodim_le_of_equivariant_surjection m.space.toRepresentation
    (symmetricAction.comp m.actor) m.projection m.surjective m.intertwines A
  have ht := h.trans (fixedCodim_subrepresentation_le σ m.space A)
  change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (symmetricAction.comp m.actor) A) ≤ _ at ht
  rw [fixedSpace_comp_map] at ht
  exact ht

/-- Common commutator lines are tested on a natural subquotient, without
assuming a model of the whole module. -/
theorem rank_one {A : Subgroup J} (hA : IsElementaryTwo A)
    (hc : Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) ≤ 1) : rank A = 1 := by
  let : IsElementaryAbelian 2 A := hA.2
  have hAm : IsElementaryTwo (A.map m.actor) :=
    ⟨fun hb => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A m.injective).mp hb),
      IsElementaryAbelian.map m.actor⟩
  have hs := subspaceCommutator_map_embedding σ m.space.toRepresentation
    (MonoidHom.id J) m.space.toSubmodule.subtype (fun _ _ => rfl) A ⊤
  simp only [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] at hs
  have hd : Module.finrank (ZMod 2) (subspaceCommutator m.space.toRepresentation ⊤ A) ≤ 1 := by
    rw [(Submodule.equivMapOfInjective m.space.toSubmodule.subtype
      (Submodule.subtype_injective _) (subspaceCommutator m.space.toRepresentation ⊤ A)).finrank_eq,
      ← hs]
    apply (Submodule.finrank_mono (show subspaceCommutator σ m.space.toSubmodule A ≤
      subspaceCommutator σ ⊤ A from ?_)).trans hc
    apply Submodule.span_mono
    rintro v ⟨a, ha, w, _, rfl⟩
    exact ⟨a, ha, w, Submodule.mem_top, rfl⟩
  have hm : Module.finrank (ZMod 2)
      (subspaceCommutator symmetricAction ⊤ (A.map m.actor)) ≤ 1 := by
    rw [← m.commutator_image]
    exact (Submodule.finrank_map_le _ _).trans hd
  rw [← rank_map_injective m.actor m.injective A]
  exact rank_one_of_natural_commutator_le_one hAm hm

/-- The fixed hyperplane lifts through the literal section, giving the
pointwise centralizer in J, including for modules with central factors. -/
theorem fixed_kernel {A : Subgroup J} (hA : IsElementaryTwo A)
    (hc : fixedCodim σ A = 1) : subspaceKernel σ (fixedSpace σ A) ⊤ = A := by
  let τ := symmetricAction.comp m.actor
  have hf : Function.Injective τ := symmetricAction_injective.comp m.injective
  have hp := fixedCodim_pos_of_faithful τ hf hA.1
  have hq := fixedCodim_le_of_equivariant_surjection m.space.toRepresentation τ
    m.projection m.surjective m.intertwines A
  have hs := fixedCodim_subrepresentation_le σ m.space A
  have ht : fixedCodim τ A = 1 := by omega
  have hn : fixedCodim m.space.toRepresentation A = fixedCodim τ A := by omega
  have hfix := fixedSpace_eq_comap_of_fixedCodim_eq m.space.toRepresentation τ
    m.projection m.surjective m.intertwines A hn
  have hk : subspaceKernel τ (fixedSpace τ A) ⊤ = A :=
    natural_kernel_equivariant τ m.actor m.injective (LinearEquiv.refl _ _)
      (fun _ _ => rfl) hA ht
  apply le_antisymm
  · intro a ha
    rw [← hk]
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro v hv
    obtain ⟨w, rfl⟩ := m.surjective v
    have hw : w ∈ fixedSpace m.space.toRepresentation A := by
      rw [hfix]
      exact hv
    have hw' : (w : E) ∈ fixedSpace σ A := fun b => congrArg Subtype.val (hw b)
    change symmetricAction (m.actor a) (m.projection w) = m.projection w
    rw [← m.intertwines]
    apply congrArg m.projection
    apply Subtype.ext
    exact ha.2 w hw'
  · intro a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hv ⟨a, ha⟩⟩

end NaturalSection

variable {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]

/-- The upper quotient keeps its opposite action under the *same* actor map.
The transvection cube can be a subgroup of the image of the quadratic actor;
equality with that actor is unnecessary. -/
theorem opposite_quotient_excludes_cube
    (τ : Representation (ZMod 2) J F) (R : Subgroup J)
    (hR : IsQuadratic τ R)
    (f : J →* Symmetric) (q : F →ₗ[ZMod 2] Natural)
    (hq : Function.Surjective q)
    (he : ∀ a v, q (τ a v) = Marked.oppositeAction (f a) (q v))
    (hD : Theory.SpecificGroups.SymmetricSix.BinaryFlags.D ≤ R.map f) : False := by
  apply Marked.D_not_quadratic
  intro a ha b hb v
  obtain ⟨a', ha', rfl⟩ := hD ha
  obtain ⟨b', hb', rfl⟩ := hD hb
  obtain ⟨w, rfl⟩ := hq v
  have h := congrArg q (hR a' ha' b' hb' w)
  simpa only [he, map_sub] using h

/-- A strong offender on any module with the displayed natural subquotient
would put the transvection cube in the quadratic upper actor. -/
theorem no_strong_of_opposite_quotient [FiniteDimensional (ZMod 2) E]
    (σ : Representation (ZMod 2) J E) (m : NaturalSection σ)
    (τ : Representation (ZMod 2) J F) (R : Subgroup J)
    (hR : IsQuadratic τ R)
    (hT : R.map m.actor ≤ CFSG.Quasithin.ChapterB.Offenders.Six.sylowCarrier)
    (q : F →ₗ[ZMod 2] Natural) (hq : Function.Surjective q)
    (he : ∀ a v, q (τ a v) = Marked.oppositeAction (m.actor a) (q v)) :
    ¬ ∃ A ≤ R, IsStrongOffender σ A := by
  rintro ⟨A, hAR, hA⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  have hm : IsStrongOffender symmetricAction (A.map m.actor) := by
    refine ⟨⟨fun hb => hA.1.1
      ((Subgroup.map_eq_bot_iff_of_injective A m.injective).mp hb),
      IsElementaryAbelian.map m.actor⟩, ?_⟩
    rw [rank_map_injective m.actor m.injective]
    exact (m.fixedCodim_le A).trans_lt hA.2
  have hd := Marked.strong_in_sylow_eq_D hm ((Subgroup.map_mono hAR).trans hT)
  exact opposite_quotient_excludes_cube τ R hR m.actor q hq he
    (hd ▸ Subgroup.map_mono hAR)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
end
