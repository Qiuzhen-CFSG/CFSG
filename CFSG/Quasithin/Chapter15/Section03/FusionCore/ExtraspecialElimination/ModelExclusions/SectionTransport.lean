module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.Replacement

/-!
# Transport to the actual component modules in 15.3.49

The last page of the extraspecial argument uses an offender on `U_H/Z`,
its conjugate inside `O₂(Y₀* T*)`, and identified component sections.
Conjugacy preserves the fixed codimension. Passing to an invariant section
can only decrease it, and an injective change of actors preserves rank.
These facts transport a strong offender to a specified model representation.
Restriction to a subrepresentation also preserves best offending, by the
fixed-space comparison, which is needed for B.4.9(2iii).

The component-module identification and the model's numerical bounds are
explicit inputs. In particular this module does not assert B.4.2 or B.5.1,
and an arbitrary representation is never identified with ambient conjugation.
The last two lemmas use the published literal `SectionAction` and `starImage`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.5,
printed pp.69–70, and the end of 15.3.49, printed p.1145.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

section Transport

variable {K D V W : Type*} [Group K] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)

/-- Strong offending survives an injective identification of actors and an
equivariant linear identification of modules. -/
theorem strong_map_equivariant (f : K →* D) (hf : Function.Injective f)
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (ρ g v) = σ (f g) (E v))
    {A : Subgroup K} (hA : IsStrongOffender ρ A) :
    IsStrongOffender σ (A.map f) := by
  refine ⟨(IsOffender.map_equivariant ρ σ f hf E hE ⟨hA.1, hA.2.le⟩).1, ?_⟩
  rw [← fixedCodim_map_equivariant ρ σ f E hE, rank_map_injective f hf]
  exact hA.2

/-- Best offending transports all subgroup comparisons, not just the
offender inequality. -/
theorem best_map_equivariant (e : K ≃* D) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (e g) (E v))
    {A : Subgroup K} (hA : IsBestOffender ρ A) :
    IsBestOffender σ (A.map e.toMonoidHom) := by
  have hweight (B : Subgroup K) : weight σ (B.map e.toMonoidHom) = weight ρ B := by
    unfold weight
    rw [rank_map_injective e.toMonoidHom e.injective]
    have he := Submodule.equivMapOfInjective E.toLinearMap E.injective (fixedSpace ρ B)
    have hd := he.finrank_eq
    rw [fixedSpace_map_equivariant ρ σ e.toMonoidHom E hE] at hd
    rw [hd]
  have helem : IsElementaryTwo (A.map e.toMonoidHom) := by
    let _ : IsElementaryAbelian 2 A := hA.1.2
    exact ⟨fun hb => hA.1.1
      ((map_eq_bot_iff_of_injective A e.injective).mp hb), IsElementaryAbelian.map _⟩
  refine ⟨helem, fun B hB => ?_⟩
  let C := B.comap e.toMonoidHom
  have hC : C ≤ A := by
    have h : C ≤ (A.map e.toMonoidHom).comap e.toMonoidHom := comap_mono hB
    rwa [comap_map_eq_self_of_injective e.injective] at h
  have hmap : C.map e.toMonoidHom = B := map_comap_eq_self_of_surjective e.surjective B
  rw [← hmap, hweight, hweight]
  exact hA.2 C hC

/-- Restricting the actor to an overgroup of the same subgroup preserves
strong offending. The subgroup is not replaced by its action image. -/
theorem strong_subgroupOf {A X : Subgroup K} (hA : IsStrongOffender ρ A)
    (hAX : A ≤ X) :
    IsStrongOffender (ρ.comp X.subtype) (A.subgroupOf X) := by
  have hmap : (A.subgroupOf X).map X.subtype = A := map_subgroupOf_eq_of_le hAX
  let _ : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.subgroupOf hAX⟩, ?_⟩
  · intro hb
    apply hA.1.1
    rw [← hmap, hb, Subgroup.map_bot]
  · have hr := rank_map_injective X.subtype X.subtype_injective (A.subgroupOf X)
    rw [hmap] at hr
    rw [fixedCodim, fixedSpace_comp_map, hmap, ← hr]
    exact hA.2

variable [FiniteDimensional (ZMod 2) V]

/-- The two conjugate source offenders have the same strict inequality. -/
theorem strong_conjugate {A : Subgroup K} (hA : IsStrongOffender ρ A) (g : K) :
    IsStrongOffender ρ (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map_conj g, ?_⟩
  rw [fixedCodim_map_conj, rank_map_conj]
  exact hA.2

/-- A strong offender remains strong on every invariant section on which
the same actor is retained. Faithfulness is a separate model hypothesis. -/
theorem strong_on_section {A : Subgroup K} (hA : IsStrongOffender ρ A)
    (N U : Subrepresentation ρ) :
    IsStrongOffender (sectionRepresentation ρ N U) A :=
  ⟨hA.1, (fixedCodim_section_le ρ N U A).trans_lt hA.2⟩

/-- Restriction to a subrepresentation preserves the comparisons with all
subgroups of a best offender, even when the restriction has a kernel. -/
theorem best_on_subrepresentation {A : Subgroup K} (hA : IsBestOffender ρ A)
    (U : Subrepresentation ρ) : IsBestOffender U.toRepresentation A := by
  refine ⟨hA.1, fun B hBA => ?_⟩
  have hb := hA.restriction_weight_le ρ hBA U.toSubmodule
  have hB := (subrepresentationFixedEquiv ρ U B).finrank_eq
  have hAA := (subrepresentationFixedEquiv ρ U A).finrank_eq
  simpa only [weight, hB, hAA] using hb

/-- A no-strong-offender bound on an identified component section excludes
the original strong offender. Both actor and module identifications occur
in the equivariance equation. -/
theorem exclude_strong_by_section
    (N U : Subrepresentation ρ) (X : Subgroup K)
    (e : X ≃* D)
    (E : (U.toSubmodule ⧸ (sectionLower ρ N U).toSubmodule) ≃ₗ[ZMod 2] W)
    (hE : ∀ (x : X) v,
      E (sectionRepresentation ρ N U x v) = σ (e x) (E v))
    (hbound : ∀ B : Subgroup D, IsElementaryTwo B → rank B ≤ fixedCodim σ B)
    {A : Subgroup K} (hAX : A ≤ X) (hA : IsStrongOffender ρ A) : False := by
  have hs := strong_on_section ρ hA N U
  have hr := strong_subgroupOf (sectionRepresentation ρ N U) hs hAX
  have hm := strong_map_equivariant
    ((sectionRepresentation ρ N U).comp X.subtype) σ e.toMonoidHom e.injective E hE hr
  exact Nat.not_lt_of_ge (hbound _ hm.1) hm.2

/-- The numerical output `q ≥ 1` of B.4.2 suffices on an identified
component section. Thompson replacement, already proved in the offender
library, relates this quadratic ratio to arbitrary strong offenders. -/
theorem exclude_strong_by_section_ratio [Finite D] [FiniteDimensional (ZMod 2) W]
    (N U : Subrepresentation ρ) (X : Subgroup K)
    (e : X ≃* D)
    (E : (U.toSubmodule ⧸ (sectionLower ρ N U).toSubmodule) ≃ₗ[ZMod 2] W)
    (hE : ∀ (x : X) v,
      E (sectionRepresentation ρ N U x v) = σ (e x) (E v))
    (hq : 1 ≤ quadraticRatio σ)
    {A : Subgroup K} (hAX : A ≤ X) (hA : IsStrongOffender ρ A) : False := by
  have hs := strong_on_section ρ hA N U
  have hr := strong_subgroupOf (sectionRepresentation ρ N U) hs hAX
  have hm := strong_map_equivariant
    ((sectionRepresentation ρ N U).comp X.subtype) σ e.toMonoidHom e.injective E hE hr
  exact not_lt_of_ge hq ((isStrongFFModule_iff_quadraticRatio_lt_one σ).mp ⟨_, hm⟩)

/-- Best offending on the actual upper section transports through both
the component inclusion and the equivariant model coordinates. This is
the precise transport needed before applying B.4.9(2iii). -/
theorem best_subrepresentation_model
    (U : Subrepresentation ρ) (X : Subgroup K) (e : X ≃* D)
    (E : U.toSubmodule ≃ₗ[ZMod 2] W)
    (hE : ∀ (x : X) v, E (U.toRepresentation x v) = σ (e x) (E v))
    {A : Subgroup K} (hAX : A ≤ X) (hA : IsBestOffender ρ A) :
    IsBestOffender σ ((A.subgroupOf X).map e.toMonoidHom) := by
  have hu := best_on_subrepresentation ρ hA U
  exact best_map_equivariant (U.toRepresentation.comp X.subtype) σ e E hE
    (hu.subgroupOf U.toRepresentation hAX)

end Transport

section ActualSection

variable {G : Type*} [Group G] [Finite G]
  {H U Z Vα Vγ : Subgroup G} [IsElementaryAbelian 2 U]

/-- The actual star conjugacy suffices; no identification of the two ambient
subgroups is made. -/
theorem strong_alpha (action : SectionAction H U Z)
    (hγ : IsStrongOffender action.representation (starImage H Vγ))
    (g : H ⧸ pCore 2 H)
    (hconj : starImage H Vα =
      (starImage H Vγ).map (MulAut.conj g).toMonoidHom) :
    IsStrongOffender action.representation (starImage H Vα) := by
  rw [hconj]
  exact strong_conjugate action.representation hγ g

/-- The point-stabilizer cases use the two-core of the subgroup of `H/O₂(H)`.
An arbitrary ambient two-core or a setwise stabilizer cannot replace it. -/
theorem exclude_at_star_twoCore (action : SectionAction H U Z)
    (Y₀ T : Subgroup G)
    (hα : starImage H Vα ≤ localTwoCore (starImage H Y₀ ⊔ starImage H T))
    (g : H ⧸ pCore 2 H)
    (hconj : starImage H Vα =
      (starImage H Vγ).map (MulAut.conj g).toMonoidHom)
    (hbound : ∀ B ≤ localTwoCore (starImage H Y₀ ⊔ starImage H T),
      IsElementaryTwo B → rank B ≤ fixedCodim action.representation B)
    (hγ : IsStrongOffender action.representation (starImage H Vγ)) : False := by
  have h := strong_alpha action hγ g hconj
  exact Nat.not_lt_of_ge (hbound _ hα h.1) h.2

end ActualSection

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions
