module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.MovedGeometry
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Models

/-!
# Commutant transport on the original marked moved space

The local LA moved space is identified with the original [V,L], using the
literal inclusion of L. A marked intertwiner transports a concrete trivial
linear commutant to that space. Since L is normal, every ambient element
centralizing L then fixes [V,L]. In particular the actual three-core fixes it,
and the odd-core moved decomposition applies with the original subgroups.

`ModelCommutants` is an intermediate concrete-model proof obligation, not a
source theorem or an allowed earlier classification assumption. It contains
only the three linear commutant calculations. Its producer must construct it
before the B.5.7 assembly can use `model_moved_decomposition`. Neither target
centralizer equality nor any dimension or global fixed-space splitting occurs
in the record.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.7,
printed p.106, from the endomorphism calculation to [V,LX] = U ⊕ [V,X].
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v w z
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)
variable [Finite G] {K : GroupClass.{u}}

variable {E : Type w} [Group E] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]

/-- Triviality of the linear automorphism commutant of a specified subgroup action. -/
def TrivialCommutant (σ : Representation (ZMod 2) E W) (M : Subgroup E) : Prop :=
  ∀ f : W ≃ₗ[ZMod 2] W,
    (∀ (g : M) (v : W), f (σ g v) = σ g (f v)) → f = LinearEquiv.refl (ZMod 2) W

/-- Concrete model calculations to be proved independently of the ambient FF group. -/
structure ModelCommutants : Prop where
  natural : ∀ n : ℕ, n = 6 ∨ n = 7 →
    TrivialCommutant (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n))
  coreSix : TrivialCommutant (BinaryPermutation.coreRepresentation (Fin 6))
    (alternatingGroup (Fin 6))

omit [Finite G] in
/-- A marked intertwiner transports the full component commutant. -/
theorem marked_trivialCommutant {L : Subgroup G}
    {σ : Representation (ZMod 2) E W} {M : Subgroup E}
    (e : MarkedActionEquiv ρ ⊤ L σ M) (hmodel : TrivialCommutant σ M) :
    TrivialCommutant ρ L := by
  intro t ht
  let b := e.action.linearEquiv
  have hact (l : L) (v : V) : b (ρ l v) = σ (e.subgroupEquiv l) (b v) := by
    have hh := e.action.intertwines ⟨l, e.contained l.property⟩ v
    rw [e.compatible] at hh
    exact hh
  let f : W ≃ₗ[ZMod 2] W := b.symm.trans (t.trans b)
  have hf : f = LinearEquiv.refl (ZMod 2) W := by
    apply hmodel
    intro g w
    obtain ⟨l, rfl⟩ := e.subgroupEquiv.surjective g
    obtain ⟨v, rfl⟩ := b.surjective w
    have hb : b.symm (σ (e.subgroupEquiv l) (b v)) = ρ l v := by
      rw [← hact, b.symm_apply_apply]
    change b (t (b.symm (σ (e.subgroupEquiv l) (b v)))) =
      σ (e.subgroupEquiv l) (b (t (b.symm (b v))))
    rw [hb, b.symm_apply_apply, ht l v, hact]
  apply LinearEquiv.ext
  intro v
  apply b.injective
  have hh := congrArg (fun f : W ≃ₗ[ZMod 2] W => f (b v)) hf
  simpa only [f, LinearEquiv.trans_apply, b.symm_apply_apply, LinearEquiv.refl_apply] using hh

omit [Finite G] in
/-- The local moved-space marking is literally the original [V,L]. -/
theorem model_space_eq {L A : Subgroup G} (m : SymmetricMovedModel ρ L A) :
    m.sectionData.space.toSubmodule = moved ρ L := by
  rw [m.sectionData.space_eq]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨l, hl, v, hv, rfl⟩
    exact ⟨l, hl, v, hv, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨l, hl, v, hv, rfl⟩
    exact ⟨⟨l, (le_sup_left : L ≤ L ⊔ A) hl⟩, hl, v, hv, rfl⟩

omit [Finite G] in
/-- The chosen natural action identifies the original component, with its actual marking. -/
theorem model_component_equiv {L A : Subgroup G} (m : SymmetricMovedModel ρ L A) :
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (L ≃* alternatingGroup (Fin 7)) := by
  cases m.action with
  | natural n hn e =>
    have he := (subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv
    rcases hn with rfl | rfl
    · exact Or.inl ⟨he⟩
    · exact Or.inr ⟨he⟩
  | coreSix e =>
    exact Or.inl ⟨(subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv⟩

omit [Finite G] in
/-- Concrete commutants control every ambient element centralizing L on [V,L]. -/
theorem centralizer_fixes_model (models : ModelCommutants) {L A : Subgroup G}
    [L.Normal] (m : SymmetricMovedModel ρ L A) :
    moved ρ L ≤ fixedSpace ρ (centralizer (L : Set G)) := by
  have heq := model_space_eq ρ m
  have htriv : TrivialCommutant m.sectionData.space.toRepresentation
      (L.subgroupOf (L ⊔ A)) := by
    cases m.action with
    | natural n hn e => exact marked_trivialCommutant _ e (models.natural n hn)
    | coreSix e => exact marked_trivialCommutant _ e models.coreSix
  intro v hv c
  let U := m.sectionData.space.toSubmodule
  have stable (g : G) (w : U) : ρ g w ∈ U := by
    change ρ g w ∈ m.sectionData.space.toSubmodule
    rw [heq]
    exact (normalMoved ρ L).apply_mem_toSubmodule g (show (w : V) ∈ moved ρ L by
      rw [← heq]
      exact w.property)
  let t : U ≃ₗ[ZMod 2] U :=
    { toFun := fun w => ⟨ρ c w, stable c w⟩
      invFun := fun w => ⟨ρ (c : G)⁻¹ w, stable (c : G)⁻¹ w⟩
      left_inv := fun w => Subtype.ext (by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply])
      right_inv := fun w => Subtype.ext (by
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply])
      map_add' := fun a b => Subtype.ext ((ρ c).map_add a b)
      map_smul' := fun a b => Subtype.ext ((ρ c).map_smul a b) }
  have ht : t = LinearEquiv.refl (ZMod 2) U := by
    apply htriv
    intro l w
    apply Subtype.ext
    change ρ c (ρ (l.val.val) w) = ρ (l.val.val) (ρ c w)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    exact congrArg (fun g => ρ g w) (c.property l.val.val l.property).symm
  have hvU : v ∈ U := by
    change v ∈ m.sectionData.space.toSubmodule
    rwa [heq]
  have hh := congrArg (fun t : U ≃ₗ[ZMod 2] U => (t ⟨v, hvU⟩ : V)) ht
  exact hh

/-- The source commuting-action step on the actual cubic core and original moved space. -/
theorem threeCore_fixes_model (models : ModelCommutants) {L A : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    (m : SymmetricMovedModel ρ L A) :
    moved ρ L ≤ fixedSpace ρ (pCore 3 G) := by
  let : L.Normal := d.normal
  have hXL : pCore 3 G ≤ centralizer (L : Set G) :=
    le_centralizer_iff.mp (component_centralizes_threeCore hL)
  intro v hv x
  exact centralizer_fixes_model ρ models m hv ⟨x, hXL x.property⟩

/-- Actual application of the commutant calculation to the source moved decomposition. -/
theorem model_moved_decomposition (models : ModelCommutants) {L A : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    (m : SymmetricMovedModel ρ L A) :
    moved ρ (L ⊔ pCore 3 G) = moved ρ L ⊔ moved ρ (pCore 3 G) ∧
      Disjoint (moved ρ L) (moved ρ (pCore 3 G)) ∧
      moved ρ (pCore 3 G) ≤ fixedSpace ρ L :=
  threeCore_moved_decomposition ρ hL d (threeCore_fixes_model ρ models hL d m)

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
