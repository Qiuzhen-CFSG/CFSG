module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Geometry
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.AlternatingFixedSpace
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.LinearThreeFixedSpace
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SeedCriterion
public import Theory.Representation.SpecialLinearNatural.CubicFixedSpace

/-!
# Native moved-section exclusions for the mixed FF quotient

The concrete cubic fixed-space calculations are applied to the classifier's
literal quotient `[V,L]/C_[V,L](L)`. Its canonical projection has central
kernel, and `V/[V,L]` is trivial under L. Cubic lifting and odd Sylow-coset
averaging therefore handle both extensions without requiring a splitting.
The doubled-natural clause instead uses the original moved submodule.

`SectionModel` contains actual compatible group and module equivalences,
including arbitrary binary fields and identically marked natural copies.
The four-dimensional A₇ clause retains faithfulness and does not identify
inequivalent actions by dimension. `restrictMarked` uses the classifier's
commuting subgroup square when restricting its full action.

The final two theorems apply these calculations to the literal offender
subgroup of `H/O₂(H)`. Its seed centralizer excludes each of these module
models. Exhaustiveness and the remaining triple-six and binary G₂ cases
are separate obligations; no quotient identification is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.2/B.4.8/B.5.1, printed pp.86,91,99; 15.4.18, printed p.1163.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Representation.BinarySylowFixedSpace
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
namespace NativeSections
open ClassificationComparison.FFAlternatives
universe u v w z

/-- Actual action models whose Sylow fixed spaces admit cubic fixers. -/
inductive SectionModel {D : Type u} [Group D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) : Prop
  | linearThree (F : BinaryField) (equiv : ActionEquiv ρ (linearNatural F 3))
  | repeatedThree (F : BinaryField) (r : ℕ)
      (equiv : ActionEquiv ρ (repeated (linearNatural F 3) r))
  | alternating (n : ℕ) (degree : n = 6 ∨ n = 7)
      (equiv : ActionEquiv ρ (alternatingNatural n))
  | symplecticDerived (equiv : ActionEquiv ρ (symplecticDerivedNatural (k := ZMod 2) 2))
  | alternatingFour (equiv : D ≃* alternatingGroup (Fin 7))
      (faithful : Function.Injective ρ) (dimension : Module.finrank (ZMod 2) V = 4)

variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem transport_fixer {E : Type w} [Group E]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} (e : ActionEquiv ρ σ)
    (h : ∀ T : Sylow 2 E, ∃ d : E, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace σ (T : Subgroup E), σ d w = w) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  exact sylow_fixedSpace_enlargement_equivariant ρ σ (S : Subgroup D)
    e.groupEquiv e.linearEquiv e.intertwines (h (S.mapSurjective e.groupEquiv.surjective))

/-- The witnesses use the concrete actions, retaining arbitrary field degree,
repeated copies with the same marking, and both four-dimensional A₇ actions. -/
theorem SectionModel.enlargement [FiniteDimensional (ZMod 2) V]
    (h : SectionModel ρ) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  cases h with
  | linearThree F e =>
    apply transport_fixer e _ S
    intro T
    exact sylow_fixedSpace_enlargement_of_cubic _ _ SL3BinaryCubic.klein_two
      _ SL3BinaryCubic.cycle_pow SL3BinaryCubic.cycle_ne_one
      SL3BinaryCubic.cycle_fixes_natural T
  | repeatedThree F r e =>
    apply transport_fixer e _ S
    intro T
    apply sylow_fixedSpace_enlargement_of_cubic _ _ SL3BinaryCubic.klein_two
      _ SL3BinaryCubic.cycle_pow SL3BinaryCubic.cycle_ne_one _ T
    intro v hv
    funext i
    exact SL3BinaryCubic.cycle_fixes_natural (v i) (fun a => congrFun (hv a) i)
  | alternating n hn e =>
    exact transport_fixer e (AlternatingFixedSpace.alternating_natural_enlargement n hn) S
  | symplecticDerived e =>
    exact transport_fixer e SymplecticCubicFixedSpace.symplecticDerived_enlargement S
  | alternatingFour e hf hd =>
    let σ := ρ.comp e.symm.toMonoidHom
    let a : ActionEquiv ρ σ := ⟨e, LinearEquiv.refl _ _, by
      intro g v
      change ρ g v = ρ (e.symm (e g)) v
      rw [e.symm_apply_apply]⟩
    exact transport_fixer a (AlternatingFixedSpace.four_dimensional_enlargement σ
      (hf.comp e.symm.injective) hd) S

/-- Restrict a marked full action using its literal subgroup compatibility. -/
def restrictMarked {E : Type w} [Group E]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} {H L : Subgroup D} {M : Subgroup E}
    (e : MarkedActionEquiv ρ H L σ M) :
    ActionEquiv (ρ.comp L.subtype) (σ.comp M.subtype) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines := by
    intro g v
    have h := e.action.intertwines (⟨g, e.contained g.property⟩ : H) v
    rw [e.compatible] at h
    exact h

variable {L : Subgroup D}

/-- Lift through the actual quotient [V,L]/C_[V,L](L), then through V/[V,L].
The two extensions need not split, and L need not be the whole actor. -/
theorem movedSection_enlargement (s : MovedSection ρ L) (T : Sylow 2 L)
    (h : ∃ d : L, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace (s.action.comp L.subtype) (T : Subgroup L),
        (s.action.comp L.subtype) d w = w)
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let U : Subrepresentation (ρ.comp L.subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  have hker : ∀ (g : L) (u : U.toSubmodule), s.central.toSubmodule.mkQ u = 0 →
      U.toRepresentation g u = u := by
    intro g u hu
    have hu' := (Submodule.Quotient.mk_eq_zero _).mp hu
    rw [s.central_eq] at hu'
    exact hu' g
  have hquot : ∀ (g : L) (v : V), ρ g v - v ∈ U := by
    intro g v
    change ρ g v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩
  obtain ⟨d, hd, h3, hf⟩ := sylow_fixedSpace_enlargement_of_central_section
    (ρ.comp L.subtype) (s.action.comp L.subtype) U s.central.toSubmodule.mkQ
    (fun _ _ => rfl) hker hquot T h
  exact sylow_fixedSpace_enlargement_of_embedded_cubic ρ L.subtype Subtype.val_injective
    (T : Subgroup L) T.isPGroup' d h3 (fun he => hd (he ▸ T.one_mem)) hf S

/-- The doubled-natural clause is on [V,L] itself rather than its central
quotient. The same trivial-quotient argument retains that convention. -/
theorem movedSpace_enlargement (s : MovedSection ρ L) (T : Sylow 2 L)
    (h : ∃ d : L, d ∉ T ∧ d ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace (s.space.toRepresentation.comp L.subtype) (T : Subgroup L),
        (s.space.toRepresentation.comp L.subtype) d w = w)
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let U : Subrepresentation (ρ.comp L.subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  let i : U.toRepresentation.IntertwiningMap (ρ.comp L.subtype) :=
    { toLinearMap := U.toSubmodule.subtype
      isIntertwining' _ := by ext; rfl }
  obtain ⟨d, hd, h3, hf⟩ := h
  have hquot : ∀ (g : L) (v : V), (ρ.comp L.subtype) g v - v ∈ i.toLinearMap.range := by
    intro g v
    refine ⟨⟨_, ?_⟩, rfl⟩
    change ρ g v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩
  have hf' := fixes_of_trivial_quotient (ρ.comp L.subtype) U.toRepresentation i
    Subtype.val_injective hquot T hf
  exact sylow_fixedSpace_enlargement_of_embedded_cubic ρ L.subtype Subtype.val_injective
    (T : Subgroup L) T.isPGroup' d h3 (fun he => hd (he ▸ T.one_mem)) hf' S

/-- A model of the actual central section yields the outside-Sylow fixer. -/
theorem movedSection_model_enlargement [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (h : SectionModel (s.action.comp L.subtype)) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let T : Sylow 2 L := Classical.choice inferInstance
  exact movedSection_enlargement s T (h.enlargement T) S

/-- A model on the moved submodule yields the same witness without passing
to a different section. -/
theorem movedSpace_model_enlargement [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (h : SectionModel (s.space.toRepresentation.comp L.subtype))
    (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  let T : Sylow 2 L := Classical.choice inferInstance
  exact movedSpace_enlargement s T (h.enlargement T) S

end NativeSections

open NativeSections ClassificationComparison.FFAlternatives
variable {H : Type*} [Group H] [Finite H]
  (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
  (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- Concrete section exclusions in the literal offender action of 15.4.18.
The only seed premise is its actual centralizer, not a model fixed-space claim. -/
theorem offenderAction_not_sectionModel (L : Subgroup (offenderGroup P Z hC))
    (s : MovedSection (offenderAction P Z hC) L) :
    ¬ SectionModel (s.action.comp L.subtype) := by
  intro h
  obtain ⟨S, hS⟩ := exists_offenderSylow P Z hC
  obtain ⟨d, hd, _, hf⟩ := movedSection_model_enlargement s h S
  exact offenderAction_no_fixedSpace_enlargement P Z hC (S : Subgroup _) hS d hd hf

/-- The same literal consumer for B.5.1's doubled-natural moved submodule. -/
theorem offenderAction_not_movedSpaceModel (L : Subgroup (offenderGroup P Z hC))
    (s : MovedSection (offenderAction P Z hC) L) :
    ¬ SectionModel (s.space.toRepresentation.comp L.subtype) := by
  intro h
  obtain ⟨S, hS⟩ := exists_offenderSylow P Z hC
  obtain ⟨d, hd, _, hf⟩ := movedSpace_model_enlargement s h S
  exact offenderAction_no_fixedSpace_enlargement P Z hC (S : Subgroup _) hS d hd hf

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
