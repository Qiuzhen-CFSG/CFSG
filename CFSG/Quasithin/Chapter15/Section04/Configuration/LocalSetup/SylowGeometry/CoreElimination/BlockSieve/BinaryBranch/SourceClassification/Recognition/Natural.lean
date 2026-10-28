module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.QuasisimpleApplication
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.NativeSections
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Natural binary source sections have cubic Sylow fixed-space enlargements

In dimensions four and five, the radical of the first coordinate line fixes
exactly that line. A cubic transformation on coordinates two and three fixes
the line, hence every vector fixed by that radical. The same element works
on any number of identically marked natural copies.

The original moved-section projection has central kernel, while the quotient
above the moved space is trivial under the same actor. The established cubic
lifting argument therefore transfers the calculation through both extensions.
The final source applications contradict the actual seed Sylow centralizer.
Source: Aschbacher–Smith, B.5.1(1i,iv), p.99; 15.4.20, p.1164.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinarySylowFixedSpace
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
open TwoFactors.FFBranch TwoFactors.FFBranch.ClassificationComparison FFAlternatives

private def fiveCycle : BinaryLinear.GL (Fin 5 → ZMod 2) where
  toFun v := ![v 0, v 2, v 1 + v 2, v 3, v 4]
  invFun v := ![v 0, v 1 + v 2, v 1, v 3, v 4]
  map_add' := by decide +kernel
  map_smul' := by decide +kernel
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private theorem fiveCycle_pow : fiveCycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  decide +kernel

private theorem fiveCycle_ne_one : fiveCycle ≠ 1 := by
  intro h
  have hv := congrArg (fun g : BinaryLinear.GL (Fin 5 → ZMod 2) =>
    g ![0, 1, 0, 0, 0] 1) h
  exact zero_ne_one hv

private def naturalGL (n : ℕ) :
    Representation (ZMod 2) (BinaryLinear.GL (Fin n → ZMod 2)) (Fin n → ZMod 2) where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem naturalGL_fixer {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ∃ (A : Subgroup (BinaryLinear.GL (Fin n → ZMod 2)))
      (c : BinaryLinear.GL (Fin n → ZMod 2)),
      IsPGroup 2 A ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧
        ∀ v ∈ fixedSpace (naturalGL n) A, naturalGL n c v = v := by
  rcases hn with rfl | rfl
  · refine ⟨BinaryLinear.FourFixedSpace.unipotent, BinaryLinear.FourFixedSpace.cycle,
      BinaryLinear.FourFixedSpace.unipotent_two, BinaryLinear.FourFixedSpace.cycle_pow,
      BinaryLinear.FourFixedSpace.cycle_ne_one, BinaryLinear.FourFixedSpace.cycle_fixes_natural⟩
  · let W : Submodule (ZMod 2) (Fin 5 → ZMod 2) :=
      Submodule.span (ZMod 2) {Pi.single 0 1}
    have hW : W ≠ ⊥ := by
      apply mt Submodule.span_singleton_eq_bot.mp
      intro hz
      have hz0 := congrFun hz 0
      norm_num at hz0
    refine ⟨BinaryLinear.radical W, fiveCycle, BinaryLinear.radical_two W,
      fiveCycle_pow, fiveCycle_ne_one, ?_⟩
    intro v hv
    have hvW : v ∈ W := (BinaryLinear.mem_iff_fixed_radical hW v).mpr (by
      intro g hg
      exact hv ⟨g, hg⟩)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvW
    change fiveCycle (a • Pi.single 0 1) = a • Pi.single 0 1
    rw [map_smul]
    congr 1
    decide +kernel

private noncomputable def naturalEquiv (n : ℕ) :
    ActionEquiv (linearNatural BinaryField.two n) (naturalGL n) where
  groupEquiv := BinaryLinear.OuterCyclic.slEquivLinear n
  linearEquiv := LinearEquiv.refl _ _
  intertwines _ _ := rfl

private theorem transport_fixer {D E V W : Type*} [Group D] [Group E] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ)
    (h : ∀ T : Sylow 2 E, ∃ c : E, c ∉ T ∧ c ^ 3 = 1 ∧
      ∀ w ∈ fixedSpace σ (T : Subgroup E), σ c w = w) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v :=
  sylow_fixedSpace_enlargement_equivariant ρ σ (S : Subgroup D)
    e.groupEquiv e.linearEquiv e.intertwines (h (S.mapSurjective e.groupEquiv.surjective))

/-- Every binary natural module of dimension four or five has the required cubic fixer. -/
theorem natural_enlargement {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) D V}
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : ActionEquiv ρ (linearNatural BinaryField.two n))
    (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  let : Finite (BinaryLinear.GL (Fin n → ZMod 2)) :=
    Finite.of_equiv _ (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv
  apply transport_fixer e _ S
  intro T
  apply transport_fixer (naturalEquiv n) _ T
  intro R
  obtain ⟨A, c, hp, hc, hne, hf⟩ := naturalGL_fixer hn
  exact sylow_fixedSpace_enlargement_of_cubic _ A hp c hc hne hf R

/-- The same cubic acts on every identically marked natural summand, with arbitrary multiplicity. -/
theorem repeatedNatural_enlargement {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) D V}
    {n : ℕ} (hn : n = 4 ∨ n = 5) (r : ℕ)
    (e : ActionEquiv ρ (repeated (linearNatural BinaryField.two n) r)) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  let : Finite (BinaryLinear.GL (Fin n → ZMod 2)) :=
    Finite.of_equiv _ (BinaryLinear.OuterCyclic.slEquivLinear n).toEquiv
  apply transport_fixer e _ S
  intro T
  let f : ActionEquiv (repeated (linearNatural BinaryField.two n) r)
      (repeated (naturalGL n) r) :=
    ⟨BinaryLinear.OuterCyclic.slEquivLinear n, LinearEquiv.refl _ _, by intros; rfl⟩
  apply transport_fixer f _ T
  intro R
  obtain ⟨A, c, hp, hc, hne, hf⟩ := naturalGL_fixer hn
  apply sylow_fixedSpace_enlargement_of_cubic _ A hp c hc hne _ R
  intro v hv
  funext k
  exact hf (v k) (fun a => congrFun (hv a) k)

variable {G : Type*} [Group G] [Finite G]
  {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- Eliminate the binary natural central section on the original source action. -/
theorem sourceAction_not_natural (h : Input d i j H U K) {L : Subgroup (sourceGroup h)}
    (s : let := h.module_properties.1; MovedSection (sourceAction h) L)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : let := h.module_properties.1;
      ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two n)) : False := by
  let := h.module_properties.1
  obtain ⟨S, hS⟩ := exists_offenderSylow h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1
  let T : Sylow 2 L := Classical.choice inferInstance
  obtain ⟨c, hc, _, hf⟩ := NativeSections.movedSection_enlargement s T
    (natural_enlargement hn e T) S
  change ∀ v ∈ fixedSpace
    (offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1) (S : Subgroup _),
    offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1 c v = v at hf
  exact offenderAction_no_fixedSpace_enlargement h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1 (S : Subgroup _) hS c hc hf

/-- Eliminate B.5.1's repeated-natural moved submodule on the same original action. -/
theorem sourceAction_not_repeatedNatural (h : Input d i j H U K)
    {L : Subgroup (sourceGroup h)}
    (s : let := h.module_properties.1; MovedSection (sourceAction h) L)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (r : ℕ)
    (e : let := h.module_properties.1;
      ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural BinaryField.two n) r)) : False := by
  let := h.module_properties.1
  obtain ⟨S, hS⟩ := exists_offenderSylow h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1
  let T : Sylow 2 L := Classical.choice inferInstance
  obtain ⟨c, hc, _, hf⟩ := NativeSections.movedSpace_enlargement s T
    (repeatedNatural_enlargement hn r e T) S
  change ∀ v ∈ fixedSpace
    (offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1) (S : Subgroup _),
    offenderAction h.placed.sylow (d.Z.subgroupOf H) h.seed_inputs.2.2.1 c v = v at hf
  exact offenderAction_no_fixedSpace_enlargement h.placed.sylow (d.Z.subgroupOf H)
    h.seed_inputs.2.2.1 (S : Subgroup _) hS c hc hf

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition
