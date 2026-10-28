module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CommonActors

/-!
# Binary chief homogeneity under one original actor

Full B.4.2 retains its offender-generation equality as well as naturality.
Restriction preserves the common original best offender, so that equality
places the same ratio-preserving offender inside the component. Its action
then bounds every faithful irreducible component submodule.

The proved common-mark natural/dual dichotomy and the genuine B.4.9 pair
exclusion imply that all irreducible component submodules are isomorphic.
This is the homogeneity hypothesis needed by A.1.42; neither a chosen marking
nor a homogeneous decomposition is an input to the final chief theorem.

Source: Aschbacher--Smith B.5.1, pp.100–101, the homogeneous-chief step
following (++), before the socle cases (I)–(II).
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped ENNReal MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
theorem binary_generated_of_ratio {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) {L H : Subgroup G}
    (h : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L H)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2))
    (hq : quadraticRatio ρ < 1) (hfour : d = 4 → quadraticRatio ρ < 3 / 4) :
    H = L := by
  obtain ⟨an⟩ := binary_natural_of_ratio ρ h hd mark hq hfour
  cases h with
  | linearThree F _ e _ =>
    exact (no_linearThree_binary_equiv F hd (e.groupEquiv.symm.trans mark)).elim
  | binaryLinear _ _ hg _ _ => exact hg
  | symplectic F _ _ e _ =>
    exact (no_symplectic_binary_equiv F hd (e.groupEquiv.symm.trans mark)).elim
  | symplecticTwo e _ =>
    exact (no_symplecticTwo_binary_equiv hd (e.subgroupEquiv.symm.trans mark)).elim
  | symmetricEight _ e _ =>
    have hn : Module.finrank (ZMod 2) V = d := by
      have hh := an.linearEquiv.finrank_eq
      change Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (Fin d → ZMod 2) at hh
      simpa using hh
    have he : Module.finrank (ZMod 2) V = 6 := by
      have hh := e.action.linearEquiv.finrank_eq
      rw [BinaryPermutation.finrank_natural_even (Fin 8) (by decide)] at hh
      simpa using hh
    rcases hd with rfl | rfl <;> omega
  | linearTwo _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | g2 _ _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | g2Two _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | symmetric _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | alternatingSix _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | alternatingSeven _ _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | tripleSix _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | orthogonalSix _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim
  | exteriorFive _ _ _ _ _ hr => rw [hr] at hq; exact (lt_irrefl _ hq).elim

/-- Retain the natural constituent's original component marking when its
local CB action has been identified by the full earlier catalogue. -/
theorem natural_on_component
    {G : Type u} [Group G] [Finite G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (C : Subgroup G) [IsQuasisimple C]
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    {B : Subgroup G} (hB : IsBestOffender ρ B)
    (W : Subrepresentation (ρ.comp C.subtype))
    (hs : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule)
    {F : BinaryField} {n : ℕ}
    (hn : IsLinearNatural
      ((invariantSubspace ρ (C ⊔ B) W.toSubmodule hs).toRepresentation.comp
        (generalizedFitting ↥(C ⊔ B)).subtype) F n) : IsLinearNatural W.toRepresentation F n := by
  obtain ⟨a⟩ := hn
  let e := local_component_equiv ρ C hfit hcore hB
  refine ⟨{ groupEquiv := e.symm.trans a.groupEquiv
            linearEquiv := a.linearEquiv
            intertwines := ?_ }⟩
  intro c v
  exact a.intertwines (e.symm c) v

/-- One actual common minimal offender is contained in C and identifies
all faithful irreducible C-constituents in the same binary degree. -/
theorem binary_common_offender {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (ρ : Representation (ZMod 2) G V)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hdec : FaithfulConstituentDecomposition ρ C)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : C ≃* SL(d,ZMod 2))
    (hq : quadraticRatio ρ < 1) (hfour : d = 4 → quadraticRatio ρ < 3 / 4) :
    ∃ B, IsMinimalBestOffender ρ B ∧ B ≤ C ∧ actionRatio ρ B ≤ quadraticRatio ρ ∧
      ∀ W : Subrepresentation (ρ.comp C.subtype), IsIrreducible W.toRepresentation →
        Function.Injective W.toRepresentation → IsLinearNatural W.toRepresentation BinaryField.two d := by
  obtain ⟨B, hB, hb⟩ := exists_minimal_ratio ρ hq.le le_rfl
  have classify (W : Subrepresentation (ρ.comp C.subtype))
      (hi : IsIrreducible W.toRepresentation) (hf : Function.Injective W.toRepresentation) :=
    constituent_classification ρ hK earlier C hC hfit hcore hfaith hB W hi hf
  have hmark := (local_component_equiv ρ C hfit hcore hB.1).trans mark
  have bound (W : Subrepresentation (ρ.comp C.subtype))
      (hs : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule) :
      quadraticRatio (invariantSubspace ρ (C ⊔ B) W.toSubmodule hs).toRepresentation ≤ quadraticRatio ρ :=
    (constituent_ratio_le ρ hB W hs).trans hb
  obtain ⟨W, hi, hf⟩ := hdec.exists_constituent ρ
  obtain ⟨hs, hc⟩ := classify W hi hf
  have hgen := binary_generated_of_ratio _ hc hd hmark ((bound W hs).trans_lt hq)
    (fun he => (bound W hs).trans_lt (hfour he))
  refine ⟨B, hB, constituent_generation_contains_offender ρ C hfit hcore hB.1 W hs hgen, hb, ?_⟩
  intro U hiU hfU
  obtain ⟨hsU, hcU⟩ := classify U hiU hfU
  apply natural_on_component ρ C hfit hcore hB.1 U hsU
  exact binary_natural_of_ratio _ hcU hd hmark ((bound U hsU).trans_lt hq)
    (fun he => (bound U hsU).trans_lt (hfour he))

/-- The common actor and the actual pair exclusion make every two
irreducible component submodules isomorphic, before A.1.42 is applied. -/
theorem binary_chief_homogeneous {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hi : IsIrreducible ρ)
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : C ≃* SL(d,ZMod 2))
    (hq : quadraticRatio ρ < 1) (hbound : quadraticRatio ρ ≤ 3 / 4)
    (hfour : d = 4 → quadraticRatio ρ < 3 / 4) :
    ∀ U W : Subrepresentation (ρ.comp C.subtype),
      IsIrreducible U.toRepresentation → IsIrreducible W.toRepresentation →
        Nonempty (U.toRepresentation.Equiv W.toRepresentation) := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hc : Nat.card (center C) = 1 ∨ Nat.card (center C) = 3 := by
    left
    rw [Nat.card_congr (centerCongr mark).toEquiv,
      BinaryLinear.OuterCyclic.binary_center_eq_bot (by rcases hd with rfl | rfl <;> decide)]
    exact Subgroup.card_bot
  have hdec := faithful_constituent_decomposition ρ hfaith hi C hc
  obtain ⟨B, hB, hBC, hr, hn⟩ := binary_common_offender ρ hK earlier C hC hfit hcore hfaith
    hdec hd mark hq hfour
  have hbC : IsElementaryTwo (B.subgroupOf C) := (hB.1.subgroupOf ρ hBC).1
  have hqC : IsQuadratic (ρ.comp C.subtype) (B.subgroupOf C) := by
    intro a ha b hb v
    exact hB.isQuadratic ρ a.val ha b.val hb v
  have hrC : actionRatio (ρ.comp C.subtype) (B.subgroupOf C) ≤ 3 / 4 := by
    simpa only [actionRatio, fixedCodim_subgroupOf ρ hBC, rank_subgroupOf hBC] using hr.trans hbound
  intro U W hiU hiW
  have hU := (Subrepresentation.irreducible_iff_isAtom U).mp hiU
  have hW := (Subrepresentation.irreducible_iff_isAtom W).mp hiW
  have hfU := constituent_faithful ρ hfaith hi C hc U hU.ne_bot
  have hfW := constituent_faithful ρ hfaith hi C hc W hW.ne_bot
  by_cases heq : U = W
  · subst W
    exact ⟨Representation.Equiv.refl _⟩
  have hdUW := hU.disjoint_of_ne hW heq
  have hdis : Disjoint U.toSubmodule W.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    intro v hvU hvW
    have hm : v ∈ U ⊓ W := ⟨hvU, hvW⟩
    rw [hdUW.eq_bot] at hm
    exact hm
  obtain ⟨e⟩ := binary_disjoint_naturals_same (ρ.comp C.subtype) U W hdis hbC hqC hrC hd
    hfU (hn U hiU hfU) (hn W hiW hfW)
  exact ⟨e.symm⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
