module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.SmallComponentReduction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.BinaryQuadraticTransitivity
public import CFSG.Quasithin.ChapterG.Section11.WholePairNatural

/-!
# Natural orthogonal component orbits on the original large flag

The original extraspecial square form has nondegenerate polar form. Binary
G₂-derived natural recognition makes the remaining degree-six component
transitive on nonzero vectors, contradicting invariance of that square form.
Combined with the preceding exclusions, this closes the normal irreducible
component branch under both fixed-point clauses of G.11.1(3).

An irreducible component orbit must consequently have two distinct components.
The existing common-field tensor construction identifies their actual join
with the natural split orthogonal action. The final consumer constructs the
G.9 hypotheses from the original nondegenerate marked constituent.

This identifies the component-join action, not the whole terminal group.
The coefficient-field bound, whole-group marking, other multiplicities and
exchanged constituents remain required for marked-catalogue exhaustiveness.

Source: Aschbacher--Smith G.9.3(10,15), G.11.7 and 14.4.2,
printed pp.354--357,367--368,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original square form excludes a degree-six irreducible binary G₂-derived
subgroup: its actual natural action is transitive on all nonzero vectors. -/
theorem source_no_binary_g2_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 6)
    (C : Subgroup F.TerminalHdot)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (e₀ : C ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let := chosen.elementary
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  obtain ⟨g, _, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  let q := F.uhatQuadraticForm (by decide) c.two c.frattini_point
    (center_frattini_bot_of_center_point F c hZ)
  obtain ⟨_, hqi, hqn⟩ := quadratic_intersection_of_center_point F c (by decide) hZ g
    (disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
      c.seed_center g hgP hgH).1)
  have hterminal (a : F.TerminalHdot) (w : Additive F.Uhat) :
      q (F.terminalRepresentation a w) = q w := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a w.toMul
  let σ := (F.terminalRepresentation.comp C.subtype).comp e₀.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e₀.symm.toMonoidHom e₀.symm.surjective _).mpr hirr
  obtain ⟨a, f, hf⟩ :=
    ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix.quasiequivalent_of_finrank_eq_six σ hd
  have htrans : ∀ x y : Additive F.Uhat, x ≠ 0 → y ≠ 0 → ∃ b, σ b x = y := by
    intro x y hx hy
    obtain ⟨b, hb⟩ := Atlas.G2.Natural.derivedAction_transitive (ZMod 2) (f x) (f y)
      (fun hz => hx (f.map_eq_zero_iff.mp hz)) (fun hz => hy (f.map_eq_zero_iff.mp hz))
    refine ⟨a.symm b, f.injective ?_⟩
    rw [hf, a.apply_symm_apply]
    exact hb
  exact not_nondegenerate_quadratic_of_nonzero_transitive σ (by omega) htrans q
    (fun a w => hterminal (e₀.symm a) w) hqn

/-- There is no normal component acting irreducibly on the original large
extraspecial module. Both source fixed-point clauses are covered. -/
theorem source_no_normal_irreducible_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype)) : False := by
  obtain ⟨hd, ⟨e⟩⟩ := source_large_single_component_binary_g2 d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH C hC hm hirr
  exact source_no_binary_g2_component d earlier hq chosen structural alternatives F hne hZ hd C hirr e

/-- An irreducible component orbit in the original large action has two actual
components and the natural split orthogonal action on their join. -/
theorem source_large_irreducible_orbit_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C (componentOrbit C ⊤)
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) :
    ∃ n : ℕ, 1 < n ∧ ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
      (ChapterG.Section09.TwoComponents.fourOrthogonal n) := by
  have hproper : componentOrbit C ⊤ ≠ C := by
    intro he
    have h9' : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
        F.terminalRepresentation (F.terminalDot (F.X g)) C C
        (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
      simpa only [he] using h9
    let := h9'.normal_H
    exact source_no_normal_irreducible_component d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH C hC hm h9'.irreducible
  obtain ⟨_, _, B, v, hyp⟩ := source_terminal_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  obtain ⟨C₂,hC₂,hH,hCC₂,⟨e⟩,hz,hmrank,td,hk⟩ :=
    ChapterG.Section11.WholePair.component_pair_data h9 hproper
      (AlternatingForm.even_finrank B hyp.alternating hyp.nondegenerate)
  obtain ⟨_,hn,hmodel⟩ := ChapterG.Section11.WholePairNatural.recognition h9
    hC₂ hH hCC₂ e hz td hmrank hk
  exact ⟨td.n,hn,hmodel⟩

/-- Apply the orbit recognition to the actual nondegenerate marked constituent
selected from the original flag; its G.9 premises are constructed by the source. -/
theorem source_large_nondegenerate_component_natural (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C, F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I)
    (hv : v ∈ I) (hnd : (B.restrict I).Nondegenerate) :
    ∃ n : ℕ, 1 < n ∧ ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
      (ChapterG.Section09.TwoComponents.fourOrthogonal n) := by
  exact source_large_irreducible_orbit_natural d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH C hC hm
    (source_large_componentHypothesis_of_nondegenerate d earlier hq chosen structural
      alternatives F hne hZ hlarge g hgP hgH hyp hC hm hI hv hnd)

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
