module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SelfNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationPreparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ActionGeneration

/-!
# Source inputs to the Borel analysis

These are the local hypotheses at the start of 15.3.49(k), after the
legitimate replacement H = ⟨L^T⟩Y₀T. The section is the actual U_H/Z action,
the selected V_α is a quadratic best offender in O₂(Y₀*T*), and (i) and
universal (j) remain explicit earlier inputs. There are no model conclusions
or containment conclusions in this structure.

The lemmas derive relative component membership, the intrinsic cubic
quotient, the B.5.3 application hypotheses, and the local conclusions for
an identified solvable Borel. Classifying the models and proving the
automorphism calculation are separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1144, proof of 15.3.49(i)–(k).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine inputs retained by the owner of (k), before any model exclusions. -/
structure SourceSetup (κ : GroupClass.{u}) (H M Y V Y0 L ZS Z A : Subgroup G)
    (T : Sylow 2 G) [IsElementaryAbelian 2 (localSpan ZS H)] where
  extraspecial : ExtraspecialCase M Y V
  residual : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G))
  solvable : Group.IsSolvable (M ⊓ H : Subgroup G)
  sqtk : IsSQTK κ H
  replacement : H = reducedOvergroup L Y0 T
  sylow_le : (T : Subgroup G) ≤ M
  theta_eq : theta (M ⊓ H) = Y0
  normalizer_eq : normalizer (Y0 : Set G) = M
  action : SectionAction H (localSpan ZS H) Z
  actor_le : A ≤ H
  best : IsBestOffender action.representation (starImage H A)
  quadratic : IsQuadratic action.representation (starImage H A)
  actor_core : starImage H A ≤
    (pCore 2 ↥(starImage H Y0 ⊔ starImage H (T : Subgroup G))).map
      (starImage H Y0 ⊔ starImage H (T : Subgroup G)).subtype
  component_le : L ≤ localSpan A H
  component : (L.subgroupOf (localSpan A H)).IsCComponent
  component_generation :
    (cComponentLayer (localSpan A H)).map (localSpan A H).subtype = localSpan A H
  component_action : ∀ C : Subgroup G, C ≤ localSpan A H →
    (C.subgroupOf (localSpan A H)).IsCComponent → C = ⁅C, Y0⁆
  solvable_control : ∀ K : Subgroup G, Group.IsSolvable K →
    Y0 ⊔ (T : Subgroup G) ≤ K → K ≤ H → K ≤ M ⊓ H

namespace SourceSetup
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

omit [Finite G] in
theorem component_in_H : (L.subgroupOf H).IsCComponent :=
  localSpan_component_isCComponent A H L d.actor_le d.component_le d.component

omit [Finite G] in
theorem commutator_eq : L = ⁅L, Y0⁆ :=
  d.component_action L d.component_le d.component

omit [Finite G] in
theorem sylow_normalizes : (T : Subgroup G) ≤ normalizer (Y0 : Set G) :=
  d.sylow_le.trans_eq d.normalizer_eq.symm

omit [Finite G] in
/-- Each individual T-conjugate retains its commutator generation by Y₀. -/
theorem conjugate_commutator_eq (t : G) (ht : t ∈ (T : Subgroup G)) :
    L.map (MulAut.conj t).toMonoidHom = ⁅L.map (MulAut.conj t).toMonoidHom, Y0⁆ := by
  have hYmap : Y0.map (MulAut.conj t).toMonoidHom = Y0 :=
    mem_normalizer_iff_map_conj_eq.mp (d.sylow_normalizes ht)
  conv_lhs => rw [d.commutator_eq]
  rw [map_commutator, hYmap]

omit [Finite G] in
/-- Y₀* fixes every T-conjugate component individually, before any orbit bound
or identification of the closure with a single component. -/
theorem conjugate_star_normalized (t : G) (ht : t ∈ (T : Subgroup G)) :
    starImage H Y0 ≤ normalizer
      (starImage H (L.map (MulAut.conj t).toMonoidHom) : Set (H ⧸ pCore 2 H)) := by
  have hCL : L.map (MulAut.conj t).toMonoidHom ≤ localSpan L T := by
    rintro x ⟨l, hl, rfl⟩
    exact subset_closure ⟨t, ht, l, hl, rfl⟩
  have hCH : L.map (MulAut.conj t).toMonoidHom ≤ H :=
    hCL.trans (d.replacement ▸ le_sup_left)
  have hYH : Y0 ≤ H := (d.theta_eq ▸ theta_le _).trans inf_le_right
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← starImage_commutator H _ Y0 hCH hYH, ← d.conjugate_commutator_eq t ht]

/-- The order is internal to Y₀ in H, not the order of its star image. -/
theorem cubic_quotient :
    Nat.card ((Y0.subgroupOf H) ⧸ pCore 2 (Y0.subgroupOf H)) = 3 :=
  residual_quotient_card_in H M Y V Y0 d.extraspecial d.residual
    ((d.theta_eq ▸ theta_le _).trans inf_le_right)

/-- The actual B.5.3 hypotheses for the offender-generated star group. -/
theorem classification_hypotheses :
    let ρ := d.action.representation.comp (starImage H (localSpan A H)).subtype
    Module.Finite (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))) ∧
      Function.Injective ρ ∧ pCore 2 (starImage H (localSpan A H)) = ⊥ ∧
      offenderSubgroup ρ = ⊤ ∧ IsSQTK κ ((localSpan A H).subgroupOf H) ∧
      IsFFModule ρ :=
  FactorGeneration.star_span_classification_hypotheses H ZS Z A d.action
    d.sqtk d.actor_le d.best

/-- Borel invariance, control, and its action modulo the Sylow intersection.
The identification and solvability of the actual Borel remain model inputs. -/
theorem borel_control (B : Subgroup G) [Group.IsSolvable B]
    (hout : ¬ Y0 ≤ localSpan L T)
    (hB : B = localSpan L T ⊓
      normalizer (((T : Subgroup G) ⊓ localSpan L T : Subgroup G) : Set G)) :
    (Y0 ⊔ (T : Subgroup G)) ⊓ localSpan L T = (T : Subgroup G) ⊓ localSpan L T ∧
    Y0 ⊔ (T : Subgroup G) ≤ normalizer (B : Set G) ∧
    B ≤ M ⊓ H ∧ ¬ 3 ∣ Nat.card B ∧ B ≤ normalizer (Y0 : Set G) ∧
    ⁅B, Y0⁆ ≤ (T : Subgroup G) ⊓ localSpan L T := by
  let _ := d.solvable
  obtain ⟨hi, hn, hM, hthree, hY⟩ :=
    borel_control_of_extraspecial H M Y V Y0 L B T d.extraspecial d.residual
      d.replacement d.sylow_le d.theta_eq d.normalizer_eq d.commutator_eq hout hB
      d.solvable_control
  exact ⟨hi, hn, hM, hthree, hY,
    borel_commutator_le_sylow_intersection Y0 T (localSpan L T) B
      (hB ▸ inf_le_left) hY (le_sup_left.trans hn) hi⟩

end SourceSetup
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner
