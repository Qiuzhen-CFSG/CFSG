module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions


/-!
# The literal moving-section representation for rank-one replacement

The displacement span in the B.5 classification is the actual subgroup
[W_K,K], written additively. We identify these two constructions, restrict the
faithful plus action, and form its quotient by the actual fixed vectors.
A classification intertwiner on this quotient gives the exact NaturalSection
consumed by RankOneBorel, with one actor isomorphism throughout.

Naturality is not assumed to have been proved here. The B.5.6 case analysis
and the use of 13.6.15 must construct the intertwiner in the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14–18, printed pp.929–931 (PDF pp.946–948).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection ComponentElimination.SourceTransferFields.RankOneBorel
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
local notation "W" => WK K L T z v
local notation "Kp" => plusImage K L T z v hL hz K
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v

/-- The source commutator is exactly the displacement span used by B.5. -/
theorem movingSpace_eq_subspaceCommutator : D = subspaceCommutator ρ ⊤ ⊤ := by
  let C := subspaceCommutator ρ ⊤ ⊤
  have hc : ⁅W, K⁆ ≤ C.toAddSubgroup.toSubgroup'.map (W).subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk w hw
    let a : Kp := componentMap K L T z v hL hz ⟨k, hk⟩
    let x : Additive W := Additive.ofMul ⟨w, hw⟩
    let d := ρ a x - x
    refine ⟨d.toMul, ?_, ?_⟩
    · change d ∈ C
      exact Submodule.subset_span ⟨a, Subgroup.mem_top _, x, Submodule.mem_top, rfl⟩
    · change (((ρ a x).toMul : W) : G) / w = _
      rw [componentRepresentation_mk, div_eq_mul_inv]
      rfl
  apply le_antisymm
  · intro w hw
    obtain ⟨d, hd, he⟩ := hc hw
    have hdw : Additive.ofMul d = w := congrArg Additive.ofMul (Subtype.ext he)
    exact hdw ▸ hd
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, _, w, _, rfl⟩
    exact displacement_mem K L T z v hL hz a w

/-- The literal moving subgroup is invariant under the literal plus action. -/
theorem movingSpace_invariant (a : Kp) (d : D) : ρ a d ∈ D := by
  have h := (D).add_mem (displacement_mem K L T z v hL hz a d) d.property
  simpa only [sub_add_cancel] using h

/-- Restriction to the source U_K = [W_K,K]. -/
noncomputable def movingSubrepresentation : Subrepresentation ρ where
  toSubmodule := D
  apply_mem_toSubmodule a d hd := movingSpace_invariant K L T z v hL hz a ⟨d, hd⟩

/-- The fixed vectors C_U_K(K), inside the actual moving space. -/
noncomputable def fixedInMoving : Subrepresentation
    (movingSubrepresentation K L T z v hL hz).toRepresentation where
  toSubmodule := (ρ).invariants.comap (D).subtype
  apply_mem_toSubmodule a d hd := by
    change ∀ b, ρ b (d : Additive W) = d at hd
    change ∀ b, ρ b (ρ a d) = ρ a d
    rw [hd a]
    exact hd

/-- The original plus action induced on U_K/C_U_K(K). -/
noncomputable def sectionRepresentation : Representation (ZMod 2) Kp
    (D ⧸ (ρ).invariants.comap (D).subtype) :=
  (fixedInMoving K L T z v hL hz).quotientRepresentation

/-- Faithfulness follows from the actual plus quotient, without a model assumption. -/
theorem componentRepresentation_faithful : Function.Injective ρ := by
  intro a b hab
  apply Subtype.ext
  apply plusAction_injective K L T z v hL hz
  ext w
  exact congrArg (fun x : Additive W => (x.toMul : G))
    (LinearMap.congr_fun hab (Additive.ofMul w))

open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.SpecialLinearGroup.RankOneResidual
variable [Finite G]

/-- Convert a classification intertwiner on the literal quotient into the
residual calculation's natural section, keeping the same actor isomorphism.
This conversion does not construct the classification intertwiner. -/
noncomputable def naturalSectionOfActionEquiv (F : BinaryField)
    (e : ActionEquiv (sectionRepresentation K L T z v hL hz) (linearNatural F 2)) :
    NaturalSection (F := F.Carrier) ρ D where
  actor := e.groupEquiv
  invariant := movingSpace_invariant K L T z v hL hz
  coordinates := e.linearEquiv
  equivariant a d := e.intertwines a (Submodule.Quotient.mk d)

/-- The classification coordinates feed the existing residual calculation
on the original W_K. The Borel is marked by the very same actor map. -/
theorem source_fixed_space_of_actionEquiv (F : BinaryField) (hn : 2 < F.degree)
    (e : ActionEquiv (sectionRepresentation K L T z v hL hz) (linearNatural F 2))
    (B : Subgroup Kp)
    (hB : B.map e.groupEquiv.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F.Carrier) :
    fixedSpace ρ ((piResidual twoThreePrimes B).map B.subtype) = (ρ).invariants :=
  source_fixed_space K L T z v hL hz hn F.card_eq
    (naturalSectionOfActionEquiv K L T z v hL hz F e) B hB
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action

end
