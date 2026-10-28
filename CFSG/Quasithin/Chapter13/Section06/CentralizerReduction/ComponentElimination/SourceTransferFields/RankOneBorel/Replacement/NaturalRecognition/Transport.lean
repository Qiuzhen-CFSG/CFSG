module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.Contracts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# Returning the classified section to the original component action

For any subgroup of the full plus actor containing K⁺, the component pulled
into that subgroup has exactly the original displacement space U_K. The
identity on W_K identifies its fixed kernel with C_U_K(K), and therefore
induces an equivariant equivalence of the literal central quotients. The
actor map is the inverse of the actual subgroup inclusion throughout.

The application in Source takes this subgroup to be the best-offender
subgroup. No splitting or block witness enters the comparison.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the B.5.6
application in the first paragraph of 13.6.18, printed p.931 (PDF p.948).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
open ComponentSelection ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
namespace ClassifierTransport
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
  (hL : Tv T v ≤ normalizer (Lv L v : Set G))
  (hz : Tv T v ≤ centralizer ({z} : Set G))
  [IsElementaryAbelian 2 (WK K L T z v)]
local notation "Kp" => plusImage K L T z v hL hz K
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v
variable (J : Subgroup (Gplus K L T z v hL hz)) (hJ : plusImage K L T z v hL hz K ≤ J)
local notation "σ" => MonoidHom.comp (wkRepresentation K L T z v hL hz) J.subtype
local notation "Cj" => Subgroup.subgroupOf (plusImage K L T z v hL hz K) J
variable (s : MovedSection ((wkRepresentation K L T z v hL hz).comp J.subtype)
  ((plusImage K L T z v hL hz K).subgroupOf J))

include hJ in
/-- The classified displacement span equals the literal source U_K. -/
theorem space_eq_moving : s.space.toSubmodule = D := by
  rw [s.space_eq, Replacement.Action.movingSpace_eq_subspaceCommutator K L T z v hL hz]
  apply congrArg (Submodule.span (ZMod 2))
  ext x
  constructor
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact ⟨⟨a, ha⟩, mem_top _, w, hw, rfl⟩
  · rintro ⟨a, _, w, hw, rfl⟩
    exact ⟨⟨a, hJ a.property⟩, a.property, w, hw, rfl⟩

/-- The comparison is the identity on the underlying vectors in W_K. -/
noncomputable def movingEquiv : D ≃ₗ[ZMod 2] s.space.toSubmodule where
  toFun x := ⟨x, (space_eq_moving K L T z v hL hz J hJ s).symm ▸ x.property⟩
  invFun x := ⟨x, (space_eq_moving K L T z v hL hz J hJ s) ▸ x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict the actual actor along the inverse of its subgroup inclusion. -/
noncomputable def movingActionEquiv :
    ActionEquiv (Replacement.Action.movingSubrepresentation K L T z v hL hz).toRepresentation
      (s.space.toRepresentation.comp (Cj).subtype) where
  groupEquiv := (subgroupOfEquivOfLe hJ).symm
  linearEquiv := movingEquiv K L T z v hL hz J hJ s
  intertwines _ _ := rfl

/-- The same comparison identifies exactly the component-fixed kernels. -/
theorem central_map :
    (((ρ).invariants.comap (D).subtype).map
      (movingEquiv K L T z v hL hz J hJ s).toLinearMap) = s.central.toSubmodule := by
  ext x
  rw [Submodule.mem_map_equiv, s.central_eq]
  constructor
  · intro hx a
    apply Subtype.ext
    exact hx ⟨a.val.val, a.property⟩
  · intro hx a
    exact congrArg Subtype.val (hx ((subgroupOfEquivOfLe hJ).symm a))

/-- The induced quotient coordinates intertwine the original plus action. -/
noncomputable def sectionActionEquiv :
    ActionEquiv (Replacement.Action.sectionRepresentation K L T z v hL hz)
      (s.action.comp (Cj).subtype) where
  groupEquiv := (subgroupOfEquivOfLe hJ).symm
  linearEquiv := Submodule.Quotient.equiv _ _ (movingEquiv K L T z v hL hz J hJ s)
    (central_map K L T z v hL hz J hJ s)
  intertwines a x := by
    induction x using Submodule.Quotient.induction_on with | _ x => rfl

include hJ in
/-- Full commutator generation and irreducibility survive the actor comparison. -/
theorem isIrrPlus_moving (hi : IsIrrPlus σ Cj s.space.toSubmodule) :
    IsIrrPlus ρ ⊤ D := by
  have he := hi.of_intertwining σ ρ
    ((subgroupOfEquivOfLe hJ).trans (Subgroup.topEquiv (G := Kp)).symm).toMonoidHom
    ((subgroupOfEquivOfLe hJ).trans (Subgroup.topEquiv (G := Kp)).symm).surjective
    LinearMap.id Function.injective_id (fun _ _ => rfl) (Submodule.map_id _)
  rwa [space_eq_moving K L T z v hL hz J hJ s] at he

end ClassifierTransport

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
end
