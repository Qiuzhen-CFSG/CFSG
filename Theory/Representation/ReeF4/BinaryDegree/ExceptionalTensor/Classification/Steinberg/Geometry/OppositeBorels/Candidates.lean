module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Realization
public import Theory.AlgebraicGroup.RootSubgroups.ClosedGeneration

/-!
# The literal positive and opposite F4 candidates

For the corrected root datum on the concrete F4 carrier, construct the closed
connected root-generated groups and their products with the fixed split torus.
The positive roots are exactly `typeF4RootPairing_base.IsPos`; opposition is
the original root negation. No representation weight or coroot word changes.
Torus normalization gives the exact products and relative normality. Borel
maximality, unipotence and opposite separation are separate obligations.

Source: GLS3, Theorems 1.11.2 and 1.11.4
(`refs/KGroup/GLS3/Chapter1.tex`), and Steinberg (6.2)
(`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
open RootModel.Corrected
universe u
variable (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2]

/-- The literal labels of the concrete root model. -/
abbrev Roots := (rootSystemModel (F := F)).rootData.Root

/-- The original standard-base positive roots. -/
abbrev positiveRoots : Set (Roots F) := (rootSystemModel (F := F)).rootData.positive

/-- The negatives of the same labelled positive roots. -/
abbrev negativeRoots : Set (Roots F) :=
  (rootSystemModel (F := F)).rootData.neg ⁻¹' positiveRoots F

/-- The actual closed root-generated subgroup for any selected labels. -/
def rootGenerated (A : Set (Roots F)) : ClosedSubgroup (F4Chevalley.Carrier (k := F)) :=
  (rootSystemModel (F := F)).rootData.generatedClosedSubgroup
    rootData_isRealization_charTwo A

/-- The actual closed product of the split torus and selected root groups. -/
def torusRootGenerated (A : Set (Roots F)) : ClosedSubgroup (F4Chevalley.Carrier (k := F)) :=
  (rootSystemModel (F := F)).rootData.torusGeneratedClosedSubgroup
    rootData_isRealization_charTwo F4Chevalley.splitTorus_isSubtorus A

@[simp] theorem rootGenerated_toSubgroup (A : Set (Roots F)) :
    (rootGenerated F A).toSubgroup =
      RootSubgroupGenerated (rootSystemModel (F := F)).rootData A := rfl

@[simp] theorem torusRootGenerated_toSubgroup (A : Set (Roots F)) :
    (torusRootGenerated F A).toSubgroup =
      (F4Chevalley.splitTorus (k := F)).toSubgroup ⊔ (rootGenerated F A).toSubgroup := rfl

theorem rootGenerated_connected (A : Set (Roots F)) :
    _root_.IsConnected (rootGenerated F A : Set (Variety.Point (F4Chevalley.Carrier (k := F)))) :=
  (rootSystemModel (F := F)).rootData.generatedClosedSubgroup_connected
    rootData_isRealization_charTwo A

theorem torusRootGenerated_connected (A : Set (Roots F)) :
    _root_.IsConnected (torusRootGenerated F A :
      Set (Variety.Point (F4Chevalley.Carrier (k := F)))) :=
  (rootSystemModel (F := F)).rootData.torusGeneratedClosedSubgroup_connected
    rootData_isRealization_charTwo F4Chevalley.splitTorus_isSubtorus A

/-- Exact factorization by the same torus and literal root subgroups. -/
theorem mem_torusRootGenerated_iff (A : Set (Roots F))
    (x : Variety.Point (F4Chevalley.Carrier (k := F))) :
    x ∈ torusRootGenerated F A ↔ ∃ t u,
      t ∈ F4Chevalley.splitTorus ∧ u ∈ rootGenerated F A ∧ x = t * u :=
  (rootSystemModel (F := F)).rootData.mem_torusGeneratedClosedSubgroup_iff
    rootData_isRealization_charTwo F4Chevalley.splitTorus_isSubtorus A x

/-- The fixed torus is contained in each candidate. -/
theorem torus_le_torusRootGenerated (A : Set (Roots F)) :
    F4Chevalley.splitTorus ≤ torusRootGenerated F A :=
  (show (F4Chevalley.splitTorus (k := F)).toSubgroup ≤
    (torusRootGenerated F A).toSubgroup from le_sup_left)

/-- The selected roots are contained in their torus/root product. -/
theorem rootGenerated_le_torusRootGenerated (A : Set (Roots F)) :
    rootGenerated F A ≤ torusRootGenerated F A :=
  (show (rootGenerated F A).toSubgroup ≤
    (torusRootGenerated F A).toSubgroup from le_sup_right)

/-- Relative normality in the candidate, with the literal inclusion. -/
theorem rootGenerated_normal_in_torusRootGenerated (A : Set (Roots F)) :
    ((rootGenerated F A).toSubgroup.subgroupOf
      (torusRootGenerated F A).toSubgroup).Normal :=
  (rootSystemModel (F := F)).rootData.generatedClosedSubgroup_normal_in_torusGenerated
    rootData_isRealization_charTwo F4Chevalley.splitTorus_isSubtorus A

/-- The positive root-generated group, before its unipotence certification. -/
abbrev positiveUnipotent := rootGenerated F (positiveRoots F)

/-- The negative root-generated group, before its unipotence certification. -/
abbrev negativeUnipotent := rootGenerated F (negativeRoots F)

/-- The positive Borel candidate, defined as the actual `T U+`. -/
abbrev positiveCandidate := torusRootGenerated F (positiveRoots F)

/-- The opposite Borel candidate, defined as the actual `T U-`. -/
abbrev negativeCandidate := torusRootGenerated F (negativeRoots F)

theorem mem_positiveRoots (r : F4Chevalley.Root) :
    (⟨r⟩ : Roots F) ∈ positiveRoots F ↔ typeF4RootPairing_base.IsPos r := Iff.rfl

theorem positive_union_negative : positiveRoots F ∪ negativeRoots F = Set.univ :=
  (rootSystemModel_isPositiveSystem (F := F)).2.1

theorem positive_inter_negative : positiveRoots F ∩ negativeRoots F = ∅ :=
  (rootSystemModel_isPositiveSystem (F := F)).1

/-- Literal root elements belong to the candidate carrying their original labels. -/
theorem rootElement_mem_rootGenerated (A : Set (Roots F))
    (r : F4Chevalley.Root) (hr : (⟨r⟩ : Roots F) ∈ A) (t : F) :
    algebraicRootElement r t ∈ rootGenerated F A := by
  apply rootSubgroup_le_RootSubgroupGenerated (rootSystemModel (F := F)).rootData hr
  exact ⟨kPlusPoint t, rfl⟩

/-- All literal root subgroups generate the full carrier. -/
theorem rootGenerated_univ_eq_top : (rootGenerated F Set.univ).toSubgroup = ⊤ := by
  apply top_unique
  rw [← algebraicRootElements_generate]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨⟨r, t⟩, rfl⟩
  exact rootElement_mem_rootGenerated F Set.univ r (Set.mem_univ _) t

/-- Both signs together generate the full point group; this alone is not density. -/
theorem positiveUnipotent_sup_negativeUnipotent :
    (positiveUnipotent F).toSubgroup ⊔ (negativeUnipotent F).toSubgroup = ⊤ := by
  change RootSubgroupGenerated (rootSystemModel (F := F)).rootData (positiveRoots F) ⊔
    RootSubgroupGenerated (rootSystemModel (F := F)).rootData (negativeRoots F) = ⊤
  rw [← RootSubgroupGenerated_union, positive_union_negative]
  exact rootGenerated_univ_eq_top F

/-- Opposite separation suffices for the exact torus intersection. The
separation hypothesis remains a geometric obligation. -/
theorem intersection_eq_torus_of_disjoint
    (hsep : Disjoint (positiveUnipotent F).toSubgroup (negativeCandidate F).toSubgroup) :
    (positiveCandidate F).toSubgroup ⊓ (negativeCandidate F).toSubgroup =
      (F4Chevalley.splitTorus (k := F)).toSubgroup := by
  apply le_antisymm
  · intro x hx
    obtain ⟨t, v, ht, hv, hxv⟩ :=
      (mem_torusRootGenerated_iff F (positiveRoots F) x).mp hx.1
    have htneg := torus_le_torusRootGenerated F (negativeRoots F) ht
    have hvneg : v ∈ (negativeCandidate F).toSubgroup := by
      have h := (negativeCandidate F).toSubgroup.mul_mem
        ((negativeCandidate F).toSubgroup.inv_mem htneg) hx.2
      simpa only [hxv, inv_mul_cancel_left] using h
    have hvone := Subgroup.disjoint_def.mp hsep hv hvneg
    rw [hxv, hvone, mul_one]
    exact ht
  · intro x hx
    exact ⟨torus_le_torusRootGenerated F (positiveRoots F) hx,
      torus_le_torusRootGenerated F (negativeRoots F) hx⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
