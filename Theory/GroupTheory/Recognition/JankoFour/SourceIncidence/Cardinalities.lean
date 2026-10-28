module

public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Defs
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Cosets
public import Theory.GroupTheory.GraphUniquenessSystem.CosetResidue
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.NativePlaneFlags
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Cardinalities of the actual AS91 line and plane residues

The original normalizer quotient (K/R) × (S/R) and the special radical
compute the line-group order. The literal point-line quotient then gives
index five. The original cubic quotient identifies the plane intersection
with the native hexad stabilizer, of index 77. Explicit equivalences from
intersection cosets to ambient incident objects transport these counts to
every line and plane, without assuming a chart or flag transitivity.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (5.1)(1) and the
77-point action in (5.3)(1), pp.599–600, DOI 10.1007/BF01232280.
The orbit partition and ambient uniqueness in (5.3) are separate obligations.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceRecognition
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}

namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)
open SourceCycleBase GraphUniquenessSystem

/-- The line stabilizer order is computed from the original product quotient. -/
theorem line_group_card : Nat.card a.L.G₂ = 660602880 := by
  let := a.d.R_normal_in_normalizer
  let : IsElementaryAbelian 2 a.d.space := a.d.elementary
  have hR : a.d.R ≤ normalizer (a.d.space : Set G) :=
    inf_le_left.trans a.d.K_le_normalizer
  have hquot : Nat.card (normalizer (a.d.space : Set G) ⧸
      a.d.R.subgroupOf (normalizer (a.d.space : Set G))) = 20160 := by
    rw [Nat.card_congr (a.d.markedNormalizerQuotientEquiv h).toEquiv, Nat.card_prod,
      card_mulAut_of_elementary_eight a.d.space a.d.card]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [a.line_normalizer, Subgroup.card_eq_card_quotient_mul_card_subgroup
    (a.d.R.subgroupOf (normalizer (a.d.space : Set G))), hquot,
    Nat.card_congr (subgroupOfEquivOfLe hR).toEquiv, a.d.R_card h]

theorem point_line_card : Nat.card (a.P.M ⊓ a.L.G₂ : Subgroup G) = 132120576 := by
  have hq : Nat.card ((a.P.M ⊓ a.L.G₂ : Subgroup G) ⧸
      pCore 2 (a.P.M ⊓ a.L.G₂ : Subgroup G)) = 1008 := by
    rw [Nat.card_congr a.L.pointLineQuotient.toEquiv, Nat.card_prod, Matrix.PSL3Two.card_PSL]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (pCore 2 (a.P.M ⊓ a.L.G₂ : Subgroup G)), hq, a.L.point_line_core_card]
  norm_num

/-- The five-point action uses N/K, not N/S. This computes its literal coset degree. -/
theorem point_line_index : (a.P.M.subgroupOf a.L.G₂).index = 5 := by
  have hc : Nat.card (a.P.M.subgroupOf a.L.G₂) = 132120576 := by
    have he : (a.P.M ⊓ a.L.G₂).subgroupOf a.L.G₂ = a.P.M.subgroupOf a.L.G₂ := by
      ext u
      simp only [mem_subgroupOf, mem_inf, u.property, and_true]
    rw [← he, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact a.point_line_card
  have hm := (a.P.M.subgroupOf a.L.G₂).card_mul_index
  rw [hc, a.line_group_card] at hm
  omega

theorem point_plane_index : (a.P.M.subgroupOf (centralizer z)).index = 77 := by
  rw [a.P.overlap, (designStabilizer a.P.hexad).index_comap_of_surjective
      (CubicLift.projection_surjective a.P.cubic),
    designStabilizer, index_map_of_bijective
      ⟨m22DesignAutToAut_injective, m22DesignAutToAut_surjective⟩]
  have hm := (MulAction.stabilizer m22DesignAut a.P.hexad).card_mul_index
  rw [native_hex_card a.P.hexad_mem, m22DesignAut_order] at hm
  omega

omit [Finite G] in
private noncomputable def incidentCosetEquiv (A B : Subgroup G) (g : G) :
    (B ⧸ A.subgroupOf B) ≃
      {x : Cosets.Vertex A // Cosets.Incident A B x (Cosets.vertex B g)} :=
  (Cosets.residueEquiv B A).trans {
    toFun x := ⟨g • x.val, by
      obtain ⟨k, hk, hx⟩ := x.property
      refine ⟨g * k, ?_, ?_⟩
      · rw [← hx]; rfl
      · have hh := congrArg (fun b : Cosets.Vertex B => g • b) hk
        simpa only [Cosets.smul_vertex, mul_one] using hh⟩
    invFun x := ⟨g⁻¹ • x.val, by
      obtain ⟨k, hk, hx⟩ := x.property
      refine ⟨g⁻¹ * k, ?_, ?_⟩
      · have hh := congrArg (fun b : Cosets.Vertex B => g⁻¹ • b) hx
        simpa only [Cosets.smul_vertex, inv_mul_cancel] using hh
      · rw [← hk]; rfl⟩
    left_inv x := Subtype.ext (inv_smul_smul g x.val)
    right_inv x := Subtype.ext (smul_inv_smul g x.val) }

/-- AS91 (5.1)(1): every actual ambient line has five incident points. -/
theorem line_card (l : Line a.L) : {x | OnLine a.L x l}.ncard = 5 := by
  induction l using QuotientGroup.induction_on with
  | H g =>
    change Nat.card {x : Cosets.Vertex a.P.M //
      Cosets.Incident a.P.M a.L.G₂ x (Cosets.vertex a.L.G₂ g)} = 5
    rw [← Nat.card_congr (incidentCosetEquiv a.P.M a.L.G₂ g)]
    exact a.point_line_index

/-- The literal plane residue has 77 points, using the original cubic overlap. -/
theorem plane_card (π : Plane z) : {x | OnPlane a.P x π}.ncard = 77 := by
  induction π using QuotientGroup.induction_on with
  | H g =>
    change Nat.card {x : Cosets.Vertex a.P.M //
      Cosets.Incident a.P.M (centralizer z) x (Cosets.vertex (centralizer z) g)} = 77
    rw [← Nat.card_congr (incidentCosetEquiv a.P.M (centralizer z) g)]
    exact a.point_plane_index


end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
