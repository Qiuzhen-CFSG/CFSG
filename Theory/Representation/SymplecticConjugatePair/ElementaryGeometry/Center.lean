module

public import Theory.Representation.SymplecticConjugatePair.Parabolics
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson

/-!
# Fixed spaces of subgroups of the symplectic Sylow center

The center is embedded in the actual matrix group through its Sylow inclusion.
Its two root parameters transform as `(s,t) ↦ (t²,s)` under the exceptional
graph automorphism. The resulting fixed equations show that a subgroup lying
in neither coordinate root has fixed space plane × plane. Nontrivial subgroups
of a coordinate root have the previously proved codimension 3n; the other
central subgroups have codimension 4n. Their orders then give the strict F−1
inequality, including the full central four-group over the binary field.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389. This module concerns the actual full symplectic group;
it does not put a full-group witness into the derived subgroup.
-/

@[expose] public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

noncomputable def sylowCenter : Subgroup (Sp F) :=
  (Subgroup.center (unipotent (F := F))).map (unipotent (F := F)).subtype

lemma mem_sylowCenter_iff (g : Sp F) : g ∈ sylowCenter ↔
    ∃ s t : F, rootElement 0 s * rootElement 4 t = g := by
  rw [sylowCenter, ← parameter_range]
  constructor
  · rintro ⟨⟨s,t⟩,h⟩
    exact ⟨s.toAdd,t.toAdd,(parameter_apply (s,t)).symm.trans h⟩
  · rintro ⟨s,t,rfl⟩
    exact ⟨(Multiplicative.ofAdd s,Multiplicative.ofAdd t),parameter_apply (Multiplicative.ofAdd s,Multiplicative.ofAdd t)⟩

lemma central_matrix (s t : F) :
    (rootElement 0 s * rootElement 4 t : Sp F).val =
      fromBlocks 1 !![s,t;t,0] 0 1 := by
  rw [← theta_val, theta, element_matrix]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

lemma graphAut_central (s t : F) :
    graphAut (rootElement 0 s * rootElement 4 t) =
      rootElement 0 (t^2) * rootElement 4 s := by
  rw [map_mul, graphAut_apply, graphAut_apply, graphEnd_root, graphEnd_root]
  change rootElement 4 s * rootElement 0 (t^2) = _
  have h := congrArg Subtype.val (theta_add (0:F) s (t^2) 0)
  simpa [theta_val, RootSubgroup.element_zero] using h

lemma central_fixed_iff (s t : F) (v : Space F) :
    graphPair (rootElement 0 s * rootElement 4 t) v = v ↔
      (s * v.1 (.inr 0) + t * v.1 (.inr 1) = 0 ∧ t * v.1 (.inr 0) = 0) ∧
      (t^2 * v.2 (.inr 0) + s * v.2 (.inr 1) = 0 ∧ s * v.2 (.inr 0) = 0) := by
  change (symplecticNatural 2 _ v.1, symplecticNatural 2 (graphAut _) v.2) = v ↔ _
  rw [graphAut_central]
  simp only [symplecticNatural_apply,central_matrix]
  simp [Prod.ext_iff, funext_iff, Sum.forall, Fin.forall_fin_two,
    Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks, one_apply, add_assoc]

lemma central_mixed_fixed_iff {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) (v : Space F) :
    graphPair (rootElement 0 s * rootElement 4 t) v = v ↔
      v.1 ∈ plane F ∧ v.2 ∈ plane F := by
  rw [central_fixed_iff]
  simp only [mem_plane, Fin.forall_fin_two]
  constructor
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    have hc := (mul_eq_zero.mp h2).resolve_left ht
    have hd := (mul_eq_zero.mp h4).resolve_left hs
    simp only [hc,hd,mul_zero,zero_add] at h1 h3
    exact ⟨⟨hc,(mul_eq_zero.mp h1).resolve_left ht⟩,
      ⟨hd,(mul_eq_zero.mp h3).resolve_left hs⟩⟩
  · rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    simp [h1,h2,h3,h4]

lemma sylowCenter_fixedSpace : fixedSpace (graphPair (F := F)) sylowCenter =
    ((plane F).prod (plane F)).restrictScalars (ZMod 2) := by
  ext v
  constructor
  · intro hv
    exact (central_mixed_fixed_iff one_ne_zero one_ne_zero v).mp
      (hv ⟨_, (mem_sylowCenter_iff _).mpr ⟨1,1,rfl⟩⟩)
  · intro hv g
    change v.1 ∈ plane F ∧ v.2 ∈ plane F at hv
    obtain ⟨s,t,h⟩ := (mem_sylowCenter_iff g.val).mp g.property
    change graphPair g.val v = v
    rw [← h,central_fixed_iff]
    simp [hv.1 0,hv.1 1,hv.2 0,hv.2 1]

lemma finrank_planePair {n : ℕ} (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) (((plane F).prod (plane F)).restrictScalars (ZMod 2)) = 4*n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F, coefficient_finrank hF]
  rw [(((plane F).prod (plane F)).restrictScalarsEquiv (ZMod 2)).finrank_eq]
  have he : ((plane F).prod (plane F)) ≃ₗ[F] (plane F × plane F) := {
    toFun v := (⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
    invFun v := ⟨(v.1.val,v.2.val),⟨v.1.property,v.2.property⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  rw [he.finrank_eq, Module.finrank_prod, finrank_plane]
  omega

lemma sylowCenter_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n) :
    fixedCodim (graphPair (F := F)) sylowCenter = 4*n := by
  have h := fixedCodim_add_finrank (graphPair (F := F)) sylowCenter
  rw [sylowCenter_fixedSpace, finrank_planePair hF, finrank_space hF] at h
  omega

lemma central_mixed_fixedSpace {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    fixedSpace (graphPair (F := F)) (Subgroup.zpowers (rootElement 0 s * rootElement 4 t)) =
      ((plane F).prod (plane F)).restrictScalars (ZMod 2) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  exact central_mixed_fixed_iff hs ht v

lemma central_mixed_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    fixedCodim (graphPair (F := F)) (Subgroup.zpowers (rootElement 0 s * rootElement 4 t)) = 4*n := by
  unfold fixedCodim
  rw [central_mixed_fixedSpace hs ht, ← sylowCenter_fixedSpace]
  exact sylowCenter_fixedCodim hF

lemma card_sylowCenter : Nat.card (sylowCenter (F := F)) = Nat.card F^2 := by
  have he := (Subgroup.center (unipotent (F := F))).equivMapOfInjective
    (unipotent (F := F)).subtype Subtype.val_injective
  rw [sylowCenter, ← Nat.card_congr he.toEquiv, ← Nat.card_congr (centerEquiv (F := F)).toEquiv]
  rw [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), pow_two]

lemma rank_sylowCenter {n : ℕ} (hF : Nat.card F = 2^n) :
    rank (sylowCenter (F := F)) = 2*n := by
  rw [Representation.BinaryOffender.rank,card_sylowCenter,hF,← pow_mul,Nat.log_pow (by decide : 1 < 2)]
  omega

lemma sylowCenter_elementary : IsElementaryAbelian 2 (sylowCenter (F := F)) := by
  let _ := center_elementary (F := F)
  exact IsElementaryAbelian.map_subtype

lemma root_zero_le_sylowCenter : RootSubgroup.group (F := F) 0 ≤ sylowCenter := by
  intro g hg
  obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff 0 g).mp hg
  exact (mem_sylowCenter_iff _).mpr ⟨s,0,by simp [RootSubgroup.element_zero]⟩

lemma root_four_le_sylowCenter : RootSubgroup.group (F := F) 4 ≤ sylowCenter := by
  intro g hg
  obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 4 g).mp hg
  exact (mem_sylowCenter_iff _).mpr ⟨0,t,by simp [RootSubgroup.element_zero]⟩

lemma exists_mixed_of_central_not_root {B : Subgroup (Sp F)}
    (hB : B ≤ sylowCenter) (h0 : ¬ B ≤ RootSubgroup.group 0)
    (h4 : ¬ B ≤ RootSubgroup.group 4) :
    ∃ s t : F, s ≠ 0 ∧ t ≠ 0 ∧ rootElement 0 s * rootElement 4 t ∈ B := by
  by_contra h
  suffices hu : (B : Set (Sp F)) ⊆
      (RootSubgroup.group (F := F) 0 : Set (Sp F)) ∪ (RootSubgroup.group (F := F) 4 : Set (Sp F)) by
    exact ((SubgroupClass.subset_union (H := B) (K := RootSubgroup.group 0)
      (L := RootSubgroup.group 4)).mp hu).elim h0 h4
  intro g hg
  obtain ⟨s,t,rfl⟩ := (mem_sylowCenter_iff g).mp (hB hg)
  by_cases hs : s = 0
  · right
    apply (RootSubgroup.mem_group_iff _ _).mpr
    exact ⟨t,by simp [hs,RootSubgroup.element_zero]⟩
  · by_cases ht : t = 0
    · left
      apply (RootSubgroup.mem_group_iff _ _).mpr
      exact ⟨s,by simp [ht,RootSubgroup.element_zero]⟩
    · exact (h ⟨s,t,hs,ht,hg⟩).elim

lemma central_subgroup_fixedSpace {B : Subgroup (Sp F)}
    (hB : B ≤ sylowCenter) (h0 : ¬ B ≤ RootSubgroup.group 0)
    (h4 : ¬ B ≤ RootSubgroup.group 4) :
    fixedSpace (graphPair (F := F)) B =
      ((plane F).prod (plane F)).restrictScalars (ZMod 2) := by
  obtain ⟨s,t,hs,ht,hst⟩ := exists_mixed_of_central_not_root hB h0 h4
  ext v
  constructor
  · intro hv
    exact (central_mixed_fixed_iff hs ht v).mp (hv ⟨_,hst⟩)
  · intro hv g
    have hz : v ∈ fixedSpace (graphPair (F := F)) sylowCenter := by
      rw [sylowCenter_fixedSpace]
      exact hv
    exact hz ⟨g.val,hB g.property⟩

lemma central_subgroup_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ sylowCenter)
    (h0 : ¬ B ≤ RootSubgroup.group 0) (h4 : ¬ B ≤ RootSubgroup.group 4) :
    fixedCodim (graphPair (F := F)) B = 4*n := by
  unfold fixedCodim
  rw [central_subgroup_fixedSpace hB h0 h4, ← sylowCenter_fixedSpace]
  exact sylowCenter_fixedCodim hF

lemma rank_le_of_le_root {n : ℕ} (hF : Nat.card F = 2^n)
    (r : Fin 8) {B : Subgroup (Sp F)} (hB : B ≤ RootSubgroup.group r) :
    Representation.BinaryOffender.rank B ≤ n := by
  have h := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hB)
  rw [RootSubgroup.card, hF, Nat.log_pow (by decide : 1 < 2)] at h
  exact h

lemma rank_le_of_le_sylowCenter {n : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ sylowCenter) :
    Representation.BinaryOffender.rank B ≤ 2*n := by
  have h := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hB)
  change Representation.BinaryOffender.rank B ≤ Representation.BinaryOffender.rank sylowCenter at h
  rwa [rank_sylowCenter hF] at h

/-- Every nontrivial subgroup of the Sylow center has codimension at least 3n. -/
lemma central_subgroup_fixedCodim_lower {n : ℕ} (hF : Nat.card F = 2^n)
    {B : Subgroup (Sp F)} (hB : B ≤ sylowCenter) (hne : B ≠ ⊥) :
    3*n ≤ fixedCodim (graphPair (F := F)) B := by
  by_cases h0 : B ≤ RootSubgroup.group 0
  · exact (root_subgroup_fixedCodim hF 0 B h0 hne).ge
  by_cases h4 : B ≤ RootSubgroup.group 4
  · exact (root_subgroup_fixedCodim hF 4 B h4 hne).ge
  rw [central_subgroup_fixedCodim hF hB h0 h4]
  omega

/-- The strict F−1 inequality, including the binary central four-group. -/
lemma central_subgroup_not_offender {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {B : Subgroup (Sp F)} (hB : B ≤ sylowCenter) (hne : B ≠ ⊥) :
    rank B + 1 < fixedCodim (graphPair (F := F)) B := by
  by_cases h0 : B ≤ RootSubgroup.group 0
  · rw [root_subgroup_fixedCodim hF 0 B h0 hne]
    have := rank_le_of_le_root hF 0 h0
    omega
  by_cases h4 : B ≤ RootSubgroup.group 4
  · rw [root_subgroup_fixedCodim hF 4 B h4 hne]
    have := rank_le_of_le_root hF 4 h4
    omega
  rw [central_subgroup_fixedCodim hF hB h0 h4]
  have := rank_le_of_le_sylowCenter hF hB
  omega
end SymplecticConjugatePair
