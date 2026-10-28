module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Theory.Quasithin
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Full symplectic parabolics are two-local and have self-centralizing two-cores

The radicals' common fixed vectors are exactly the standard point and plane.
Their normalizers therefore preserve those subspaces. The established core
identities give the reverse inclusions, identifying both full normalizers.

Commutation with explicit radical matrices forces the relevant torus entries
to square to one. In characteristic two they are one, so a centralizing matrix
lies in the determinant kernel. The natural-extension centralizer theorem
then puts it in the radical. Transport through the actual subgroup embeddings
gives self-centralizing intrinsic two-cores for the full parabolics.

All normality used here is inside the corresponding parabolic. This calculation
does not assert that arbitrary two-local subgroups lie in conjugate parabolics,
or establish their odd-prime ranks.

Source: Aschbacher–Smith, F.1.12(I)(2), printed pp.262–264. These explicit
matrix calculations supply part of the PSp₄(2^f) converse in Theorem 0.1.2(1),
printed p.4 (Theorem 0.1.1(1) on printed p.482).
-/

public noncomputable section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

/-- The point radical embedded in the original matrix group. -/
abbrev pointRadicalAmbient : Subgroup (Sp F) := pointRadical.map pointLocal.subtype
/-- The plane radical embedded in the original matrix group. -/
abbrev planeRadicalAmbient : Subgroup (Sp F) := Plane.radical.map planeLocal.subtype

private theorem point_element_mem (u v z : F) :
    (pointRadicalElement u v z).val ∈ pointRadicalAmbient :=
  Subgroup.mem_map_of_mem _ (pointRadicalElement_mem u v z)

omit [CharP F 2] in
private theorem plane_shear_mem (B : Plane.symmetricMatrices F) :
    (Plane.shear B).val ∈ planeRadicalAmbient :=
  Subgroup.mem_map_of_mem planeLocal.subtype
    (show Plane.shear B ∈ Plane.radical from Plane.quotientMap_shear B)

private def diagShear (i : Fin 2) : Plane.symmetricMatrices F :=
  ⟨Matrix.diagonal (Pi.single i 1), Matrix.isSymm_diagonal _⟩

private theorem point_fixed (x : Vector F) :
    (∀ q ∈ pointRadicalAmbient (F := F), q • x = x) ↔ x ∈ point F := by
  constructor
  · intro h
    have h₀ := congrFun (h _ (point_element_mem 0 0 (1 : F))) (.inl 0)
    have h₁ := congrFun (h _ (point_element_mem 1 0 (0 : F))) (.inl 0)
    have h₂ := congrFun (h _ (point_element_mem 0 1 (0 : F))) (.inl 0)
    simp [pointRadicalElement, pointRadicalMatrix, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two] at h₀ h₁ h₂
    exact (mem_point_iff x).mpr ⟨h₂, by intro i; fin_cases i <;> assumption⟩
  · intro hx q hq
    obtain ⟨q, _, rfl⟩ := hq
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change toLinear q.val (a • e 0) = a • e 0
    rw [map_smul]
    exact congrArg (a • ·) ((mem_pointLocal_iff_fixed q.val).mp q.property)

omit [CharP F 2] in
private theorem plane_fixed (x : Vector F) :
    (∀ q ∈ planeRadicalAmbient (F := F), q • x = x) ↔ x ∈ plane F := by
  constructor
  · intro h i
    have hi := congrFun (h _ (plane_shear_mem (diagShear i))) (.inl i)
    fin_cases i <;>
      simpa [smul_eq_mulVec, Plane.shear, Plane.shearSp, diagShear, mulVec, dotProduct,
        Fintype.sum_sum_type, Fin.sum_univ_two, diagonal, Pi.single_apply] using hi
  · intro hx q hq
    have hx' : ∀ i, x (.inr i) = 0 := hx
    obtain ⟨q, hq, rfl⟩ := hq
    have hm := Plane.radical_matrix (⟨q, hq⟩ : Plane.radical)
    change q.val.val *ᵥ x = x
    rw [hm]
    funext i
    cases i with
    | inl i => simp [mulVec, dotProduct, Fintype.sum_sum_type, one_apply, hx']
    | inr i => simp [mulVec, dotProduct, Fintype.sum_sum_type, one_apply, hx']

omit [CharP F 2] in
private theorem normalizer_le_fixed_stabilizer (Q : Subgroup (Sp F))
    (W : Submodule F (Vector F))
    (hfix : ∀ x, (∀ q ∈ Q, q • x = x) ↔ x ∈ W) :
    Subgroup.normalizer (Q : Set (Sp F)) ≤ stabilizer W := by
  intro g hg
  rw [mem_stabilizer_iff]
  intro x hx
  apply (hfix _).mp
  intro q hq
  have hq' : g⁻¹ * q * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hg q).mp hq
  have h := congrArg (g • ·) ((hfix x).mpr hx _ hq')
  simpa only [mul_smul, smul_inv_smul] using h

private theorem point_normalizer_le :
    Subgroup.normalizer (pointRadicalAmbient (F := F) : Set (Sp F)) ≤ pointParabolic :=
  normalizer_le_fixed_stabilizer _ _ point_fixed

omit [CharP F 2] in
private theorem plane_normalizer_le :
    Subgroup.normalizer (planeRadicalAmbient (F := F) : Set (Sp F)) ≤ planeParabolic :=
  normalizer_le_fixed_stabilizer _ _ plane_fixed

omit [CharP F 2] in
private theorem comm_entry {Q : Subgroup (Sp F)} {g : Sp F}
    (hg : g ∈ Subgroup.centralizer (Q : Set (Sp F))) {q : Sp F} (hq : q ∈ Q)
    (i j : Fin 2 ⊕ Fin 2) : (q.val * g.val) i j = (g.val * q.val) i j := by
  exact congrArg (fun a : Sp F => a.val i j)
    (Subgroup.mem_centralizer_iff.mp hg q hq)

private theorem point_centralizer_le_local :
    Subgroup.centralizer (pointRadicalAmbient (F := F) : Set (Sp F)) ≤ pointLocal := by
  intro g hg
  have hp := point_normalizer_le (Subgroup.centralizer_le_normalizer _ hg)
  have hc := comm_entry hg (point_element_mem 0 0 (1 : F)) (.inl 0) (.inr 0)
  simp [pointRadicalElement, pointRadicalMatrix, mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two] at hc
  have hd : g.val (.inr 0) (.inr 0) = g.val (.inl 0) (.inl 0) := by
    linear_combination hc
  have hs := preserves_form g (e (F := F) 0) (Pi.single (.inr 0) 1)
  have hcol := (mem_pointParabolic_iff g).mp hp
  have hsq : g.val (.inl 0) (.inl 0) ^ 2 = 1 := by
    simpa [form_apply, smul_eq_mulVec, e, mulVec_single, Fin.sum_univ_two,
      hcol.1, hcol.2, hd, pow_two] using hs
  exact (mem_pointLocal_iff g).mpr ⟨hp, CharTwo.sq_injective (by simpa using hsq)⟩

private theorem plane_centralizer_le_local :
    Subgroup.centralizer (planeRadicalAmbient (F := F) : Set (Sp F)) ≤ planeLocal := by
  intro g hg
  have hp := plane_normalizer_le (Subgroup.centralizer_le_normalizer _ hg)
  have hc (k : Fin 2) (i j : Fin 2 ⊕ Fin 2) :=
    comm_entry hg (plane_shear_mem (diagShear k)) i j
  have h00 := hc 0 (.inl 0) (.inr 0)
  have h11 := hc 1 (.inl 1) (.inr 1)
  have h01 := hc 1 (.inl 0) (.inr 1)
  have h10 := hc 0 (.inl 1) (.inr 0)
  simp [Plane.shear, Plane.shearSp, diagShear, mul_apply, diagonal,
    Pi.single_apply, Fintype.sum_sum_type, Fin.sum_univ_two] at h00 h11 h01 h10
  have hd0 : g.val (.inr 0) (.inr 0) = g.val (.inl 0) (.inl 0) := by
    linear_combination h00
  have hd1 : g.val (.inr 1) (.inr 1) = g.val (.inl 1) (.inl 1) := by
    linear_combination h11
  have hcol := (mem_planeParabolic_iff g).mp hp
  have hs0 := preserves_form g (e (F := F) 0) (Pi.single (.inr 0) 1)
  have hs1 := preserves_form g (e (F := F) 1) (Pi.single (.inr 1) 1)
  have hsq0 : g.val (.inl 0) (.inl 0) ^ 2 = 1 := by
    simpa [form_apply, smul_eq_mulVec, e, mulVec_single, Fin.sum_univ_two,
      hcol, h10, hd0, pow_two] using hs0
  have hsq1 : g.val (.inl 1) (.inl 1) ^ 2 = 1 := by
    simpa [form_apply, smul_eq_mulVec, e, mulVec_single, Fin.sum_univ_two,
      hcol, h01, hd1, pow_two] using hs1
  have he0 : g.val (.inl 0) (.inl 0) = 1 := CharTwo.sq_injective (by simpa using hsq0)
  have he1 : g.val (.inl 1) (.inl 1) = 1 := CharTwo.sq_injective (by simpa using hsq1)
  exact (mem_planeLocal_iff g).mpr ⟨hp, by simp [he0, he1, h01]⟩


private theorem centralizer_map_le_of_local {G : Type*} [Group G]
    (L : Subgroup G) (Q : Subgroup L)
    (hL : Subgroup.centralizer (Q.map L.subtype : Set G) ≤ L)
    (hQ : Subgroup.centralizer (Q : Set L) ≤ Q) :
    Subgroup.centralizer (Q.map L.subtype : Set G) ≤ Q.map L.subtype := by
  intro g hg
  have hgl := hL hg
  have hcg : (⟨g, hgl⟩ : L) ∈ Subgroup.centralizer (Q : Set L) := by
    intro q hq
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hg q (Subgroup.mem_map_of_mem _ hq)
  exact Subgroup.mem_map_of_mem L.subtype (hQ hcg)

variable [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)

include hF hf in
theorem pointRadicalAmbient_selfCentralizing :
    Subgroup.centralizer (pointRadicalAmbient (F := F) : Set (Sp F)) ≤
      pointRadicalAmbient :=
  centralizer_map_le_of_local _ _ point_centralizer_le_local
    ((pointNaturalExtension hF hf).centralizer_eq.le)

include hF hf in
theorem planeRadicalAmbient_selfCentralizing :
    Subgroup.centralizer (planeRadicalAmbient (F := F) : Set (Sp F)) ≤
      planeRadicalAmbient :=
  centralizer_map_le_of_local _ _ plane_centralizer_le_local
    ((planeNaturalExtension hF hf).centralizer_eq.le)

private theorem normalizer_mapped_core_le {G : Type*} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer ((pCore 2 P).map P.subtype : Set G) := by
  intro g hg
  apply Subgroup.le_normalizer_map P.subtype
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [Subgroup.normalizer_eq_top]
  trivial

include hF hf in
theorem pointRadicalAmbient_normalizer :
    Subgroup.normalizer (pointRadicalAmbient (F := F) : Set (Sp F)) = pointParabolic := by
  apply le_antisymm point_normalizer_le
  rw [show pointRadicalAmbient (F := F) =
    (pCore 2 (pointParabolic (F := F))).map pointParabolic.subtype from
      (pointParabolic_core_map_eq_radical hF hf).symm]
  exact normalizer_mapped_core_le _

include hF hf in
theorem planeRadicalAmbient_normalizer :
    Subgroup.normalizer (planeRadicalAmbient (F := F) : Set (Sp F)) = planeParabolic := by
  apply le_antisymm plane_normalizer_le
  rw [show planeRadicalAmbient (F := F) =
    (pCore 2 (planeParabolic (F := F))).map planeParabolic.subtype from
      (planeParabolic_core_map_eq_radical hF hf).symm]
  exact normalizer_mapped_core_le _

private theorem core_selfCentralizing_of_map {G : Type*} [Group G] (P : Subgroup G)
    (hc : Subgroup.centralizer ((pCore 2 P).map P.subtype : Set G) ≤
      (pCore 2 P).map P.subtype) :
    Subgroup.centralizer (pCore 2 P : Set P) ≤ pCore 2 P := by
  intro g hg
  have hcg : (g : G) ∈ Subgroup.centralizer ((pCore 2 P).map P.subtype : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg y hy)
  obtain ⟨y, hy, he⟩ := hc hcg
  exact (P.subtype_injective he) ▸ hy

include hF hf in
theorem pointParabolic_selfCentralizing_core :
    Subgroup.centralizer (pCore 2 (pointParabolic (F := F)) :
      Set (pointParabolic (F := F))) ≤ pCore 2 (pointParabolic (F := F)) := by
  apply core_selfCentralizing_of_map
  rw [pointParabolic_core_map_eq_radical hF hf]
  exact pointRadicalAmbient_selfCentralizing hF hf

include hF hf in
theorem planeParabolic_selfCentralizing_core :
    Subgroup.centralizer (pCore 2 (planeParabolic (F := F)) :
      Set (planeParabolic (F := F))) ≤ pCore 2 (planeParabolic (F := F)) := by
  apply core_selfCentralizing_of_map
  rw [planeParabolic_core_map_eq_radical hF hf]
  exact planeRadicalAmbient_selfCentralizing hF hf

include hF hf in
theorem pointParabolic_isTwoLocal : IsTwoLocal (pointParabolic (F := F)) := by
  refine ⟨pointRadicalAmbient, ?_, ?_, (pointRadicalAmbient_normalizer hF hf).symm⟩
  · intro h
    have hx := point_element_mem 0 0 (1 : F)
    rw [h, Subgroup.mem_bot] at hx
    have he := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 0)) hx
    simp [pointRadicalElement, pointRadicalMatrix] at he
  · exact (IsElementaryAbelian.isPGroup 2 (pointRadical (F := F))).map _

include hF hf in
theorem planeParabolic_isTwoLocal : IsTwoLocal (planeParabolic (F := F)) := by
  refine ⟨planeRadicalAmbient, ?_, ?_, (planeRadicalAmbient_normalizer hF hf).symm⟩
  · intro h
    have hx := plane_shear_mem (diagShear (F := F) 0)
    rw [h, Subgroup.mem_bot] at hx
    have he := congrArg (fun g : Sp F => g.val (.inl 0) (.inr 0)) hx
    simp [Plane.shear, Plane.shearSp, diagShear, diagonal, Pi.single_apply] at he
  · let := Plane.radical_elementaryAbelian (F := F)
    exact (IsElementaryAbelian.isPGroup 2 (Plane.radical (F := F))).map _

end Theory.SpecificGroups.SymplecticFour
