module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.MatrixIdentification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# Standard fixed-Sylow geometry for the symplectic swapping branch

The marked Suzuki root matrices are upper unipotent in the native symplectic
coordinates. Their inverse images therefore give a Sylow subgroup of the
fixed group inside the standard symplectic unipotent subgroup. Maximality
identifies this inclusion with the full intersection.

The block-swap Weyl matrix is graph-field fixed and exchanges each positive
root with its opposite. Thus the fixed group and the unipotent subgroup
generate the symplectic group. A conjugator belonging to the fixed group
transports both calculations to any supplied aligned Sylow subgroup.

Source: the swapping branch of Aschbacher--Smith E.1.14(1), printed p.214;
16.1.4(7), printed p.1171; the Suzuki root matrices of Huppert--Blackburn III,
XI.3.1--3.3. Alignment of an arbitrary invariant Sylow is a separate premise.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Standard
open DiagramAutomorphisms GraphFieldFixedResidual GraphFieldFixedResidual.MatrixIdentification
open BenderSuzuki.MatrixGroups
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The Weyl matrix exchanging the two halves of the native symplectic basis. -/
def opposition : Sp F :=
  ⟨Matrix.fromBlocks 0 1 1 0, by
    rw [SymplecticGroup.mem_iff]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.J, Matrix.fromBlocks, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq]⟩

/-- The opposition matrix is fixed by every graph-field representative. -/
theorem opposition_fixed (m : ℕ) : opposition (F := F) ∈ (graphFieldAut m).fixedSubgroup := by
  rw [mem_fixed_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [opposition, ExceptionalGraph.graphMatrix, ExceptionalGraph.minor,
      ExceptionalGraph.first, ExceptionalGraph.second, Matrix.fromBlocks]

omit [Finite F] in
private theorem opposition_root (r : Fin 8) (x : F) :
    opposition * rootElement r x * opposition =
      rootElement (![1, 0, 3, 2, 5, 4, 7, 6] r) x := by
  apply Subtype.ext
  change Matrix.fromBlocks 0 1 1 0 * rootMatrix r x * Matrix.fromBlocks 0 1 1 0 = _
  fin_cases r <;>
    simp [rootElement, rootMatrix, Matrix.fromBlocks_multiply, sub_eq_add_neg]
  all_goals constructor <;> ext i j <;> simp [CharTwo.neg_eq]

/-- The fixed Weyl matrix and all positive roots generate the full group. -/
theorem fixed_sup_unipotent (m : ℕ) :
    (graphFieldAut (F := F) m).fixedSubgroup ⊔ unipotent = ⊤ := by
  apply eq_top_of_rootElement_mem
  intro r x
  have positive (s : Fin 8) (hs : s = 0 ∨ s = 2 ∨ s = 4 ∨ s = 6) :
      rootElement s x ∈ (graphFieldAut (F := F) m).fixedSubgroup ⊔ unipotent :=
    mem_sup_right (positive_root_mem_unipotent s x hs)
  have negative (s : Fin 8) (hs : s = 0 ∨ s = 2 ∨ s = 4 ∨ s = 6) :
      rootElement (![1, 0, 3, 2, 5, 4, 7, 6] s) x ∈
        (graphFieldAut (F := F) m).fixedSubgroup ⊔ unipotent := by
    rw [← opposition_root]
    exact mul_mem (mul_mem (mem_sup_left (opposition_fixed m)) (positive s hs))
      (mem_sup_left (opposition_fixed m))
  fin_cases r
  · exact positive 0 (by simp)
  · exact negative 0 (by simp)
  · exact positive 2 (by simp)
  · exact negative 2 (by simp)
  · exact positive 4 (by simp)
  · exact negative 4 (by simp)
  · exact positive 6 (by simp)
  · exact negative 6 (by simp)

private theorem root_preimage_mem_unipotent (m : ℕ)
    (hF : Nat.card F = 2 ^ (2 * m + 1))
    (g : (graphFieldAut (F := F) m).fixedSubgroup)
    (hg : fixedEquivOfBinaryModel m hF (fixedSuzukiEquiv m) g ∈ SuzukiRootSubgroup m) :
    g.val ∈ unipotent := by
  obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m _).mp hg
  have he := (fixedEquivOfBinaryModel_matrix m hF (fixedSuzukiEquiv m)
    (fixedSuzukiEquiv_matrix m) g).symm.trans (congrArg Units.val hab)
  let c := coefficientFieldEquiv m hF
  have entry (i j : Fin 2 ⊕ Fin 2) :
      c (g.val.val i j) = SuzukiRootMatrix m a b (suzukiIndex i) (suzukiIndex j) := by
    have hh := congrArg (fun M => M (suzukiIndex i) (suzukiIndex j)) he
    simp only [matrixCoordinates, Matrix.submatrix_apply, Matrix.map_apply,
      Equiv.symm_apply_apply] at hh
    exact hh
  have zero (i j : Fin 2 ⊕ Fin 2)
      (h : SuzukiRootMatrix m a b (suzukiIndex i) (suzukiIndex j) = 0) :
      g.val.val i j = 0 := c.injective ((entry i j).trans (h.trans c.map_zero.symm))
  have one (i j : Fin 2 ⊕ Fin 2)
      (h : SuzukiRootMatrix m a b (suzukiIndex i) (suzukiIndex j) = 1) :
      g.val.val i j = 1 := c.injective ((entry i j).trans (h.trans c.map_one.symm))
  rw [mem_unipotent_iff, mem_borel_iff]
  refine ⟨⟨zero _ _ ?_, fun i j => zero _ _ ?_⟩, one _ _ ?_, one _ _ ?_⟩
  all_goals first | (fin_cases i <;> fin_cases j) | skip
  all_goals simp [SuzukiRootMatrix, suzukiIndex]

/-- The intersection with the standard unipotent subgroup is Sylow in the
actual graph-field fixed group. -/
theorem standard_fixed_sylow (m : ℕ) (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    ∃ R : Sylow 2 (graphFieldAut (F := F) m).fixedSubgroup,
      (R : Subgroup (graphFieldAut (F := F) m).fixedSubgroup) =
        unipotent.subgroupOf (graphFieldAut m).fixedSubgroup := by
  let e := fixedEquivOfBinaryModel m hF (fixedSuzukiEquiv m)
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  let R := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hR : (R : Subgroup (graphFieldAut (F := F) m).fixedSubgroup) ≤
      unipotent.subgroupOf (graphFieldAut m).fixedSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    apply root_preimage_mem_unipotent m hF
    change e (e.symm x) ∈ SuzukiRootSubgroup m
    rw [e.apply_symm_apply]
    exact hP ▸ hx
  have hp : IsPGroup 2 (unipotent.subgroupOf (graphFieldAut (F := F) m).fixedSubgroup) :=
    (isPGroup_unipotent hF).comap_subtype
  exact ⟨R, (R.is_maximal' hp hR).symm⟩

/-- A fixed conjugator transports both standard conclusions without replacing
any supplied Sylow subgroup. -/
theorem geometry_at_aligned_sylow (m : ℕ) (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (S : Sylow 2 (Sp F))
    (k : Sp F) (hk : k ∈ (graphFieldAut m).fixedSubgroup)
    (hS : unipotent.map (MulAut.conj k).toMonoidHom = (S : Subgroup (Sp F))) :
    (∃ R : Sylow 2 (graphFieldAut (F := F) m).fixedSubgroup,
      (R : Subgroup (graphFieldAut (F := F) m).fixedSubgroup) =
        (S : Subgroup (Sp F)).subgroupOf (graphFieldAut m).fixedSubgroup) ∧
      (graphFieldAut (F := F) m).fixedSubgroup ⊔ (S : Subgroup (Sp F)) = ⊤ := by
  let C := (graphFieldAut (F := F) m).fixedSubgroup
  let c : C := ⟨k, hk⟩
  obtain ⟨R, hR⟩ := standard_fixed_sylow m hm hF
  let R' := R.mapSurjective (f := (MulAut.conj c).toMonoidHom)
    (MulAut.conj c).surjective
  have hle : (R' : Subgroup C) ≤ (S : Subgroup (Sp F)).subgroupOf C := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hR] at hx
    exact hS ▸ (mem_map_of_mem (MulAut.conj k).toMonoidHom hx)
  refine ⟨⟨R', (R'.is_maximal' S.isPGroup'.comap_subtype hle).symm⟩, ?_⟩
  apply top_unique
  rw [← map_top_of_surjective (MulAut.conj k).toMonoidHom (MulAut.conj k).surjective,
    ← fixed_sup_unipotent m, Subgroup.map_sup, hS]
  apply sup_le _ le_sup_right
  apply le_trans _ le_sup_left
  rintro _ ⟨x, hx, rfl⟩
  have hk' := (MulAut.mem_fixedSubgroup _ _).mp hk
  have hx' := (MulAut.mem_fixedSubgroup _ _).mp (show x ∈ (graphFieldAut m).fixedSubgroup from hx)
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  change graphFieldAut m (k * x * k⁻¹) = k * x * k⁻¹
  rw [map_mul, map_mul, map_inv, hk', hx']

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers.CentralizerGeometry.Standard
