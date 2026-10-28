module
public import Theory.SpecificGroups.SymplecticFour.SelectedGeneration
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeAbelian

/-!
# A single long root generates with a point mover

The standard point radical contains roots 0, 4 and 6. The opposite long
root supplies the first Weyl reflection, which turns root 6 into root 5;
the four root axes generate the whole symplectic group. This gives one
conjugator relative to any prescribed long-root marking.

A large abelian two-actor in Sp4(4) lies in an elementary Sylow wing. A
natural moving index greater than sixteen excludes the plane wing, so it
is exactly the point radical of order sixty-four. The original-kernel
application is SourceComparison.OriginalAbelianMoverGeneration. This is
the abelian inner-image subcase of MS93 (5.5)(c), printed pp.915--917;
no abelian or inner-image assertion for every original mover is made.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SelectedGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def firstSwap : Sp F := rootElement 0 1 * rootElement 1 1 * rootElement 0 1

omit [Finite F] in
private theorem firstSwap_mixed (t : F) :
    firstSwap * rootElement 6 t * firstSwap⁻¹ = rootElement 5 t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) * rootMatrix 6 t =
    rootMatrix 5 t * (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem point_root_mem (r : Fin 8) (hr : r=0 ∨ r=4 ∨ r=6) (t : F) :
    rootElement r t ∈ (wing false).map (unipotent (F := F)).subtype := by
  rcases hr with rfl | rfl | rfl
  · refine ⟨element 0 t 0 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]
  · refine ⟨element 0 0 t 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]
  · refine ⟨element t 0 0 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]

/-- The entire point radical and one opposite long root generate Sp4. -/
theorem point_wing_and_long_root :
    (wing false).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1 = ⊤ := by
  let H := (wing false).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1
  have hp (r : Fin 8) (hr : r=0 ∨ r=4 ∨ r=6) (t : F) : rootElement r t ∈ H :=
    (show (wing false).map (unipotent (F := F)).subtype ≤ H from le_sup_left)
      (point_root_mem r hr t)
  have h1 (t : F) : rootElement 1 t ∈ H :=
    (show RootSubgroup.group 1 ≤ H from le_sup_right) (subset_closure ⟨t,rfl⟩)
  have hs : firstSwap (F := F) ∈ H :=
    H.mul_mem (H.mul_mem (hp 0 (by simp) 1) (h1 1)) (hp 0 (by simp) 1)
  apply TwoConjugate.eq_top_of_four_axes H (hp 0 (by simp)) h1 (hp 4 (by simp))
  intro t
  rw [←firstSwap_mixed]
  exact H.mul_mem (H.mul_mem hs (hp 6 (by simp) t)) (H.inv_mem hs)

omit [CharP F 2] [Finite F] in
private theorem point_map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- Position a point radical relative to a prescribed full long root. -/
theorem exists_point_root_generator
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing false).map (unipotent (F := F)).subtype)
    (hA : ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g : Sp F, E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  obtain ⟨k,hk⟩ := hE
  obtain ⟨h,hh⟩ := hA
  let o := TwoConjugate.opposition (F := F)
  let c := o*h
  have h01 : (RootSubgroup.group (F := F) 0).map (MulAut.conj o).toMonoidHom =
      RootSubgroup.group 1 := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
      change o * rootElement 0 t * o⁻¹ ∈ _
      rw [(TwoConjugate.opposition_central_axes t).1]
      exact subset_closure ⟨t,rfl⟩
    · intro hy
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
      exact ⟨rootElement 0 t,subset_closure ⟨t,rfl⟩,(TwoConjugate.opposition_central_axes t).1⟩
  have hAc : A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 := by
    rw [←point_map_conj_mul,hh,h01]
  refine ⟨c⁻¹*k,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [Subgroup.map_sup,point_map_conj_mul,hAc,
    show c*(c⁻¹*k)=k by group,hk,point_wing_and_long_root]
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]

/-- A large abelian two-actor with cross moving index above sixteen is the
point radical, with its order and the same natural marking retained. -/
theorem conjugate_point_of_large_abelian
    [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (E : Subgroup (Sp F)) [IsMulCommutative E] (hE : IsPGroup 2 E)
    (hc : 64 ≤ Nat.card E)
    (hm : 16 < Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E)) :
    Nat.card E = 64 ∧ ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing false).map (unipotent (F := F)).subtype := by
  obtain ⟨P,hP⟩ := hE.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) P
    (unipotentSylow (n := 2) hF (by decide))
  have hkP : (P : Subgroup (Sp F)).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let E' := E.map (MulAut.conj k).toMonoidHom
  have hEU : E' ≤ unipotent := hkP ▸ map_mono hP
  let A := E'.subgroupOf unipotent
  have hAm : A.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hEU
  have hAc : Nat.card A = Nat.card E := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hAm,
      card_map_of_injective (MulAut.conj k).injective]
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hdim := BinaryOffender.fixedCodim_map_equivariant σ σ (MulAut.conj k).toMonoidHom
    (SymplecticConjugatePair.Ambient.linearAction σ k)
    (fun g v => by
      change σ k (σ g v) = σ (k*g*k⁻¹) (σ k v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]) E
  have hdim' := BinaryOffender.fixedCodim_map_equivariant
    (σ.comp (unipotent (F := F)).subtype) σ (unipotent (F := F)).subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) A
  rw [hAm] at hdim'
  have hbound : 16 < SmallMovers.movingIndex A := by
    rw [←SmallMovers.binary_movingIndex]
    change 16 < 2 ^ BinaryOffender.fixedCodim (σ.comp (unipotent (F := F)).subtype) A
    rw [hdim',←hdim]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hm
    exact hm
  let : IsMulCommutative A := inferInstance
  have hlarge : 2 * Nat.card F ^ 2 < Nat.card A := by rw [hF,hAc]; omega
  have hAw : A = wing false := by
    rcases SmallMovers.Degree.abelian_le_wing_of_large A hlarge with hw | hw
    · have hi := SmallMovers.movingIndex_le_field_sq_of_le_wing A hw
      rw [hF] at hi
      omega
    · exact eq_of_le_of_card_ge hw (by rw [card_wing,hF,hAc]; exact hc)
  have hec : Nat.card E=64 := by rw [←hAc,hAw,card_wing,hF]; norm_num
  exact ⟨hec,k,hAm.symm.trans (congrArg (Subgroup.map (unipotent (F := F)).subtype) hAw)⟩
end Theory.SpecificGroups.SymplecticFour.SelectedGeneration
