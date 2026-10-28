module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Classification
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.SymplecticConjugatePair.Ambient.Basic
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# Simultaneous root generators and separated plane fixed spaces in Sp4(4)

An order-64 two-subgroup with natural moving index at most sixteen is the
full plane radical in Sylow coordinates. This radical and two full long
roots generate Sp4. A lower-root shear preserves the second generating
root and makes the fixed planes of the radical and its inverse conjugate
transverse. Conjugation transports both conclusions to the same marked
small mover and full transvection root.

The standard selector also normalizes the opposite plane radical. The
extension SelectedPositioning aligns the original root and plane together
and uses this fact to prove MS93 (5.6)(d), alongside clauses (b,c),
printed pp.917--918, in the full-Sylow reciprocal-root branch. The original residual and tensor
applications are in SourceComparison.OriginalSelectedGeneration and
GenerationTwoSymplecticSelectedGeneration.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SelectedGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
private def swapFirst : Sp F := rootElement 0 1 * rootElement 1 1 * rootElement 0 1
private def swapSecond : Sp F := rootElement 2 1 * rootElement 3 1 * rootElement 2 1
private def swapPairs : Sp F := rootElement 6 1 * rootElement 7 1 * rootElement 6 1
omit [Finite F] in
private theorem opposition_word : swapFirst * swapSecond = TwoConjugate.opposition (F := F) := by
  apply Subtype.ext
  change (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) *
    (rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, TwoConjugate.opposition, CharTwo.add_self_eq_zero]
omit [Finite F] in
private theorem swapPairs_matrix : (swapPairs (F := F)).val =
    fromBlocks !![0,1;1,0] 0 0 !![0,1;1,0] := by
  change rootMatrix 6 1 * rootMatrix 7 1 * rootMatrix 6 1 = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
omit [Finite F] in
private theorem swap_lower (t : F) :
    swapPairs * rootElement 1 t * swapPairs⁻¹ = rootElement 3 t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (swapPairs (F := F)).val * rootMatrix 1 t = rootMatrix 3 t * (swapPairs (F := F)).val
  rw [swapPairs_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks]
private theorem upper_mem (r : Fin 8) (hr : r = 0 ∨ r = 2 ∨ r = 4) (t : F) :
    rootElement r t ∈ (wing true).map (unipotent (F := F)).subtype := by
  rcases hr with rfl | rfl | rfl
  · refine ⟨element 0 t 0 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]
  · refine ⟨element 0 0 0 t,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]
  · refine ⟨element 0 0 t 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
    simp [element,RootSubgroup.element_zero]

private theorem plane_and_two_long_roots :
    ((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
      (RootSubgroup.group 1).map (MulAut.conj (swapPairs (F := F))).toMonoidHom = ⊤ := by
  let H := ((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
      (RootSubgroup.group 1).map (MulAut.conj (swapPairs (F := F))).toMonoidHom
  have hu (r : Fin 8) (hr : r=0 ∨ r=2 ∨ r=4) (t : F) : rootElement r t ∈ H :=
    (show (wing true).map (unipotent (F := F)).subtype ≤ H from le_sup_left.trans le_sup_left)
      (upper_mem r hr t)
  have h1 (t : F) : rootElement 1 t ∈ H :=
    (show RootSubgroup.group 1 ≤ H from le_sup_right.trans le_sup_left) (subset_closure ⟨t,rfl⟩)
  have h3 (t : F) : rootElement 3 t ∈ H := by
    rw [←swap_lower]
    exact (show (RootSubgroup.group 1).map (MulAut.conj (swapPairs (F := F))).toMonoidHom ≤ H from
      le_sup_right) (mem_map_of_mem _ (subset_closure ⟨t,rfl⟩))
  have hop : TwoConjugate.opposition (F := F) ∈ H := by
    rw [←opposition_word]
    exact H.mul_mem (H.mul_mem (H.mul_mem (hu 0 (by simp) 1) (h1 1)) (hu 0 (by simp) 1))
      (H.mul_mem (H.mul_mem (hu 2 (by simp) 1) (h3 1)) (hu 2 (by simp) 1))
  apply TwoConjugate.eq_top_of_four_axes H (hu 0 (by simp)) h1 (hu 4 (by simp))
  intro t
  rw [←(TwoConjugate.opposition_central_axes t).2]
  exact H.mul_mem (H.mul_mem hop (hu 4 (by simp) t)) (H.inv_mem hop)

omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]


private def separatePairs : Sp F := rootElement 5 1 * swapPairs
omit [Finite F] in
private theorem separatePairs_matrix : (separatePairs (F := F)).val =
    fromBlocks !![0,1;1,0] 0 1 !![0,1;1,0] := by
  change rootMatrix 5 1 * (swapPairs (F := F)).val = _
  rw [swapPairs_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks]
omit [Finite F] in
private theorem separate_lower (t : F) :
    separatePairs * rootElement 1 t * separatePairs⁻¹ = rootElement 3 t := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (separatePairs (F := F)).val * rootMatrix 1 t = rootMatrix 3 t * (separatePairs (F := F)).val
  rw [separatePairs_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks]

private theorem plane_fixed_bottom (v : Vector F)
    (hv : ∀ y ∈ (wing true).map (unipotent (F := F)).subtype, y • v = v) :
    v (.inr 0) = 0 ∧ v (.inr 1) = 0 := by
  have h0 := congrFun (hv (rootElement 0 1) (upper_mem 0 (by simp) 1)) (.inl 0)
  have h2 := congrFun (hv (rootElement 2 1) (upper_mem 2 (by simp) 1)) (.inl 1)
  simp [rootElement,rootMatrix,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.single,Matrix.fromBlocks] at h0 h2
  exact ⟨h0,h2⟩

omit [Finite F] [CharP F 2] in
private theorem fixed_conj_inverse (K : Subgroup (Sp F)) (x : Sp F) (v : Vector F)
    (hw : ∀ y ∈ K.map (MulAut.conj x⁻¹).toMonoidHom, y • v = v) :
    ∀ y ∈ K, y • (x • v) = x • v := by
  intro y hy
  have h := hw _ (mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hy)
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] at h
  have h' := congrArg (fun w : Vector F => x • w) h
  simpa only [←mul_smul,mul_assoc,mul_inv_cancel_left] using h'

private theorem plane_pair_fixed_eq_zero (v : Vector F)
    (hv : ∀ y ∈ (wing true).map (unipotent (F := F)).subtype, y • v = v)
    (hw : ∀ y ∈ ((wing true).map (unipotent (F := F)).subtype).map
      (MulAut.conj (separatePairs (F := F))⁻¹).toMonoidHom, y • v = v) : v = 0 := by
  have hbottom := plane_fixed_bottom v hv
  have hx := fixed_conj_inverse _ (separatePairs (F := F)) v hw
  have hother := plane_fixed_bottom ((separatePairs (F := F)) • v) hx
  have hu : (separatePairs (F := F) • v) (.inr 0) = v (.inl 0) ∧
      (separatePairs (F := F) • v) (.inr 1) = v (.inl 1) := by
    simp [smul_eq_mulVec,separatePairs_matrix,Matrix.mulVec,dotProduct,
      Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.fromBlocks,hbottom.1,hbottom.2]
  ext i
  rcases i with i | i <;> fin_cases i
  · exact hu.1.symm.trans hother.1
  · exact hu.2.symm.trans hother.2
  · exact hbottom.1
  · exact hbottom.2
/-- The same three generators have disjoint paired plane fixed spaces. -/
theorem exists_plane_two_root_separated_generators
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hA : ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (∀ v : Vector F,
        (∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y • v = v) →
        (∀ y ∈ (E.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom, y • v = v) → v = 0) := by
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
    rw [←map_conj_mul,hh,h01]
  have hgen : ((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
      (RootSubgroup.group 1).map (MulAut.conj (separatePairs (F := F))).toMonoidHom = ⊤ := by
    have hmaps : (RootSubgroup.group (F := F) 1).map (MulAut.conj separatePairs).toMonoidHom =
        (RootSubgroup.group 1).map (MulAut.conj swapPairs).toMonoidHom := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
        refine ⟨rootElement 1 t,subset_closure ⟨t,rfl⟩,?_⟩
        change swapPairs * rootElement 1 t * swapPairs⁻¹ =
          separatePairs * rootElement 1 t * separatePairs⁻¹
        rw [swap_lower,separate_lower]
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
        refine ⟨rootElement 1 t,subset_closure ⟨t,rfl⟩,?_⟩
        change separatePairs * rootElement 1 t * separatePairs⁻¹ =
          swapPairs * rootElement 1 t * swapPairs⁻¹
        rw [swap_lower,separate_lower]
    rw [hmaps]
    exact plane_and_two_long_roots
  refine ⟨c⁻¹*k,c⁻¹*separatePairs*c,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_conj_mul,map_conj_mul,hAc]
    rw [show c*(c⁻¹*k)=k by group,
      show c*(c⁻¹*separatePairs*c)=separatePairs*c by group,hk,
      ←map_conj_mul,hAc,hgen]
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
  · intro v hv hw
    have hE : (E.map (MulAut.conj (c⁻¹*k)).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        (wing true).map (unipotent (F := F)).subtype := by
      rw [map_conj_mul,show c*(c⁻¹*k)=k by group,hk]
    have hEx : ((E.map (MulAut.conj (c⁻¹*k)).toMonoidHom).map
        (MulAut.conj (c⁻¹*separatePairs*c)⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        ((wing true).map (unipotent (F := F)).subtype).map
          (MulAut.conj (separatePairs (F := F))⁻¹).toMonoidHom := by
      rw [←hE]
      simp only [map_conj_mul]
      apply congrArg (fun h : Sp F => E.map (MulAut.conj h).toMonoidHom)
      group
    have transport (K : Subgroup (Sp F)) (hv : ∀ y ∈ K, y • v = v) :
        ∀ y ∈ K.map (MulAut.conj c).toMonoidHom, y • (c • v) = c • v := by
      rintro y ⟨z,hz,rfl⟩
      change (c*z*c⁻¹) • (c • v) = c • v
      rw [←mul_smul,inv_mul_cancel_right,mul_smul,hv z hz]
    have hzero := plane_pair_fixed_eq_zero (c • v)
      (hE ▸ transport _ hv) (hEx ▸ transport _ hw)
    have hz := congrArg (fun w : Vector F => c⁻¹ • w) hzero
    simpa only [inv_smul_smul,smul_zero] using hz

/-- A plane radical and a full long root admit the three actual source generators. -/
theorem exists_plane_two_root_generators
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hA : ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ := by
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
    rw [←map_conj_mul,hh,h01]
  refine ⟨c⁻¹*k,c⁻¹*swapPairs*c,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [Subgroup.map_sup,Subgroup.map_sup,map_conj_mul,map_conj_mul,hAc]
  rw [show c*(c⁻¹*k)=k by group,show c*(c⁻¹*swapPairs*c)=swapPairs*c by group,hk,
    ←map_conj_mul,hAc,plane_and_two_long_roots]
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]

/-- An order-64 small two-subgroup is the whole plane radical in Sylow coordinates. -/
theorem conjugate_plane_of_small_order
    [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (E : Subgroup (Sp F)) (hE : IsPGroup 2 E) (hc : Nat.card E = 64)
    (hm : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E) ≤ 16) :
    ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype := by
  obtain ⟨P,hP⟩ := hE.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) P
    (unipotentSylow (n := 2) hF (by decide))
  have hkP : (P : Subgroup (Sp F)).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let E' := E.map (MulAut.conj k).toMonoidHom
  have hEU : E' ≤ unipotent := hkP ▸ map_mono hP
  let A := E'.subgroupOf unipotent
  have hAm : A.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hEU
  have hAc : Nat.card A = 64 := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hAm,
      card_map_of_injective (MulAut.conj k).injective,hc]
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
  have hbound : SmallMovers.movingIndex A ≤ 16 := by
    rw [←SmallMovers.binary_movingIndex]
    change 2 ^ BinaryOffender.fixedCodim (σ.comp (unipotent (F := F)).subtype) A ≤ 16
    rw [hdim',←hdim]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hm
    exact hm
  have hs : SmallMovers.Small A := ⟨by rw [hAc]; omega,hbound⟩
  have hAw : A = wing true := by
    rcases SmallMovers.small_classification_nonstandard hF A hs with h | ⟨l,hl⟩
    · apply eq_of_le_of_card_ge h
      rw [card_wing,hF,hAc]
      decide
    · rw [hl,SmallMovers.card_finitePlane,hF] at hAc
      norm_num at hAc
  exact ⟨k,hAm.symm.trans (congrArg (Subgroup.map (unipotent (F := F)).subtype) hAw)⟩

/-- The natural small-mover and full-root conditions produce actual generators. -/
theorem exists_small_mover_two_root_generators
    [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (E A : Subgroup (Sp F)) (hE : IsPGroup 2 E) (hc : Nat.card E = 64)
    (hm : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E) ≤ 16)
    (hAc : Nat.card A = 4) (hAd : Module.finrank F (displacementSpace A) = 1)
    (hAq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ :=
  exists_plane_two_root_generators E A (conjugate_plane_of_small_order hF E hE hc hm)
    (FourLongRoots.exists_conjugate_root_of_displacement_one A (hAc.trans hF.symm) hAd hAq)
/-- The small-mover and full-root conditions supply generation and separation simultaneously. -/
theorem exists_small_mover_two_root_separated_generators
    [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (E A : Subgroup (Sp F)) (hE : IsPGroup 2 E) (hc : Nat.card E = 64)
    (hm : Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E) ≤ 16)
    (hAc : Nat.card A = 4) (hAd : Module.finrank F (displacementSpace A) = 1)
    (hAq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v) :
    ∃ g x : Sp F, (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
      A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (∀ v : Vector F,
        (∀ y ∈ E.map (MulAut.conj g).toMonoidHom, y • v = v) →
        (∀ y ∈ (E.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom, y • v = v) → v = 0) :=
  exists_plane_two_root_separated_generators E A (conjugate_plane_of_small_order hF E hE hc hm)
    (FourLongRoots.exists_conjugate_root_of_displacement_one A (hAc.trans hF.symm) hAd hAq)

/-- The standard selector also preserves the original opposite plane radical. -/
theorem exists_standard_plane_root_selector :
    ∃ x : Sp F,
      (((wing true).map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1) ⊔
        (RootSubgroup.group 1).map (MulAut.conj x).toMonoidHom = ⊤) ∧
      (∀ v : Vector F,
        (∀ y ∈ (wing true).map (unipotent (F := F)).subtype, y • v = v) →
        (∀ y ∈ ((wing true).map (unipotent (F := F)).subtype).map
          (MulAut.conj x⁻¹).toMonoidHom, y • v = v) → v = 0) ∧
      TwoConjugate.opposition⁻¹*x*TwoConjugate.opposition ∈
        normalizer ((wing true).map (unipotent (F := F)).subtype : Set (Sp F)) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  refine ⟨separatePairs,?_,plane_pair_fixed_eq_zero,?_⟩
  · have hmaps : (RootSubgroup.group (F := F) 1).map (MulAut.conj separatePairs).toMonoidHom =
        (RootSubgroup.group 1).map (MulAut.conj swapPairs).toMonoidHom := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
        refine ⟨rootElement 1 t,subset_closure ⟨t,rfl⟩,?_⟩
        change swapPairs * rootElement 1 t * swapPairs⁻¹ =
          separatePairs * rootElement 1 t * separatePairs⁻¹
        rw [swap_lower,separate_lower]
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
        refine ⟨rootElement 1 t,subset_closure ⟨t,rfl⟩,?_⟩
        change separatePairs * rootElement 1 t * separatePairs⁻¹ =
          swapPairs * rootElement 1 t * swapPairs⁻¹
        rw [swap_lower,separate_lower]
    rw [hmaps]
    exact plane_and_two_long_roots
  · let o := TwoConjugate.opposition (F := F)
    have hm : (o⁻¹*separatePairs*o).val = fromBlocks !![0,1;1,0] 1 0 !![0,1;1,0] := by
      have ho : o⁻¹=o := TwoConjugate.opposition_inv
      rw [ho]
      change o.val*(separatePairs (F := F)).val*o.val = _
      rw [separatePairs_matrix]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [o,TwoConjugate.opposition,Matrix.mul_apply,Fintype.sum_sum_type,
          Matrix.fromBlocks,Matrix.one_apply]
    have hl : o⁻¹*separatePairs*o ∈ planeLocal := by
      apply (Plane.mem_local_iff _).mpr
      refine ⟨?_,?_⟩
      · rw [mem_planeParabolic_iff]
        intro i j
        rw [hm]
        rfl
      · rw [hm]
        simp [Matrix.toBlocks₁₁,Matrix.fromBlocks,Matrix.det_fin_two,CharTwo.neg_eq]
    rw [←SymplecticConjugatePair.planeRadical_eq_wing]
    exact (Plane.radical (F := F)).le_normalizer_map planeLocal.subtype
      (mem_map_of_mem planeLocal.subtype (by rw [normalizer_eq_top]; trivial :
        (⟨_,hl⟩ : planeLocal (F := F)) ∈ normalizer (Plane.radical (F := F) : Set (planeLocal (F := F)))))

end Theory.SpecificGroups.SymplecticFour.SelectedGeneration
