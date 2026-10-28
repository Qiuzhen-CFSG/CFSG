module
public import Theory.SpecificGroups.SymplecticFour.PointMoverGeneration
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Frattini

/-!
# A long-root generator for large normal symplectic movers

A normal subgroup of the field-four unipotent group with order at least
64 has abelian quotient of order at most four. The explicit square and
commutator formulas put the whole Sylow center in that subgroup.

The central roots together with an opposite long root contain a first
coordinate torus. Conjugating any element outside the plane radical by
this torus extracts the missing short root. The resulting point radical
and long root generate Sp4. Transport to an arbitrary Sylow subgroup and
the prescribed long root retains the same natural representation.

This proves the inner-image selection needed in MS93 (5.5)(c), pp.915--917,
without assuming the mover is abelian. The original-kernel application is
Sp4Four.SourceComparison.OriginalNormalMoverGeneration and its tensor
backward-path consumer is GenerationTwoSymplecticNormalSelection.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open scoped commutatorElement IsMulCommutative
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SelectedGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem small_commutative {K : Type*} [Group K] [Finite K]
    (h : Nat.card K ≤ 4) : IsMulCommutative K := by
  have hp : 0 < Nat.card K := Nat.card_pos
  have hh : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 3 ∨ Nat.card K = 4 := by omega
  rcases hh with h1 | h2 | h3 | h4
  · let : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic K := isCyclic_of_prime_card h2
    infer_instance
  · let : IsCyclic K := isCyclic_of_prime_card h3
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h4

omit [Finite F] in
private theorem theta_square_commutator (b v : F) :
    theta (b^2*v) (b*v) = ⁅element b 0 0 0,element 0 0 0 v⁆ := by
  rw [commutatorElement_def]
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply (eq_mul_inv_iff_mul_eq).mpr
  simp only [theta,element_mul]
  apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
  simp [CharTwo.add_self_eq_zero,add_assoc,mul_comm,mul_left_comm,mul_assoc,pow_two]

theorem normal_large_contains_center (hF : Nat.card F = 4)
    (E : Subgroup (unipotent (F := F))) [E.Normal] (hc : 64 ≤ Nat.card E) :
    center (unipotent (F := F)) ≤ E := by
  have hi := E.card_mul_index
  rw [card_unipotent,hF] at hi
  have hindex : E.index ≤ 4 := by nlinarith
  let : IsMulCommutative (unipotent (F := F) ⧸ E) := small_commutative hindex
  have hsq (x : unipotent (F := F)) : x^2 ∈ E := by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    rw [element_square,theta_square_commutator]
    rw [←QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' E ⁅element b 0 0 0,element 0 0 0 v⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  rw [←frattini_eq_center (n := 2) hF (by decide),
    (isPGroup_unipotent (n := 2) hF).frattini_eq_closure_squares]
  exact (closure_le _).mpr (by rintro _ ⟨x,rfl⟩; exact hsq x)

private def scaleFirst (s : Fˣ) : Sp F :=
  (rootElement 0 (s : F) * rootElement 1 ((s⁻¹ : Fˣ) : F) * rootElement 0 (s : F)) *
    (rootElement 0 1 * rootElement 1 1 * rootElement 0 1)

omit [Finite F] in
private theorem scaleFirst_matrix (s : Fˣ) :
    (scaleFirst s).val = diagonal (Sum.elim ![(s : F),1] ![((s⁻¹ : Fˣ) : F),1]) := by
  change (rootMatrix 0 (s : F) * rootMatrix 1 ((s⁻¹ : Fˣ) : F) * rootMatrix 0 (s : F)) *
    (rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1) = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.single, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.add_self_eq_zero,
      Matrix.diagonal]

omit [Finite F] in
private theorem scaleFirst_element (s : Fˣ) (b u w v : F) :
    scaleFirst s * (element b u w v).val * (scaleFirst s)⁻¹ =
      (element ((s:F)*b) ((s:F)^2*u) ((s:F)*w) v).val := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (scaleFirst s).val * (element b u w v).val.val =
    (element ((s:F)*b) ((s:F)^2*u) ((s:F)*w) v).val.val * (scaleFirst s).val
  rw [scaleFirst_matrix,element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.fromBlocks,
      pow_two,mul_add,mul_assoc,mul_comm,mul_left_comm]

omit [Finite F] [CharP F 2] in
private theorem scaleFirst_mem (H : Subgroup (Sp F))
    (h0 : ∀ t, rootElement 0 t ∈ H) (h1 : ∀ t, rootElement 1 t ∈ H) (s : Fˣ) :
    scaleFirst s ∈ H :=
  H.mul_mem (H.mul_mem (H.mul_mem (h0 _) (h1 _)) (h0 _))
    (H.mul_mem (H.mul_mem (h0 _) (h1 _)) (h0 _))

omit [Finite F] [CharP F 2] in
private theorem root6_mem_of_element (H : Subgroup (Sp F))
    (h0 : ∀ t, rootElement 0 t ∈ H) (h4 : ∀ t, rootElement 4 t ∈ H)
    {b u w : F} (hx : (element b u w 0).val ∈ H) : rootElement 6 b ∈ H := by
  have he : (element b u w 0).val = rootElement 6 b *
      (rootElement 0 (u+b*w)*rootElement 4 w) := by
    simp [element,RootSubgroup.element_zero,mul_assoc]
  rw [he] at hx
  exact (H.mul_mem_cancel_right (H.mul_mem (h0 _) (h4 _))).mp hx

theorem center_and_nonplane_long_root_generate (hF : 2 < Nat.card F)
    (E : Subgroup (unipotent (F := F)))
    (hZ : center (unipotent (F := F)) ≤ E) (hn : ¬ E ≤ wing true) :
    E.map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1 = ⊤ := by
  let H := E.map (unipotent (F := F)).subtype ⊔ RootSubgroup.group 1
  have htheta (u w : F) : (theta u w).val ∈ H :=
    (show E.map (unipotent (F := F)).subtype ≤ H from le_sup_left)
      (mem_map_of_mem _ (hZ (theta_mem_center _ _)))
  have h0 (u : F) : rootElement 0 u ∈ H := by
    simpa [theta_val,RootSubgroup.element_zero] using htheta u 0
  have h4 (w : F) : rootElement 4 w ∈ H := by
    simpa [theta_val,RootSubgroup.element_zero] using htheta 0 w
  have h1 (u : F) : rootElement 1 u ∈ H :=
    (show RootSubgroup.group 1 ≤ H from le_sup_right) (subset_closure ⟨u,rfl⟩)
  obtain ⟨x,hx,hxw⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hb : b ≠ 0 := by simpa only [element_mem_wing,↓reduceIte] using hxw
  have hxH : (element b u w v).val ∈ H := (show E.map (unipotent (F := F)).subtype ≤ H from le_sup_left) (mem_map_of_mem _ hx)
  let := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [←Nat.card_eq_fintype_card,Nat.card_units]; omega)
  obtain ⟨s,hs⟩ := exists_ne (1 : Fˣ)
  have hs1 : (s:F) ≠ 1 := fun h => hs (Units.ext h)
  have hxs : (element ((s:F)*b) ((s:F)^2*u) ((s:F)*w) v).val ∈ H := by
    rw [←scaleFirst_element]
    exact H.mul_mem (H.mul_mem (scaleFirst_mem H h0 h1 s) hxH)
      (H.inv_mem (scaleFirst_mem H h0 h1 s))
  have hp := H.mul_mem hxs hxH
  change ((element ((s:F)*b) ((s:F)^2*u) ((s:F)*w) v)*element b u w v).val ∈ H at hp
  rw [element_mul,CharTwo.add_self_eq_zero] at hp
  have hr := root6_mem_of_element H h0 h4 hp
  let c : F := (s:F)*b+b
  have hc : c ≠ 0 := by
    intro h
    have hh : (s:F)*b=b := CharTwo.add_eq_zero.mp h
    exact hs1 (mul_right_cancel₀ hb (by simpa using hh))
  have h6 (t : F) : rootElement 6 t ∈ H := by
    by_cases ht : t=0
    · subst t; simp [RootSubgroup.element_zero]
    let r : Fˣ := Units.mk0 (t/c) (div_ne_zero ht hc)
    have he : rootElement 6 c = (element c 0 0 0).val := by
      simp [element,RootSubgroup.element_zero]
    have hh := H.mul_mem (H.mul_mem (scaleFirst_mem H h0 h1 r) hr)
      (H.inv_mem (scaleFirst_mem H h0 h1 r))
    change scaleFirst r * rootElement 6 c * (scaleFirst r)⁻¹ ∈ H at hh
    rw [he,scaleFirst_element] at hh
    simpa [r,element,RootSubgroup.element_zero,div_mul_cancel₀ _ hc] using hh
  have hpoint : (wing false).map (unipotent (F := F)).subtype ≤ H := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    have hv : v=0 := (element_mem_wing _ _ _ _ _).mp hy
    subst v
    simpa [element,RootSubgroup.element_zero] using
      H.mul_mem (H.mul_mem (h6 b) (h0 (u+b*w))) (h4 w)
  exact top_unique (point_wing_and_long_root (F := F) ▸ sup_le hpoint le_sup_right)

/-- A large Sylow-normal actor with movement above the plane bound has a
single-root generating conjugate; commutativity of the actor is unnecessary. -/
theorem exists_normal_large_root_generator
    [Algebra (ZMod 2) F] (hF : Nat.card F = 4)
    (P : Sylow 2 (Sp F)) (E A : Subgroup (Sp F))
    (hEP : E ≤ P) (hPN : (P : Subgroup (Sp F)) ≤ normalizer (E : Set (Sp F)))
    (hc : 64 ≤ Nat.card E)
    (hm : 16 < Nat.card (Vector F ⧸ BinaryOffender.fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)) E))
    (hA : ∃ h : Sp F, A.map (MulAut.conj h).toMonoidHom = RootSubgroup.group 0) :
    ∃ g : Sp F, E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq (Sp F) P
    (unipotentSylow (n := 2) hF (by decide))
  have hkP : (P : Subgroup (Sp F)).map (MulAut.conj k).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hk
  let E' := E.map (MulAut.conj k).toMonoidHom
  have hEU : E' ≤ unipotent := hkP ▸ map_mono hEP
  let N := E'.subgroupOf unipotent
  have hNm : N.map (unipotent (F := F)).subtype = E' := map_subgroupOf_eq_of_le hEU
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hEU).mpr
    (hkP ▸ (map_mono hPN).trans (le_normalizer_map _))
  have hNc : Nat.card N = Nat.card E := by
    rw [←card_map_of_injective (unipotent (F := F)).subtype_injective,hNm,
      card_map_of_injective (MulAut.conj k).injective]
  have hZ := normal_large_contains_center hF N (hNc.symm ▸ hc)
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
  have hdim := BinaryOffender.fixedCodim_map_equivariant σ σ (MulAut.conj k).toMonoidHom
    (SymplecticConjugatePair.Ambient.linearAction σ k)
    (fun g v => by
      change σ k (σ g v) = σ (k*g*k⁻¹) (σ k v)
      simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]) E
  have hdim' := BinaryOffender.fixedCodim_map_equivariant
    (σ.comp (unipotent (F := F)).subtype) σ (unipotent (F := F)).subtype
    (LinearEquiv.refl _ _) (fun _ _ => rfl) N
  rw [hNm] at hdim'
  have hbound : 16 < SmallMovers.movingIndex N := by
    rw [←SmallMovers.binary_movingIndex]
    change 16 < 2 ^ BinaryOffender.fixedCodim (σ.comp (unipotent (F := F)).subtype) N
    rw [hdim',←hdim]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hm
    exact hm
  have hn : ¬ N ≤ wing true := by
    intro hh
    have hh := SmallMovers.movingIndex_le_field_sq_of_le_wing N hh
    rw [hF] at hh
    omega
  have hgen : E' ⊔ RootSubgroup.group 1 = ⊤ := by
    rw [←hNm]
    exact center_and_nonplane_long_root_generate (by omega) N hZ hn
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
  have hmaps (B : Subgroup (Sp F)) (g h : Sp F) :
      (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        B.map (MulAut.conj (g*h)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hAc : A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 := by
    rw [←hmaps,hh,h01]
  refine ⟨c⁻¹*k,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [Subgroup.map_sup,hmaps,hAc,show c*(c⁻¹*k)=k by group,hgen]
  rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
end Theory.SpecificGroups.SymplecticFour.SelectedGeneration
