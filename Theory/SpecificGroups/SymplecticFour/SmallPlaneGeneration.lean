module
public import Theory.SpecificGroups.SymplecticFour.PointMoverGeneration
public import Theory.SpecificGroups.SymplecticFour.SelectedPlaneGeneration
/-!
# Smaller plane actors and two selected roots generate Sp₄

A plane actor strictly larger than a contained full long root can be
positioned, by a plane-preserving shear, to contain an element with a
nonzero off-diagonal entry. The first rank-one torus extracts a full short
root. Together with the two selected lower long roots, this generates Sp₄.
The same selector preserves the original plane radical and makes its two
conjugates generate; all assertions use one pair of conjugators.

This works at every finite characteristic-two field order greater than two.
The full-kernel consumer is NonbinarySymplectic.CriticalReduction.SmallerSelection.
Source: MS93 (5.6)(b--d), printed pp.917--918, field-sized critical-image branch.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

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


omit [Finite F] in
private theorem extract_short (s u w v : F) :
    (element 0 (s^2*u) (s*w) v * element 0 u w v * element 0 (s^2*u+u) 0 0).val =
      rootElement 4 (s*w+w) := by
  rw [element_mul,element_mul]
  simp [element,RootSubgroup.element_zero,CharTwo.add_self_eq_zero,add_assoc]

omit [Finite F] in
private theorem short_second_commutator (t : F) :
    rootElement 4 t * rootElement 3 1 * rootElement 4 t * rootElement 3 1 *
      rootElement 0 (t^2) = rootElement 6 t := by
  apply Subtype.ext
  change rootMatrix 4 t * rootMatrix 3 1 * rootMatrix 4 t * rootMatrix 3 1 *
    rootMatrix 0 (t^2) = rootMatrix 6 t
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,Fin.sum_univ_two,
      Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq,CharTwo.add_self_eq_zero,pow_two]

private theorem cross_shear_generates (hF : 2 < Nat.card F)
    (H : Subgroup (Sp F))
    (h0 : ∀ t, rootElement 0 t ∈ H) (h1 : ∀ t, rootElement 1 t ∈ H)
    (h3 : ∀ t, rootElement 3 t ∈ H)
    {u w v : F} (hx : (element 0 u w v).val ∈ H) (hw : w ≠ 0) : H=⊤ := by
  let := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [←Nat.card_eq_fintype_card,Nat.card_units]; omega)
  obtain ⟨s,hs⟩ := exists_ne (1 : Fˣ)
  have hs1 : (s:F) ≠ 1 := fun he => hs (Units.ext he)
  have hxs : (element 0 ((s:F)^2*u) ((s:F)*w) v).val ∈ H := by
    have hh := H.mul_mem (H.mul_mem (scaleFirst_mem H h0 h1 s) hx)
      (H.inv_mem (scaleFirst_mem H h0 h1 s))
    rw [scaleFirst_element] at hh
    simpa only [mul_zero] using hh
  have he0 : (element 0 ((s:F)^2*u+u) 0 0).val ∈ H := by
    simpa [element,RootSubgroup.element_zero] using h0 ((s:F)^2*u+u)
  have hp := H.mul_mem (H.mul_mem hxs hx) he0
  change (element 0 ((s:F)^2*u) ((s:F)*w) v * element 0 u w v *
    element 0 ((s:F)^2*u+u) 0 0).val ∈ H at hp
  rw [extract_short] at hp
  let c : F := (s:F)*w+w
  have hc : c ≠ 0 := by
    intro he
    have hh : (s:F)*w=w := CharTwo.add_eq_zero.mp he
    exact hs1 (mul_right_cancel₀ hw (by simpa using hh))
  have h4 (t : F) : rootElement 4 t ∈ H := by
    by_cases ht : t=0
    · subst t; simp [RootSubgroup.element_zero]
    let r : Fˣ := Units.mk0 (t/c) (div_ne_zero ht hc)
    have he : rootElement 4 c = (element 0 0 c 0).val := by
      simp [element,RootSubgroup.element_zero]
    have hh := H.mul_mem (H.mul_mem (scaleFirst_mem H h0 h1 r) hp)
      (H.inv_mem (scaleFirst_mem H h0 h1 r))
    change scaleFirst r * rootElement 4 c * (scaleFirst r)⁻¹ ∈ H at hh
    rw [he,scaleFirst_element] at hh
    simpa [r,element,RootSubgroup.element_zero,div_mul_cancel₀ _ hc] using hh
  have h6 (t : F) : rootElement 6 t ∈ H := by
    rw [←short_second_commutator]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (h4 t) (h3 1)) (h4 t)) (h3 1)) (h0 (t^2))
  have hpoint : (wing false).map (unipotent (F := F)).subtype ≤ H := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    have hv : v=0 := (element_mem_wing _ _ _ _ _).mp hy
    subst v
    simpa [element,RootSubgroup.element_zero] using
      H.mul_mem (H.mul_mem (h6 b) (h0 (u+b*w))) (h4 w)
  exact top_unique (SelectedGeneration.point_wing_and_long_root (F := F) ▸
    sup_le hpoint ((closure_le _).mpr (by rintro _ ⟨t,rfl⟩; exact h1 t)))


omit [Finite F] in
private theorem shear_conj (b u w v : F) :
    rootElement 6 b * (element 0 u w v).val * (rootElement 6 b)⁻¹ =
      (element 0 (u+b^2*v) (w+b*v) v).val := by
  rw [mul_inv_eq_iff_eq_mul]
  have he : rootElement 6 b = (element b 0 0 0).val := by
    simp [element,RootSubgroup.element_zero]
  rw [he]
  change (element b 0 0 0 * element 0 u w v).val =
    (element 0 (u+b^2*v) (w+b*v) v * element b 0 0 0).val
  apply congrArg Subtype.val
  rw [element_mul,element_mul,element_eq_iff]
  simp only [zero_mul,mul_zero,add_zero,zero_add]
  simp only [true_and,and_true,eq_self_iff_true]
  constructor <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem shear_preserves_plane (b : F) :
    ((wing true).map (unipotent (F := F)).subtype).map
      (MulAut.conj (rootElement 6 b)).toMonoidHom = (wing true).map unipotent.subtype := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    obtain ⟨⟨c,u,w,v⟩,rfl⟩ := element_surjective x
    have hc : c=0 := (element_mem_wing true _ _ _ _).mp hx
    subst c
    change rootElement 6 b * (element 0 u w v).val * (rootElement 6 b)⁻¹ ∈ _
    rw [shear_conj]
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)
  · exact (card_map_of_injective (MulAut.conj (rootElement 6 b)).injective).ge

omit [Finite F] in
private theorem shear_preserves_root (b t : F) :
    rootElement 6 b * rootElement 0 t * (rootElement 6 b)⁻¹ = rootElement 0 t := by
  have he : rootElement 0 t = (element 0 t 0 0).val := by
    simp [element,RootSubgroup.element_zero]
  rw [he,shear_conj]
  simp

/-- A plane actor properly above the first full root can be positioned
inside the same plane so that it generates with the two lower long roots. -/
theorem exists_plane_preserving_three_roots (hF : 2 < Nat.card F)
    (E : Subgroup (Sp F))
    (hEP : E ≤ (wing true).map unipotent.subtype)
    (h0 : RootSubgroup.group 0 ≤ E) (hc : Nat.card F < Nat.card E) :
    ∃ k : Sp F,
      (((wing true).map unipotent.subtype).map (MulAut.conj k).toMonoidHom =
        (wing true).map unipotent.subtype) ∧
      ((E.map (MulAut.conj k).toMonoidHom ⊔ RootSubgroup.group 1) ⊔
        RootSubgroup.group 3 = ⊤) := by
  have hn : ¬ E ≤ RootSubgroup.group 0 := by
    intro he
    have hh := card_le_of_le he
    rw [RootSubgroup.card] at hh
    omega
  obtain ⟨x,hx,hnx⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨y,hy,rfl⟩ := hEP hx
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
  have hb : b=0 := (element_mem_wing true _ _ _ _).mp hy
  subst b
  have hwv : w≠0 ∨ v≠0 := by
    by_contra! hh
    obtain ⟨rfl,rfl⟩ := hh
    apply hnx
    have hr : rootElement 0 u ∈ RootSubgroup.group (F := F) 0 := subset_closure ⟨u,rfl⟩
    change (element 0 u 0 0).val ∈ RootSubgroup.group 0
    have he : (element (0:F) u 0 0).val = rootElement 0 u := by
      simp [element,RootSubgroup.element_zero]
    rw [he]
    exact hr
  obtain ⟨b,hb⟩ : ∃ b : F, w+b*v ≠ 0 := by
    rcases hwv with hw | hv
    · exact ⟨0,by simpa using hw⟩
    · by_cases hw : w=0
      · exact ⟨1,by simpa [hw] using hv⟩
      · exact ⟨0,by simpa using hw⟩
  let k := rootElement 6 b
  let J := (E.map (MulAut.conj k).toMonoidHom ⊔ RootSubgroup.group 1) ⊔ RootSubgroup.group 3
  refine ⟨k,shear_preserves_plane b,?_⟩
  have hr0 (t : F) : rootElement 0 t ∈ J := by
    apply (show E.map (MulAut.conj k).toMonoidHom ≤ J from le_sup_left.trans le_sup_left)
    refine ⟨rootElement 0 t,h0 (subset_closure ⟨t,rfl⟩),shear_preserves_root b t⟩
  have hr1 (t : F) : rootElement 1 t ∈ J :=
    (show RootSubgroup.group 1 ≤ J from le_sup_right.trans le_sup_left) (subset_closure ⟨t,rfl⟩)
  have hr3 (t : F) : rootElement 3 t ∈ J := mem_sup_right (subset_closure ⟨t,rfl⟩)
  apply cross_shear_generates hF J hr0 hr1 hr3 (w := w+b*v) (v := v) (u := u+b^2*v) _ hb
  rw [←shear_conj]
  exact (show E.map (MulAut.conj k).toMonoidHom ≤ J from le_sup_left.trans le_sup_left)
    (mem_map_of_mem _ hx)


omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

variable [Algebra (ZMod 2) F]
/-- A proper overgroup of a full root inside a plane radical has the
simultaneous source selector: generation uses the smaller subgroup,
the full plane pair generates, and the selector preserves the original plane. -/
theorem exists_subplane_root_generators (hF : 2 < Nat.card F)
    (P E A : Subgroup (Sp F))
    (hP : ∃ k : Sp F, P.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hEP : E ≤ P) (hAE : A ≤ E) (hcE : Nat.card F < Nat.card E)
    (hcA : Nat.card A = Nat.card F)
    (hdA : Module.finrank F (displacementSpace A) = 1) :
    ∃ g x : Sp F,
      (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
        A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (P.map (MulAut.conj g).toMonoidHom ⊔
        (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      x ∈ normalizer (P : Set (Sp F)) := by
  obtain ⟨h,hh,ha⟩ := SelectedPositioning.plane_root_coordinates P A hP (hAE.trans hEP) hcA hdA
  obtain ⟨k,hk,hgen⟩ := exists_plane_preserving_three_roots hF
    (E.map (MulAut.conj h).toMonoidHom) (hh ▸ map_mono hEP)
    (ha ▸ map_mono hAE) (by rwa [card_map_of_injective (MulAut.conj h).injective])
  obtain ⟨x₀,hroot,hpair,hpos⟩ := SelectedPlaneGeneration.exists_standard_root_plane_selector (F := F)
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
    rw [←map_conj_mul,ha,h01]
  have htop : (⊤ : Subgroup (Sp F)).map (MulAut.conj c).toMonoidHom = ⊤ :=
    map_top_of_surjective _ (MulAut.conj c).surjective
  refine ⟨c⁻¹*(k*h),c⁻¹*x₀*c,?_,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_conj_mul,map_conj_mul,hAc,htop]
    rw [show c*(c⁻¹*(k*h))=k*h by group,
      show c*(c⁻¹*x₀*c)=x₀*c by group,←map_conj_mul A x₀ c,hAc,hroot,←map_conj_mul E k h]
    exact hgen
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,map_conj_mul,map_conj_mul,map_conj_mul,htop]
    rw [show c*(c⁻¹*(k*h))=k*h by group,
      show c*(c⁻¹*x₀*c)⁻¹*(c⁻¹*(k*h))=x₀⁻¹*(k*h) by group,
      ←map_conj_mul P x₀⁻¹ (k*h),←map_conj_mul P k h,hh,hk]
    exact hpair
  · rw [mem_normalizer_iff_map_conj_eq]
    change P.map (MulAut.conj (c⁻¹*x₀*c)).toMonoidHom = P
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    rw [map_conj_mul,hh]
    have heq : h*(c⁻¹*x₀*c)=(o⁻¹*x₀*o)*h := by dsimp [c]; group
    rw [heq,←map_conj_mul,hh]
    exact mem_normalizer_iff_map_conj_eq.mp hpos

end Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
