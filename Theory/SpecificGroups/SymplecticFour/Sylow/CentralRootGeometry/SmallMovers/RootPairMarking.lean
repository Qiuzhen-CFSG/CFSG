module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeRootProduct

/-!
# Simultaneous standard positions for symplectic transvection roots

Explicit upper and lower two-by-two changes of basis act on the full
transvection parameters. Two roots in the same isotropic plane therefore
have joint image equal to one standard root or the product of the two
orthogonal standard roots. All changes are inner automorphisms of the
original symplectic four-space; no field-degree restriction is used.

Source: the choice of E₁ and E₂ before the rank-one construction in MS93
(5.1), printed p.913. The replacement application in
NonbinarySymplectic.CriticalReduction.RootProductGeometry composes this
conjugation with the original surjective vertex marking.
-/

@[expose] public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix
open scoped Pointwise
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

abbrev rootImage (s : Option F) : Subgroup (Sp F) := (rootFamily s).map unipotent.subtype

omit [Finite F] in
private theorem shift_element (b u w v : F) :
    rootElement 6 b * (element 0 u w v).val * (rootElement 6 b)⁻¹ =
      (element 0 (u+b^2*v) (w+b*v) v).val := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change rootMatrix 6 b * (element 0 u w v).val.val =
    (element 0 (u+b^2*v) (w+b*v) v).val.val * rootMatrix 6 b
  rw [element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.fromBlocks,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.single] <;>
    (ring_nf <;> try simp [CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq])

omit [Finite F] in
private theorem lower_element (c u w v : F) :
    rootElement 7 c * (element 0 u w v).val * (rootElement 7 c)⁻¹ =
      (element 0 u (w+c*u) (v+c^2*u)).val := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change rootMatrix 7 c * (element 0 u w v).val.val =
    (element 0 u (w+c*u) (v+c^2*u)).val.val * rootMatrix 7 c
  rw [element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.fromBlocks,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.single] <;>
    (ring_nf <;> try simp [CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq])

omit [CharP F 2] in
private theorem image_conj_eq_of_le (A B : Subgroup (Sp F)) (g : Sp F)
    (hc : Nat.card A = Nat.card B) (hle : A.map (MulAut.conj g).toMonoidHom ≤ B) :
    A.map (MulAut.conj g).toMonoidHom = B :=
  eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective,hc])

omit [Finite F] in
private theorem mem_rootImage_some (s : F) (x : Sp F) :
    x ∈ rootImage (some s) ↔ ∃ v : F, (element 0 (s^2*v) (s*v) v).val = x := by
  constructor
  · rintro ⟨y,⟨v,rfl⟩,rfl⟩
    exact ⟨v.toAdd,rfl⟩
  · rintro ⟨v,rfl⟩
    exact mem_map_of_mem _ (show transvectionHom s (Multiplicative.ofAdd v) ∈ finiteRoot s from
      ⟨Multiplicative.ofAdd v,rfl⟩)

private theorem mem_rootImage_none (x : Sp F) :
    x ∈ rootImage (none : Option F) ↔ ∃ u : F, (element 0 u 0 0).val = x := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective y
    obtain ⟨rfl,rfl,rfl⟩ := (element_mem_root _ _ _ _).mp hy
    exact ⟨u,rfl⟩
  · rintro ⟨u,rfl⟩
    exact mem_map_of_mem _ ((element_mem_root _ _ _ _).mpr ⟨rfl,rfl,rfl⟩)

theorem rootImage_shift (s b : F) :
    (rootImage (some s)).map (MulAut.conj (rootElement 6 b)).toMonoidHom =
      rootImage (some (s+b)) := by
  apply image_conj_eq_of_le
  · simp only [rootImage,card_map_of_injective (unipotent (F := F)).subtype_injective,card_rootFamily]
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨v,rfl⟩ := (mem_rootImage_some s x).mp hx
    change rootElement 6 b * _ * (rootElement 6 b)⁻¹ ∈ _
    rw [shift_element]
    apply (mem_rootImage_some (s+b) _).mpr
    refine ⟨v,?_⟩
    congr 2 <;> (ring_nf <;> simp [CharTwo.two_eq_zero])

theorem rootImage_none_shift (b : F) :
    (rootImage (none : Option F)).map (MulAut.conj (rootElement 6 b)).toMonoidHom =
      rootImage none := by
  apply image_conj_eq_of_le _ _ _ rfl
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨u,rfl⟩ := (mem_rootImage_none x).mp hx
  change rootElement 6 b * _ * (rootElement 6 b)⁻¹ ∈ _
  rw [shift_element]
  simpa only [mul_zero,add_zero] using (mem_rootImage_none _).mpr ⟨u,rfl⟩

theorem rootImage_zero_lower (c : F) :
    (rootImage (some (0:F))).map (MulAut.conj (rootElement 7 c)).toMonoidHom =
      rootImage (some 0) := by
  apply image_conj_eq_of_le _ _ _ rfl
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨v,rfl⟩ := (mem_rootImage_some 0 x).mp hx
  change rootElement 7 c * _ * (rootElement 7 c)⁻¹ ∈ _
  rw [lower_element]
  simpa only [zero_pow (by decide : 2 ≠ 0),zero_mul,mul_zero,add_zero] using
    (mem_rootImage_some 0 _).mpr ⟨v,rfl⟩

theorem rootImage_inverse_lower (s : F) (hs : s ≠ 0) :
    (rootImage (some s)).map (MulAut.conj (rootElement 7 s⁻¹)).toMonoidHom =
      rootImage none := by
  apply image_conj_eq_of_le
  · simp only [rootImage,card_map_of_injective (unipotent (F := F)).subtype_injective,card_rootFamily]
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨v,rfl⟩ := (mem_rootImage_some s x).mp hx
    change rootElement 7 s⁻¹ * _ * (rootElement 7 s⁻¹)⁻¹ ∈ _
    rw [lower_element]
    apply (mem_rootImage_none _).mpr
    refine ⟨s^2*v,?_⟩
    have h1 : s*v+s⁻¹*(s^2*v)=0 := by
      field_simp
      simp [CharTwo.add_self_eq_zero]
    have h2 : v+s⁻¹^2*(s^2*v)=0 := by
      rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ hs,one_pow,one_mul,CharTwo.add_self_eq_zero]
    rw [h1,h2]

omit [CharP F 2] [Finite F] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    A.map (MulAut.conj (g*h)).toMonoidHom =
      (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

/-- A full root or a product of two roots has one of the three standard
positions in the same four-space, using actual symplectic conjugation. -/
theorem rootPair_standard (s t : Option F) :
    ∃ g : Sp F,
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom = rootImage none ∨
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom = rootImage (some 0) ∨
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom =
        rootImage none ⊔ rootImage (some 0) := by
  cases s with
  | none =>
    cases t with
    | none =>
      refine ⟨1,Or.inl ?_⟩
      rw [sup_idem]
      rw [show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id (Sp F) by
        ext x; simp]
      exact map_id _
    | some t =>
      refine ⟨rootElement 6 t,Or.inr (Or.inr ?_)⟩
      rw [Subgroup.map_sup,rootImage_none_shift,rootImage_shift,CharTwo.add_self_eq_zero]
  | some s =>
    cases t with
    | none =>
      refine ⟨rootElement 6 s,Or.inr (Or.inr ?_)⟩
      rw [Subgroup.map_sup,rootImage_none_shift,rootImage_shift,CharTwo.add_self_eq_zero,sup_comm]
    | some t =>
      by_cases he : s=t
      · subst t
        refine ⟨rootElement 6 s,Or.inr (Or.inl ?_)⟩
        rw [sup_idem,rootImage_shift,CharTwo.add_self_eq_zero]
      · have hr : t+s ≠ 0 := by
          intro hh
          have ht : t = s := by
            have hh' := eq_neg_of_add_eq_zero_left hh
            simpa only [CharTwo.neg_eq] using hh'
          exact he ht.symm
        refine ⟨rootElement 7 (t+s)⁻¹ * rootElement 6 s,Or.inr (Or.inr ?_)⟩
        rw [map_conj_mul,Subgroup.map_sup,rootImage_shift,rootImage_shift,
          CharTwo.add_self_eq_zero,Subgroup.map_sup,rootImage_zero_lower,
          rootImage_inverse_lower _ hr,sup_comm]

/-- The singleton case can always use the first standard root. -/
theorem rootPair_standard_first (s t : Option F) :
    ∃ g : Sp F,
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom = rootImage none ∨
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom =
        rootImage none ⊔ rootImage (some 0) := by
  obtain ⟨g,hg | hg | hg⟩ := rootPair_standard s t
  · exact ⟨g,Or.inl hg⟩
  · let w := rootElement (K := F) 7 1 * rootElement 6 1
    refine ⟨w*g,Or.inl ?_⟩
    rw [map_conj_mul,hg]
    change (rootImage (some (0:F))).map (MulAut.conj
      (rootElement 7 1 * rootElement 6 1)).toMonoidHom = _
    rw [map_conj_mul,rootImage_shift,zero_add]
    simpa using rootImage_inverse_lower (1:F) one_ne_zero
  · exact ⟨g,Or.inr hg⟩

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
