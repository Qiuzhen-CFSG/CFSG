module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# Complements to root planes inside Sylow two-subgroups of SL₃

In characteristic two, a subgroup of UT₃ whose elements square to one lies
in one of its two coordinate root planes. Order |F|² then forces equality.
Swapping the first two or last two coordinates supplies a conjugate plane
whose intersection with UT₃ is the missing simple-root subgroup. Literal
matrix multiplication proves both disjointness and coverage. Sylow
conjugacy transports this construction to an arbitrary specified Sylow.

The final action lemma derives square one from displacement in a pointwise
fixed subspace. Together these results give the finite matrix calculation
used in Aschbacher–Smith G.2.5(3), printed pp.335–336, including |F| = 2.
All groups and conjugators here are in SL₃, before any projective quotient.
The existing unitriangular coordinate API retains its ATLAS attribution in
`Theory/SpecificGroups/PSL3Even/UnipotentGeometry/Basic.lean`.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.RootPlaneGeometry
namespace Matrix.SpecialLinearGroup.PointRadicalSylow
variable (F : Type*) [Field F] [CharP F 2]

private def swap (point : Bool) : SL(3,F) :=
  ⟨if point then !![0,1,0;1,0,0;0,0,1] else !![1,0,0;0,0,1;0,1,0], by
    cases point <;> simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

private theorem swap_sq (point : Bool) : swap F point * swap F point = 1 := by
  apply Subtype.ext
  change (swap F point).val * (swap F point).val = (1 : Matrix (Fin 3) (Fin 3) F)
  ext i j
  cases point <;> fin_cases i <;> fin_cases j <;>
    simp [swap, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap_inv (point : Bool) : (swap F point)⁻¹ = swap F point :=
  inv_eq_of_mul_eq_one_left (swap_sq F point)

private theorem swap_point (a c : F) :
    ((MulAut.conj (swap F true)⁻¹) (specialLinear F ⟨a,0,c⟩)).val =
      !![1,0,0;a,1,c;0,0,1] := by
  rw [swap_inv]
  change ((swap F true * specialLinear F ⟨a,0,c⟩ * (swap F true)⁻¹)).val = _
  rw [swap_inv]
  change (swap F true).val * matrix F ⟨a,0,c⟩ * (swap F true).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, matrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem swap_line (b c : F) :
    ((MulAut.conj (swap F false)⁻¹) (specialLinear F ⟨0,b,c⟩)).val =
      !![1,c,0;0,1,0;0,b,1] := by
  rw [swap_inv]
  change ((swap F false * specialLinear F ⟨0,b,c⟩ * (swap F false)⁻¹)).val = _
  rw [swap_inv]
  change (swap F false).val * matrix F ⟨0,b,c⟩ * (swap F false).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, matrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem plane_disjoint (point : Bool) :
    Disjoint (rootPlaneSL F point)
      ((rootPlaneSL F point).map (MulAut.conj (swap F point)⁻¹).toMonoidHom) := by
  rw [Subgroup.disjoint_def]
  intro u hu hv
  obtain ⟨v,hv,he⟩ := hv
  cases point
  · obtain ⟨b,c,rfl⟩ := (mem_rootPlaneSL_line F u).mp hu
    obtain ⟨d,e,rfl⟩ := (mem_rootPlaneSL_line F v).mp hv
    have hm := congrArg Subtype.val he
    change ((MulAut.conj (swap F false)⁻¹) (specialLinear F ⟨0,d,e⟩)).val = _ at hm
    rw [swap_line] at hm
    have hb := congrArg (fun m => m 1 2) hm
    have hc := congrArg (fun m => m 0 2) hm
    have hb' : b = 0 := hb.symm
    have hc' : c = 0 := hc.symm
    rw [hb', hc']
    exact (specialLinear F).map_one
  · obtain ⟨a,c,rfl⟩ := (mem_rootPlaneSL_point F u).mp hu
    obtain ⟨d,e,rfl⟩ := (mem_rootPlaneSL_point F v).mp hv
    have hm := congrArg Subtype.val he
    change ((MulAut.conj (swap F true)⁻¹) (specialLinear F ⟨d,0,e⟩)).val = _ at hm
    rw [swap_point] at hm
    have ha := congrArg (fun m => m 0 1) hm
    have hc := congrArg (fun m => m 0 2) hm
    have ha' : a = 0 := ha.symm
    have hc' : c = 0 := hc.symm
    rw [ha', hc']
    exact (specialLinear F).map_one

private theorem plane_covers (point : Bool) :
    unipotentSL F ≤ rootPlaneSL F point ⊔
      (unipotentSL F ⊓ (rootPlaneSL F point).map
        (MulAut.conj (swap F point)⁻¹).toMonoidHom) := by
  intro u hu
  rw [← specialLinear_range] at hu
  obtain ⟨v,rfl⟩ := hu
  cases point
  · have hr : specialLinear F ⟨v.x,0,0⟩ ∈ unipotentSL F ⊓
        (rootPlaneSL F false).map (MulAut.conj (swap F false)⁻¹).toMonoidHom := by
      refine ⟨?_, specialLinear F ⟨0,0,v.x⟩,
        (mem_rootPlaneSL_line F _).mpr ⟨0,v.x,rfl⟩, ?_⟩
      · rw [← specialLinear_range]; exact ⟨_,rfl⟩
      · apply Subtype.ext
        exact swap_line F 0 v.x
    have he : v = (⟨0,v.y,v.c⟩ : U F) * ⟨v.x,0,0⟩ := by
      apply U.ext <;> simp
    rw [he, map_mul]
    exact Subgroup.mul_mem_sup
      ((mem_rootPlaneSL_line F _).mpr ⟨v.y,v.c,rfl⟩) hr
  · have hr : specialLinear F ⟨0,v.y,0⟩ ∈ unipotentSL F ⊓
        (rootPlaneSL F true).map (MulAut.conj (swap F true)⁻¹).toMonoidHom := by
      refine ⟨?_, specialLinear F ⟨0,0,v.y⟩,
        (mem_rootPlaneSL_point F _).mpr ⟨0,v.y,rfl⟩, ?_⟩
      · rw [← specialLinear_range]; exact ⟨_,rfl⟩
      · apply Subtype.ext
        exact swap_point F 0 v.y
    have he : v = (⟨v.x,0,v.c-v.x*v.y⟩ : U F) * ⟨0,v.y,0⟩ := by
      apply U.ext <;> simp
    rw [he, map_mul]
    exact Subgroup.mul_mem_sup
      ((mem_rootPlaneSL_point F _).mpr ⟨v.x,v.c-v.x*v.y,rfl⟩) hr


/-- Each of the two root planes has a conjugate supplying its missing simple root. -/
theorem rootPlane_complement (point : Bool) :
    ∃ x : SL(3,F),
      Disjoint (rootPlaneSL F point)
        (unipotentSL F ⊓ (rootPlaneSL F point).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      unipotentSL F ≤ rootPlaneSL F point ⊔
        (unipotentSL F ⊓ (rootPlaneSL F point).map (MulAut.conj x⁻¹).toMonoidHom) :=
  ⟨swap F point, (plane_disjoint F point).mono_right inf_le_right, plane_covers F point⟩

variable [Finite F]

omit [CharP F 2] [Finite F] in
private theorem rootPlane_card (point : Bool) :
    Nat.card (rootPlaneSL F point) = Nat.card F ^ 2 := by
  rw [rootPlaneSL, Subgroup.card_map_of_injective (specialLinear_injective F)]
  cases point
  · exact card_V₂ F
  · exact card_V₁ F

/-- A square-one subgroup of full plane order is one of the coordinate planes. -/
theorem eq_rootPlane_of_card_exponent_two (A : Subgroup SL(3,F))
    (hAU : A ≤ unipotentSL F) (hcard : Nat.card A = Nat.card F ^ 2)
    (hpow : ∀ a ∈ A, a ^ 2 = 1) : ∃ point : Bool, A = rootPlaneSL F point := by
  have hexp : ∀ u ∈ A.comap (specialLinear F), u ^ 2 = 1 := by
    intro u hu
    apply specialLinear_injective F
    rw [map_pow, map_one]
    exact hpow _ hu
  have hmap : (A.comap (specialLinear F)).map (specialLinear F) = A := by
    apply Subgroup.map_comap_eq_self
    rwa [specialLinear_range]
  have hle (b : Bool) (h : A.comap (specialLinear F) ≤ if b then V₁ F else V₂ F) :
      A = rootPlaneSL F b := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hmap]
      exact Subgroup.map_mono h
    · rw [rootPlane_card, hcard]
  rcases le_plane_of_exponent_two F _ hexp with h | h
  · exact ⟨true, hle true h⟩
  · exact ⟨false, hle false h⟩

private theorem map_right_conjugate {G : Type*} [Group G]
    (A : Subgroup G) (e : MulAut G) (x : G) :
    (A.map (MulAut.conj x⁻¹).toMonoidHom).map e.toMonoidHom =
      (A.map e.toMonoidHom).map (MulAut.conj (e x)⁻¹).toMonoidHom := by
  simp only [Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro a
  change e (x⁻¹ * a * x⁻¹⁻¹) = (e x)⁻¹ * e a * (e x)⁻¹⁻¹
  simp only [map_mul, map_inv]

/-- Every square-one plane inside a Sylow two-subgroup has the required
complement from a literal right conjugate in SL₃. -/
theorem exists_root_complement {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (A : Subgroup SL(3,F)) (R : Sylow 2 SL(3,F))
    (hAR : A ≤ R) (hcard : Nat.card A = Nat.card F ^ 2)
    (hpow : ∀ a ∈ A, a ^ 2 = 1) :
    ∃ x : SL(3,F),
      Disjoint A ((R : Subgroup SL(3,F)) ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom) ∧
      (R : Subgroup SL(3,F)) ≤ A ⊔
        ((R : Subgroup SL(3,F)) ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom) := by
  obtain ⟨g, hg, _⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate F hn hF R
  let e := MulAut.conj g
  let B := A.comap e.toMonoidHom
  have hBA : B.map e.toMonoidHom = A :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective A
  have hBU : B ≤ unipotentSL F := by
    apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hBA]
    change A ≤ (unipotentSL F).map (MulAut.conj g).toMonoidHom
    rwa [hg]
  have hBcard : Nat.card B = Nat.card F ^ 2 := by
    rw [← Subgroup.card_map_of_injective (K := B) (f := e.toMonoidHom) e.injective, hBA, hcard]
  have hBpow : ∀ b ∈ B, b ^ 2 = 1 := by
    intro b hb
    apply e.injective
    rw [map_pow, map_one]
    exact hpow _ hb
  obtain ⟨point, hB⟩ := eq_rootPlane_of_card_exponent_two F B hBU hBcard hBpow
  obtain ⟨x, hd, hc⟩ := rootPlane_complement F point
  rw [← hB] at hd hc
  have hm : (unipotentSL F ⊓ B.map (MulAut.conj x⁻¹).toMonoidHom).map e.toMonoidHom =
      (R : Subgroup SL(3,F)) ⊓ A.map (MulAut.conj (e x)⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ e.injective, map_right_conjugate, hBA]
    exact congrArg (· ⊓ A.map (MulAut.conj (e x)⁻¹).toMonoidHom) hg
  refine ⟨e x, ?_, ?_⟩
  · have hd' := Subgroup.disjoint_map (f := e.toMonoidHom) e.injective hd
    rwa [hBA, hm] at hd'
  · have hc' := Subgroup.map_mono (f := e.toMonoidHom) hc
    rw [Subgroup.map_sup, hBA, hm] at hc'
    exact hg ▸ hc'

omit [Finite F] in
/-- Displacement in a pointwise fixed subspace implies square one in
characteristic two. No dimension assumption is needed for this inference. -/
theorem square_eq_one_of_point_action (point : Submodule F (Fin 3 → F))
    (a : SL(3,F)) (hmove : ∀ v : Fin 3 → F, a.val *ᵥ v - v ∈ point)
    (hfix : ∀ v ∈ point, a.val *ᵥ v = v) : a ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  have h := hfix _ (hmove v)
  rw [Matrix.mulVec_sub] at h
  change (a.val * a.val) *ᵥ v = (1 : Matrix (Fin 3) (Fin 3) F) *ᵥ v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  ext i
  have hi := congrFun h i
  simp only [Pi.sub_apply] at hi
  rw [sub_eq_sub_iff_add_eq_add, CharTwo.add_self_eq_zero,
    add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hi
  exact hi

end Matrix.SpecialLinearGroup.PointRadicalSylow
