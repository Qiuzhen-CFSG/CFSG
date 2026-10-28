module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Proper Sylow overgroups in the actual degree-three projective group

The opposite-corner root extraction only uses the standard unipotent group.
Once all elementary transvections have been obtained, elementary generation
supplies every determinant-one diagonal as well. Thus every proper subgroup
containing that unipotent group stabilizes the standard point or line, without
a full-Borel premise. This is the actual same-Sylow embedding input used for
Aschbacher–Smith 2.5.6, printed p.554, in the binary PSL₃ case.
-/

public section

open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry Subgroup
namespace Matrix.PSL3.LinearThree.UnipotentOvergroups
variable (F : Type*) [Field F]

local notation "e01" => SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide)
local notation "e12" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 2) (by decide)
local notation "e10" => SpecialLinearGroup.transvection (i := (1 : Fin 3)) (j := 0) (by decide)
local notation "e20" => SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 0) (by decide)
local notation "e21" => SpecialLinearGroup.transvection (i := (2 : Fin 3)) (j := 1) (by decide)

private theorem upper_val (u : U F) : (specialLinear F u).val = matrix F u := rfl

private theorem upper_mem (a b c : F) : specialLinear F ⟨a,b,c⟩ ∈ unipotentSL F :=
  (specialLinear_range F).le ⟨⟨a,b,c⟩, rfl⟩

private theorem upper_root_mem (i j : Fin 3) (hij : i < j) (t : F) :
    SpecialLinearGroup.transvection (ne_of_lt hij) t ∈ unipotentSL F := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · convert upper_mem F t 0 0 using 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe,upper_val,matrix]
  · convert upper_mem F 0 0 t using 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe,upper_val,matrix]
  · convert upper_mem F 0 t 0 using 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe,upper_val,matrix]

private theorem lower10_identity (t : F) :
    e10 t = e12 (1 : F) * e20 t * e12 (-1 : F) * e20 (-t) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem lower21_identity (t : F) :
    e21 t = e20 t * e01 (1 : F) * e20 (-t) * e01 (-1 : F) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

private theorem eq_top_of_lower20 (K : Subgroup SL(3,F)) (hU : unipotentSL F ≤ K)
    (h20 : ∀ t : F, e20 t ∈ K) : K = ⊤ := by
  have h10 (t : F) : e10 t ∈ K := by
    rw [lower10_identity]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hU (upper_root_mem F 1 2 (by decide) 1))
      (h20 t)) (hU (upper_root_mem F 1 2 (by decide) (-1)))) (h20 (-t))
  have h21 (t : F) : e21 t ∈ K := by
    rw [lower21_identity]
    exact K.mul_mem (K.mul_mem (K.mul_mem (h20 t)
      (hU (upper_root_mem F 0 1 (by decide) 1))) (h20 (-t)))
      (hU (upper_root_mem F 0 1 (by decide) (-1)))
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun g => g ∈ K) ?_ ?_ g
  · intro i j hij t
    by_cases hlt : i < j
    · exact hU (upper_root_mem F i j hlt t)
    · fin_cases i <;> fin_cases j <;> simp_all <;> exact (hij rfl).elim
  · exact fun _ _ => K.mul_mem

private theorem lower20_of_first_column (K : Subgroup SL(3,F))
    (hU : unipotentSL F ≤ K) (g : SL(3,F)) (hg : g ∈ K)
    (h00 : g.val 0 0 = 0) (h10 : g.val 1 0 = 0) (h20 : g.val 2 0 ≠ 0) (t : F) :
    e20 t ∈ K := by
  let u := specialLinear F ⟨t * g.val 0 1 / g.val 2 0, 0,
    t * g.val 0 2 / g.val 2 0⟩
  have he : g * u = e20 t * g := by
    apply Subtype.ext
    change g.val * matrix F _ = (e20 t).val * g.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_three, h00, h10] <;> field_simp
  have hu : u ∈ K := hU (upper_mem F _ _ _)
  have hc := K.mul_mem (K.mul_mem hg hu) (K.inv_mem hg)
  rwa [he, mul_inv_cancel_right] at hc

private theorem bottom_left_eq_zero (K : Subgroup SL(3,F))
    (hU : unipotentSL F ≤ K) (hK : K ≠ ⊤) (g : SL(3,F)) (hg : g ∈ K) :
    g.val 2 0 = 0 := by
  by_contra h20
  apply hK
  apply eq_top_of_lower20 F K hU
  let u := specialLinear F ⟨0, -g.val 1 0 / g.val 2 0, -g.val 0 0 / g.val 2 0⟩
  let w := u * g
  have hw : w ∈ K := K.mul_mem (hU (upper_mem F _ _ _)) hg
  have hw00 : w.val 0 0 = 0 := by
    simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply,
      Fin.sum_univ_three, h20]
  have hw10 : w.val 1 0 = 0 := by
    simp [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply,
      Fin.sum_univ_three, h20]
  have hw20 : w.val 2 0 ≠ 0 := by
    simpa [w, u, SpecialLinearGroup.coe_mul, upper_val, matrix, Matrix.mul_apply,
      Fin.sum_univ_three] using h20
  exact lower20_of_first_column F K hU w hw hw00 hw10 hw20

variable [Finite F]

/-- Every proper subgroup containing the full standard unipotent group fixes the
standard point or the standard line. -/
theorem overgroup_unipotentSL (K : Subgroup SL(3,F)) (hU : unipotentSL F ≤ K) (hK : K ≠ ⊤) :
    K ≤ pointParabolicSL F ∨ K ≤ lineParabolicSL F := by
  classical
  by_cases hp : K ≤ pointParabolicSL F
  · exact Or.inl hp
  · right
    obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hp
    have hg20 := bottom_left_eq_zero F K hU hK g hg
    have hg10 : g.val 1 0 ≠ 0 := by
      intro hz
      exact hgp ((mem_pointParabolicSL_iff F g).mpr ⟨hz, hg20⟩)
    intro h hh
    have hh20 := bottom_left_eq_zero F K hU hK h hh
    have hprod := bottom_left_eq_zero F K hU hK (h * g) (K.mul_mem hh hg)
    have hz : h.val 2 1 * g.val 1 0 = 0 := by
      simpa [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
        hg20, hh20] using hprod
    exact (mem_lineParabolicSL_iff F h).mpr ⟨hh20, (mul_eq_zero.mp hz).resolve_right hg10⟩

/-- Every proper projective unipotent overgroup lies in one of the two full
standard parabolics. -/
theorem overgroup_unipotent (K : Subgroup PSL(3,F)) (hU : unipotent F ≤ K) (hK : K ≠ ⊤) :
    K ≤ pointParabolic F ∨ K ≤ lineParabolic F := by
  have hpre : K.comap (projection F) ≠ ⊤ := by
    intro h
    apply hK
    rw [← map_comap_eq_self_of_surjective (projection_surjective F) K, h]
    exact map_top_of_surjective _ (projection_surjective F)
  have hUpre : unipotentSL F ≤ K.comap (projection F) := by
    intro g hg
    exact hU (mem_map_of_mem _ hg)
  rcases overgroup_unipotentSL F _ hUpre hpre with hp | hp
  · left
    simpa only [pointParabolic, lineParabolic,
      map_comap_eq_self_of_surjective (projection_surjective F)] using
      map_mono (f := projection F) hp
  · right
    simpa only [pointParabolic, lineParabolic,
      map_comap_eq_self_of_surjective (projection_surjective F)] using
      map_mono (f := projection F) hp

/-- The actual full Sylow hypothesis yields a conjugate point or line parabolic. -/
theorem proper_sylow_overgroup_parabolic_cover {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2^n)
    (Q : Sylow 2 PSL(3,F)) (K : Subgroup PSL(3,F))
    (hQK : (Q : Subgroup PSL(3,F)) ≤ K) (hK : K ≠ ⊤) :
    ∃ g : PSL(3,F), K.map (MulAut.conj g).toMonoidHom ≤ pointParabolic F ∨
      K.map (MulAut.conj g).toMonoidHom ≤ lineParabolic F := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) Q (unipotentSylow F hn hF)
  have hQ : (Q : Subgroup PSL(3,F)).map (MulAut.conj g).toMonoidHom = unipotent F :=
    congrArg Sylow.toSubgroup hg
  have hUK : unipotent F ≤ K.map (MulAut.conj g).toMonoidHom := hQ ▸ map_mono hQK
  have hp : K.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro htop
    apply hK
    apply top_unique
    intro x _
    apply (Subgroup.mem_map_iff_mem (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).mp
    rw [htop]
    trivial
  exact ⟨g,overgroup_unipotent F _ hUK hp⟩
end Matrix.PSL3.LinearThree.UnipotentOvergroups
