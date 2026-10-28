module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourDiagonal

/-!
# The two concrete simple root intersections in SU₄

Intersect the upper-unitriangular Sylow with its conjugate by the longest
Weyl element times each simple reflection. The resulting matrices are
exactly the additive F root at positions (0,1),(2,3), and the additive
fixed-field root at (1,2), respectively. The Hermitian equation in the
first intersection is retained through the existing radical coordinates.
The actual injective SU₄ projection transfers both descriptions to PSU₄.

Consequently an automorphism preserving the native Sylow and fixing the
two marked reflections preserves these actual simple root subgroups.
This is the intrinsic root-extraction step for the direct apartment route
of Aschbacher–Smith F.4.10,16–17, pp.279,282–283. Pointwise root fixation
and root generation remain separate obligations.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRoots
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourSylow UnitaryFourPointLocal UnitaryFourPointQuotient
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "U" => upper F σ hσ

def shortRoot (x : F) : SU F J := radicalElement F σ hσ ⟨0,x,0,by simp⟩
def longRoot (x : FixedField F σ) : SU F J :=
  (leviSL F σ hσ (SpecialLinearGroup.upperUnipotentHom (FixedField F σ) (Multiplicative.ofAdd x))).val

def shortOpp : SU F J := reverse F σ hσ*pairSwap F σ hσ
def longOpp : SU F J := reverse F σ hσ*middleSwap F σ hσ

private theorem shortOpp_val : (shortOpp F σ hσ).val.val=
    !![0,0,1,0;0,0,0,1;1,0,0,0;0,1,0,0] := by
  change (reverse F σ hσ).val.val*(pairSwap F σ hσ).val.val=_
  rw [reverse_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram,pairSwap,pairSwapMatrix,involutionElement,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem longOpp_val : (longOpp F σ hσ).val.val=
    !![0,0,0,1;0,1,0,0;0,0,1,0;1,0,0,0] := by
  change (reverse F σ hσ).val.val*(middleSwap F σ hσ).val.val=_
  rw [reverse_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram,middleSwap,middleSwapMatrix,involutionElement,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem shortOpp_inv : (shortOpp F σ hσ)⁻¹=shortOpp F σ hσ := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change (shortOpp F σ hσ).val.val*(shortOpp F σ hσ).val.val=1
  rw [shortOpp_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

private theorem longOpp_inv : (longOpp F σ hσ)⁻¹=longOpp F σ hσ := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  apply Units.ext
  change (longOpp F σ hσ).val.val*(longOpp F σ hσ).val.val=1
  rw [longOpp_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_succ]

theorem short_intersection (g : SU F J) (hg : g∈U)
    (hw : shortOpp F σ hσ*g*(shortOpp F σ hσ)⁻¹∈U) :
    g=shortRoot F σ hσ (g.val.val 2 3) := by
  obtain ⟨ht,hd⟩ := (mem_upper_iff_entries F σ hσ g).mp hg
  have ht' := ((mem_upper_iff_entries F σ hσ _).mp hw).1
  rw [shortOpp_inv] at ht'
  have h02 := ht' 2 0 (by decide)
  have h03 := ht' 2 1 (by decide)
  have h12 := ht' 3 0 (by decide)
  have h13 := ht' 3 1 (by decide)
  change ((shortOpp F σ hσ).val.val*g.val.val*(shortOpp F σ hσ).val.val) 2 0=0 at h02
  change ((shortOpp F σ hσ).val.val*g.val.val*(shortOpp F σ hσ).val.val) 2 1=0 at h03
  change ((shortOpp F σ hσ).val.val*g.val.val*(shortOpp F σ hσ).val.val) 3 0=0 at h12
  change ((shortOpp F σ hσ).val.val*g.val.val*(shortOpp F σ hσ).val.val) 3 1=0 at h13
  simp [shortOpp_val,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] at h02 h03 h12 h13
  have hl : g∈localSU F J := ((mem_upper F σ hσ g).mp hg).1
  let u : radical F σ hσ := ⟨⟨g,hl⟩,(mem_radical F σ hσ _).mpr
    ⟨hd 1,h12,ht 2 1 (by decide),hd 2⟩⟩
  have h01 : g.val.val 0 1=σ (g.val.val 2 3) := (radical_entries F σ hσ u).1
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortRoot,radicalElement,radicalMatrix,h01,h02,h03,h12,h13,hd,
      ht 1 0 (by decide),ht 2 0 (by decide),ht 3 0 (by decide),ht 2 1 (by decide),
      ht 3 1 (by decide),ht 3 2 (by decide)]

theorem long_intersection (g : SU F J) (hg : g∈U)
    (hw : longOpp F σ hσ*g*(longOpp F σ hσ)⁻¹∈U) :
    ∃ x : FixedField F σ, g=longRoot F σ hσ x := by
  obtain ⟨ht,hd⟩ := (mem_upper_iff_entries F σ hσ g).mp hg
  have ht' := ((mem_upper_iff_entries F σ hσ _).mp hw).1
  rw [longOpp_inv] at ht'
  have h01 := ht' 3 1 (by decide)
  have h02 := ht' 3 2 (by decide)
  have h03 := ht' 3 0 (by decide)
  have h13 := ht' 1 0 (by decide)
  have h23 := ht' 2 0 (by decide)
  change ((longOpp F σ hσ).val.val*g.val.val*(longOpp F σ hσ).val.val) 3 1=0 at h01
  change ((longOpp F σ hσ).val.val*g.val.val*(longOpp F σ hσ).val.val) 3 2=0 at h02
  change ((longOpp F σ hσ).val.val*g.val.val*(longOpp F σ hσ).val.val) 3 0=0 at h03
  change ((longOpp F σ hσ).val.val*g.val.val*(longOpp F σ hσ).val.val) 1 0=0 at h13
  change ((longOpp F σ hσ).val.val*g.val.val*(longOpp F σ hσ).val.val) 2 0=0 at h23
  simp [longOpp_val,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ] at h01 h02 h03 h13 h23
  have hl : g∈localSU F J := ((mem_upper F σ hσ g).mp hg).1
  let u : localSU F J := ⟨g,hl⟩
  have hu : middleSL F σ hσ u∈SpecialLinearGroup.upperUnipotent (FixedField F σ) := by
    apply (mem_localUpper F σ hσ u).mpr
    exact ⟨hd 1,ht 2 1 (by decide),hd 2⟩
  obtain ⟨x,hx⟩ := (SpecialLinearGroup.mem_upperUnipotent (FixedField F σ) _).mp hu
  have hv := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) (middleSL_val F σ hσ u)
  rw [←hx] at hv
  have hx' : (x : F)=g.val.val 1 2 := by
    simpa [SpecialLinearGroup.transvection_coe,middleBlock,u] using hv
  refine ⟨x,?_⟩
  apply Subtype.ext
  apply Units.ext
  change g.val.val=(leviSL F σ hσ _).val.val.val
  rw [leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,
      leviMatrix,hx',h01,h02,h03,h13,h23,hd,
      ht 1 0 (by decide),ht 2 0 (by decide),ht 3 0 (by decide),ht 2 1 (by decide),
      ht 3 1 (by decide),ht 3 2 (by decide)]
omit [Finite F] in
theorem shortRoot_mem_upper (x : F) : shortRoot F σ hσ x∈U :=
  radicalElement_mem_upper F σ hσ _

omit [Finite F] in
theorem longRoot_mem_upper (x : FixedField F σ) : longRoot F σ hσ x∈U := by
  apply (mem_upper F σ hσ _).mpr
  refine ⟨(leviSL F σ hσ _).property,?_⟩
  simp [longRoot,leviSL_val,leviMatrix,SpecialLinearGroup.upperUnipotentHom,
    SpecialLinearGroup.transvection_coe]

private theorem shortRoot_conj (x : F) :
    shortOpp F σ hσ*shortRoot F σ hσ x*(shortOpp F σ hσ)⁻¹=shortRoot F σ hσ (σ x) := by
  rw [shortOpp_inv]
  apply Subtype.ext
  apply Units.ext
  change (shortOpp F σ hσ).val.val*(shortRoot F σ hσ x).val.val*(shortOpp F σ hσ).val.val=_
  rw [shortOpp_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortRoot,radicalElement,radicalMatrix,Matrix.mul_apply,
      Fin.sum_univ_succ,hσ x]

private theorem longRoot_conj (x : FixedField F σ) :
    longOpp F σ hσ*longRoot F σ hσ x*(longOpp F σ hσ)⁻¹=longRoot F σ hσ x := by
  rw [longOpp_inv]
  apply Subtype.ext
  apply Units.ext
  change (longOpp F σ hσ).val.val*(leviSL F σ hσ _).val.val.val*(longOpp F σ hσ).val.val=
    (leviSL F σ hσ _).val.val.val
  rw [longOpp_val,leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMatrix,SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply,Fin.sum_univ_succ]

theorem projective_short_intersection (g : PSU F J) (hg : g∈(U).map (project F J))
    (hw : project F J (shortOpp F σ hσ)*g*(project F J (shortOpp F σ hσ))⁻¹∈
      (U).map (project F J)) : ∃ x, g=project F J (shortRoot F σ hσ x) := by
  obtain ⟨z,hz,rfl⟩ := hg
  have hw' : shortOpp F σ hσ*z*(shortOpp F σ hσ)⁻¹∈U := by
    apply (mem_map_iff_mem (project_injective F J)).mp
    simpa only [map_mul,map_inv] using hw
  exact ⟨_,congrArg (project F J) (short_intersection F σ hσ z hz hw')⟩

theorem projective_long_intersection (g : PSU F J) (hg : g∈(U).map (project F J))
    (hw : project F J (longOpp F σ hσ)*g*(project F J (longOpp F σ hσ))⁻¹∈
      (U).map (project F J)) : ∃ x, g=project F J (longRoot F σ hσ x) := by
  obtain ⟨z,hz,rfl⟩ := hg
  have hw' : longOpp F σ hσ*z*(longOpp F σ hσ)⁻¹∈U := by
    apply (mem_map_iff_mem (project_injective F J)).mp
    simpa only [map_mul,map_inv] using hw
  obtain ⟨x,hx⟩ := long_intersection F σ hσ z hz hw'
  exact ⟨x,congrArg (project F J) hx⟩

/-- Automorphisms preserving the native Sylow and the two marked reflections
preserve the actual short simple root subgroup. -/
theorem preserves_projective_shortRoot (a : MulAut (PSU F J))
    (hU : ∀ g∈(U).map (project F J), a g∈(U).map (project F J))
    (hs : a (project F J (middleSwap F σ hσ))=project F J (middleSwap F σ hσ))
    (ht : a (project F J (pairSwap F σ hσ))=project F J (pairSwap F σ hσ)) (x : F) :
    ∃ y, a (project F J (shortRoot F σ hσ x))=project F J (shortRoot F σ hσ y) := by
  apply projective_short_intersection F σ hσ
  · exact hU _ ⟨_,shortRoot_mem_upper F σ hσ x,rfl⟩
  · have hw : a (project F J (shortOpp F σ hσ))=project F J (shortOpp F σ hσ) := by
      simp only [shortOpp,reverse,map_mul,hs,ht]
    have h := hU _ (show project F J (shortOpp F σ hσ*shortRoot F σ hσ x*
      (shortOpp F σ hσ)⁻¹)∈(U).map (project F J) from
      ⟨_,by rw [shortRoot_conj]; exact shortRoot_mem_upper F σ hσ _,rfl⟩)
    simpa only [map_mul,map_inv,hw] using h

/-- The same intrinsic intersection gives the actual long simple root. -/
theorem preserves_projective_longRoot (a : MulAut (PSU F J))
    (hU : ∀ g∈(U).map (project F J), a g∈(U).map (project F J))
    (hs : a (project F J (middleSwap F σ hσ))=project F J (middleSwap F σ hσ))
    (ht : a (project F J (pairSwap F σ hσ))=project F J (pairSwap F σ hσ)) (x : FixedField F σ) :
    ∃ y, a (project F J (longRoot F σ hσ x))=project F J (longRoot F σ hσ y) := by
  apply projective_long_intersection F σ hσ
  · exact hU _ ⟨_,longRoot_mem_upper F σ hσ x,rfl⟩
  · have hw : a (project F J (longOpp F σ hσ))=project F J (longOpp F σ hσ) := by
      simp only [longOpp,reverse,map_mul,hs,ht]
    have h := hU _ (show project F J (longOpp F σ hσ*longRoot F σ hσ x*
      (longOpp F σ hσ)⁻¹)∈(U).map (project F J) from
      ⟨_,by rw [longRoot_conj]; exact longRoot_mem_upper F σ hσ _,rfl⟩)
    simpa only [map_mul,map_inv,hw] using h
end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRoots
