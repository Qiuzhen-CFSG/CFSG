module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial
public import Theory.Frattini.SquareImage
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A characteristic elementary subgroup of the binary unitary-four Sylow

The last simple-root coordinate maps the standard Sylow group onto the
additive full field. Its kernel is the additive group `K × F × K`, where
`K` is the fixed subfield. Squares belong to this kernel, and it is abelian.
Conversely, commuting with the explicit squares of root words forces the
last coordinate to vanish, by nondegeneracy of the field trace pairing.
Thus the kernel is exactly the centralizer of the Frattini subgroup and
is characteristic. This is the subgroup on which Sylow automorphisms induce
the norm-plane root normalizer action.

Source: Aschbacher--Smith, F.1.11 and F.1.12(I)(6), printed pp.262--264,
and the Sylow-restriction application in 4.4.10--11, printed p.621.
-/

open Matrix BenderSuzuki.MatrixGroups Subgroup
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "U" => localUpper F σ hσ
local notation "K" => FixedBy.subfield F σ

def shear (t : K) : U :=
  ⟨leviSL F σ hσ (SpecialLinearGroup.transvection zero_ne_one t), by
    change middleSL F σ hσ _ ∈ SpecialLinearGroup.upperUnipotent K
    rw [middleSL_leviSL]
    exact ⟨Multiplicative.ofAdd t,rfl⟩⟩

def element (c : RadicalCoordinates F σ) (t : K) : U :=
  inclusion (radical_le_localUpper F σ hσ) (radicalOfCoordinates F σ hσ c) *
    shear F σ hσ t

theorem element_matrix (c : RadicalCoordinates F σ) (t : K) :
    (element F σ hσ c t).val.val.val.val =
      !![1,σ c.y,σ c.x+(t:F)*σ c.y,c.z; 0,1,t,c.x; 0,0,1,c.y; 0,0,0,1] := by
  change radicalMatrix F σ c * (leviSL F σ hσ _).val.val.val = _
  rw [leviSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, leviMatrix, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_comm, add_comm]

theorem exists_element (u : U) :
    ∃ c : RadicalCoordinates F σ, ∃ t : K, u = element F σ hσ c t := by
  obtain ⟨t,ht⟩ := (SpecialLinearGroup.mem_upperUnipotent _ _).mp u.property
  let r : radical F σ hσ := ⟨u.val * (shear F σ hσ t).val⁻¹, by
    rw [← middleSL_ker]
    change middleSL F σ hσ (u.val * _) = 1
    rw [map_mul,map_inv]
    change middleSL F σ hσ u.val *
      (middleSL F σ hσ (leviSL F σ hσ _))⁻¹ = 1
    rw [middleSL_leviSL,ht,mul_inv_cancel]⟩
  obtain ⟨c,hc⟩ := (radicalCoordinatesEquiv F σ hσ).surjective r
  refine ⟨c,t,?_⟩
  apply Subtype.ext
  change u.val = (radicalOfCoordinates F σ hσ c).val * (shear F σ hσ t).val
  change radicalOfCoordinates F σ hσ c = r at hc
  rw [hc]
  change u.val = (u.val * (shear F σ hσ t).val⁻¹) * (shear F σ hσ t).val
  group

theorem last_mul (a b : U) :
    (a*b).val.val.val.val 2 3 = a.val.val.val.val 2 3 + b.val.val.val.val 2 3 := by
  obtain ⟨c,t,rfl⟩ := exists_element F σ hσ a
  obtain ⟨d,u,rfl⟩ := exists_element F σ hσ b
  change ((element F σ hσ c t).val.val.val.val *
    (element F σ hσ d u).val.val.val.val) 2 3 = _
  rw [element_matrix,element_matrix]
  simp [Matrix.mul_apply,Fin.sum_univ_succ,add_comm]

def lastHom : U →* Multiplicative F where
  toFun u := Multiplicative.ofAdd (u.val.val.val.val 2 3)
  map_one' := rfl
  map_mul' a b := congrArg Multiplicative.ofAdd (last_mul F σ hσ a b)

def elementaryKernel : Subgroup U := (lastHom F σ hσ).ker

@[simp] theorem mem_elementaryKernel (u : U) :
    u ∈ elementaryKernel F σ hσ ↔ u.val.val.val.val 2 3 = 0 := Iff.rfl

def elementaryElement (v : K × F × K) : U :=
  element F σ hσ ⟨v.2.1,0,v.2.2,by
    have hv : σ (v.2.2 : F) = v.2.2 := v.2.2.property
    simp [hv,CharTwo.add_self_eq_zero]⟩ v.1

theorem elementaryElement_matrix (v : K × F × K) :
    (elementaryElement F σ hσ v).val.val.val.val =
      !![1,0,σ v.2.1,v.2.2; 0,1,v.1,v.2.1; 0,0,1,0; 0,0,0,1] := by
  rw [elementaryElement,element_matrix]
  simp

theorem elementaryElement_mem (v : K × F × K) :
    elementaryElement F σ hσ v ∈ elementaryKernel F σ hσ := by
  rw [mem_elementaryKernel,elementaryElement_matrix]
  rfl

def elementaryHom : Multiplicative (K × F × K) →* elementaryKernel F σ hσ where
  toFun v := ⟨elementaryElement F σ hσ v.toAdd,elementaryElement_mem F σ hσ _⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    apply Units.ext
    rw [elementaryElement_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' v w := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    apply Units.ext
    change (elementaryElement F σ hσ (v.toAdd+w.toAdd)).val.val.val.val =
      (elementaryElement F σ hσ v.toAdd).val.val.val.val *
        (elementaryElement F σ hσ w.toAdd).val.val.val.val
    rw [elementaryElement_matrix,elementaryElement_matrix,elementaryElement_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply,Fin.sum_univ_succ,add_comm]

theorem elementaryHom_bijective : Function.Bijective (elementaryHom F σ hσ) := by
  constructor
  · intro v w h
    have hm := congrArg (fun a : elementaryKernel F σ hσ => a.val.val.val.val.val) h
    change (elementaryElement F σ hσ v.toAdd).val.val.val.val =
      (elementaryElement F σ hσ w.toAdd).val.val.val.val at hm
    rw [elementaryElement_matrix,elementaryElement_matrix] at hm
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun M => M 1 2) hm
    · apply Prod.ext
      · exact congrArg (fun M => M 1 3) hm
      · apply Subtype.ext
        exact congrArg (fun M => M 0 3) hm
  · intro a
    obtain ⟨c,t,hc⟩ := exists_element F σ hσ a.val
    have hy : c.y = 0 := by
      have ha := a.property
      rw [mem_elementaryKernel,hc,element_matrix] at ha
      exact ha
    have hz : σ c.z = c.z := by
      have h := c.trace_eq
      rw [hy] at h
      simpa using (CharTwo.add_eq_zero.mp (by simpa using h)).symm
    refine ⟨Multiplicative.ofAdd (t,c.x,⟨c.z,hz⟩),?_⟩
    apply Subtype.ext
    change elementaryElement F σ hσ _ = a.val
    rw [hc]
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [elementaryElement_matrix,element_matrix,hy]
    simp

def elementaryEquiv : Multiplicative (K × F × K) ≃* elementaryKernel F σ hσ :=
  MulEquiv.ofBijective (elementaryHom F σ hσ) (elementaryHom_bijective F σ hσ)

theorem elementaryKernel_comm (a b : elementaryKernel F σ hσ) : a*b=b*a := by
  obtain ⟨v,rfl⟩ := (elementaryEquiv F σ hσ).surjective a
  obtain ⟨w,rfl⟩ := (elementaryEquiv F σ hσ).surjective b
  rw [←map_mul,←map_mul,mul_comm]

theorem frattini_le_elementaryKernel [Finite F] : frattini U ≤ elementaryKernel F σ hσ := by
  apply Theory.GroupTheory.frattini_le_ker_of_square_image
  intro a
  rw [pow_two]
  apply Multiplicative.toAdd.injective
  change (lastHom F σ hσ a).toAdd + (lastHom F σ hσ a).toAdd = 0
  exact CharTwo.add_self_eq_zero _

def rootWord (y : F) : U := element F σ hσ ⟨0,y,0,by simp⟩ 1

theorem rootWord_square_matrix (y : F) :
    (rootWord F σ hσ y ^ 2).val.val.val.val =
      !![1,0,σ y,σ y*y; 0,1,0,y; 0,0,1,0; 0,0,0,1] := by
  rw [pow_two]
  change (element F σ hσ _ _).val.val.val.val *
    (element F σ hσ _ _).val.val.val.val = _
  rw [element_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_succ,CharTwo.add_self_eq_zero]

theorem elementaryKernel_eq_centralizer_frattini [Finite F] (hnt : ∃ u,σ u ≠ u) :
    elementaryKernel F σ hσ = centralizer (frattini U : Set U) := by
  apply le_antisymm
  · intro a ha
    apply mem_centralizer_iff.mpr
    intro b hb
    exact congrArg Subtype.val (elementaryKernel_comm F σ hσ
      ⟨b,frattini_le_elementaryKernel F σ hσ hb⟩ ⟨a,ha⟩)
  · intro a ha
    obtain ⟨c,t,rfl⟩ := exists_element F σ hσ a
    rw [mem_elementaryKernel,element_matrix]
    have hp (y : F) : σ c.y * y = σ y * c.y := by
      have hsq : rootWord F σ hσ y ^ 2 ∈ frattini U := by
        have hU : IsPGroup 2 U := (localSylow F σ hσ).isPGroup'
        rw [hU.frattini_eq_closure_squares]
        exact subset_closure ⟨rootWord F σ hσ y,rfl⟩
      have he := congrArg (fun u : U => u.val.val.val.val 0 3)
        ((mem_centralizer_iff.mp ha) _ hsq)
      change ((rootWord F σ hσ y ^ 2).val.val.val.val *
          (element F σ hσ c t).val.val.val.val) 0 3 =
        ((element F σ hσ c t).val.val.val.val *
          (rootWord F σ hσ y ^ 2).val.val.val.val) 0 3 at he
      rw [element_matrix,rootWord_square_matrix] at he
      simp [Matrix.mul_apply,Fin.sum_univ_succ] at he
      linear_combination -he
    obtain ⟨v,hv⟩ := hnt
    have hc : σ c.y = c.y := by simpa using hp 1
    have he : (σ v-v)*c.y=0 := by
      have h := hp v
      rw [hc] at h
      linear_combination -h
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hv)

theorem elementaryKernel_characteristic [Finite F] (hnt : ∃ u,σ u ≠ u) :
    (elementaryKernel F σ hσ).Characteristic := by
  rw [elementaryKernel_eq_centralizer_frattini F σ hσ hnt]
  infer_instance

theorem centralizer_elementaryKernel_le [Finite F] (hnt : ∃ u,σ u ≠ u) :
    centralizer (elementaryKernel F σ hσ : Set U) ≤ elementaryKernel F σ hσ := by
  rw [elementaryKernel_eq_centralizer_frattini F σ hσ hnt]
  apply centralizer_le
  rw [← elementaryKernel_eq_centralizer_frattini F σ hσ hnt]
  exact frattini_le_elementaryKernel F σ hσ

end Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure
