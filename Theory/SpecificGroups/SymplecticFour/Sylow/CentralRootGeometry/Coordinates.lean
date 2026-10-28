module

public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.ElementaryAbelian.Basic
/-!
# Coordinates and the center of the symplectic Sylow group

The product of the four actual positive root matrices has four independent
entries. The known Sylow order makes this injection surjective. Multiplication
then identifies the center with roots 0 and 4 and gives the square formula.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2]
def element (b u w v : F) : unipotent (F := F) :=
  ⟨rootElement 6 b * rootElement 0 (u + b*w) * rootElement 4 w * rootElement 2 v,
    mul_mem (mul_mem (mul_mem (positive_root_mem_unipotent 6 b (by simp))
      (positive_root_mem_unipotent 0 _ (by simp)))
      (positive_root_mem_unipotent 4 w (by simp)))
      (positive_root_mem_unipotent 2 v (by simp))⟩
theorem element_matrix (b u w v : F) :
    (element b u w v).val.val = fromBlocks !![1,b;0,1]
      !![u,w+b*v;w,v] 0 !![1,0;b,1] := by
  change rootMatrix 6 b * rootMatrix 0 (u+b*w) * rootMatrix 4 w * rootMatrix 2 v = _
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, CharTwo.neg_eq,
      CharTwo.add_self_eq_zero, add_assoc] <;>
    (ring_nf; all_goals simp [CharTwo.two_eq_zero])

theorem element_injective : Function.Injective (fun x : F × F × F × F =>
    element x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  intro x y h
  have hh := congrArg (fun g : unipotent (F := F) => g.val.val) h
  rw [element_matrix, element_matrix] at hh
  have h1 := congrArg (fun M => M (.inl 0) (.inl 1)) hh
  have h2 := congrArg (fun M => M (.inl 0) (.inr 0)) hh
  have h3 := congrArg (fun M => M (.inl 1) (.inr 0)) hh
  have h4 := congrArg (fun M => M (.inl 1) (.inr 1)) hh
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
theorem element_surjective [Finite F] : Function.Surjective (fun x : F × F × F × F =>
    element x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr ⟨element_injective, ?_⟩ |>.surjective
  simp only [Nat.card_prod, card_unipotent]
  ring

theorem element_mul (b u w v c z t a : F) :
    element b u w v * element c z t a =
    element (b+c) (u+z+b*t+w*c+b*v*c) (w+t+v*c) (v+a) := by
  apply Subtype.ext
  apply Subtype.ext
  change (element b u w v).val.val * (element c z t a).val.val = _
  rw [element_matrix, element_matrix, element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;>
    (ring_nf; all_goals simp [CharTwo.two_eq_zero])


theorem element_eq_iff (b u w v c z t a : F) :
    element b u w v = element c z t a ↔ b=c ∧ u=z ∧ w=t ∧ v=a := by
  constructor
  · intro h
    have he : (b,u,w,v) = (c,z,t,a) := element_injective h
    exact ⟨congrArg Prod.fst he, congrArg (fun x => x.2.1) he,
      congrArg (fun x => x.2.2.1) he, congrArg (fun x => x.2.2.2) he⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rfl

omit [CharP F 2] in
theorem element_zero : element (0:F) 0 0 0 = 1 := by
  apply Subtype.ext
  simp [element, RootSubgroup.element_zero]

def theta (s t : F) : unipotent (F := F) := element 0 s t 0

omit [CharP F 2] in
theorem theta_val (s t : F) : (theta s t).val = rootElement 0 s * rootElement 4 t := by
  simp [theta, element, RootSubgroup.element_zero]

theorem theta_add (s t u v : F) : theta s t * theta u v = theta (s+u) (t+v) := by
  simp [theta, element_mul]

def thetaHom : (Multiplicative F × Multiplicative F) →* unipotent (F := F) where
  toFun x := theta x.1.toAdd x.2.toAdd
  map_one' := element_zero
  map_mul' _ _ := (theta_add _ _ _ _).symm

theorem theta_injective : Function.Injective (thetaHom (F := F)) := by
  intro x y h
  have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp h
  exact Prod.ext (congrArg Multiplicative.ofAdd hh.2.1)
    (congrArg Multiplicative.ofAdd hh.2.2.1)

theorem theta_mem_center [Finite F] (s t : F) : theta s t ∈ center (unipotent (F := F)) := by
  apply mem_center_iff.mpr
  intro x
  obtain ⟨⟨b,u,w,v⟩, rfl⟩ := element_surjective x
  simp only [theta, element_mul]
  congr 1 <;> simp [add_comm, add_left_comm, add_assoc,
    mul_comm, CharTwo.add_self_eq_zero]

theorem mem_center_iff_coordinates [Finite F] (b u w v : F) :
    element b u w v ∈ center (unipotent (F := F)) ↔ b = 0 ∧ v = 0 := by
  constructor
  · intro h
    have h1 := mem_center_iff.mp h (element 0 0 0 1)
    have h2 := mem_center_iff.mp h (element 1 0 0 0)
    simp only [element_mul, element_eq_iff] at h1 h2
    constructor
    · have hh := h1.2.2.1
      simpa using hh
    · have hh := h2.2.2.1
      simpa using hh.symm
  · rintro ⟨rfl,rfl⟩
    exact theta_mem_center u w

theorem theta_range [Finite F] : (thetaHom (F := F)).range = center (unipotent (F := F)) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact theta_mem_center _ _
  · intro hx
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    obtain ⟨rfl,rfl⟩ := (mem_center_iff_coordinates b u w v).mp hx
    exact ⟨(Multiplicative.ofAdd u, Multiplicative.ofAdd w),rfl⟩

theorem element_square (b u w v : F) : (element b u w v)^2 = theta (b^2*v) (b*v) := by
  rw [pow_two, element_mul]
  apply (element_eq_iff _ _ _ _ _ _ _ _).mpr
  simp only [CharTwo.add_self_eq_zero, zero_add, add_assoc]
  constructor
  · trivial
  constructor
  · ring_nf
    simp [CharTwo.two_eq_zero]
  constructor
  · simp [mul_comm, add_comm, add_left_comm, CharTwo.add_self_eq_zero]
  · trivial

/-- The center with its actual inclusion in the standard unipotent subgroup. -/
noncomputable def centerEquiv [Finite F] :
    (Multiplicative F × Multiplicative F) ≃* center (unipotent (F := F)) :=
  (MonoidHom.ofInjective theta_injective).trans (MulEquiv.subgroupCongr theta_range)

theorem centerEquiv_val [Finite F] (x : Multiplicative F × Multiplicative F) :
    (centerEquiv x).val = thetaHom x := rfl

/-- The two-root plane embedded in the actual symplectic matrix group. -/
noncomputable def parameter : (Multiplicative F × Multiplicative F) →* Sp F :=
  (unipotent (F := F)).subtype.comp thetaHom

theorem parameter_apply (x : Multiplicative F × Multiplicative F) :
    parameter x = rootElement 0 x.1.toAdd * rootElement 4 x.2.toAdd := theta_val _ _

theorem parameter_injective : Function.Injective (parameter (F := F)) :=
  Subtype.val_injective.comp theta_injective

theorem parameter_range [Finite F] : (parameter (F := F)).range =
    (center (unipotent (F := F))).map (unipotent (F := F)).subtype := by
  rw [parameter, MonoidHom.range_comp, theta_range]

theorem center_elementary [Finite F] : IsElementaryAbelian 2 (center (unipotent (F := F))) := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ?_ }
  intro x
  obtain ⟨a, rfl⟩ := (centerEquiv (F := F)).surjective x
  apply Subtype.ext
  change (theta a.1.toAdd a.2.toAdd)^2 = 1
  rw [theta, element_square]
  simpa [theta] using (element_zero (F := F))
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
