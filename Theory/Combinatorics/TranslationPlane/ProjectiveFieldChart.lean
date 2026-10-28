module
public import Theory.Combinatorics.TranslationPlane.Coordinates

/-!
# The affine chart of the coordinate projective plane

The map t ↦ [t₀:t₁:1] is an equivalence onto the complement of z=0.
The affine line b+Fv has covector [-v₁:v₀:b₀v₁-b₁v₀]. Its incidence
equation is proved over an arbitrary field, without characteristic or
cardinality restrictions. These literal native coordinates are used to
complete the source translation-plane chart in the centerfree A₂ branch
of DGS, Groups and Graphs, 10.5 and Theorem D, pp.156,224.
-/

@[expose] public noncomputable section
namespace Configuration.TranslationPlane.FieldChart
open Matrix Projectivization
variable (F : Type*) [Field F]
abbrev PG := Projectivization F (Fin 3 → F)

/-- The covector z=0 defining the line at infinity. -/
def axis : PG F := mk F ![0,0,1] (by simp)

/-- The standard affine point [x:y:1]. -/
def point (t : Fin 2 → F) : PG F := mk F ![t 0,t 1,1] (by simp)

theorem point_not_mem_axis (t : Fin 2 → F) : point F t ∉ axis F := by
  simp [point,axis,ofField.mem_iff,orthogonal_mk,dotProduct,Fin.sum_univ_three]

theorem point_injective : Function.Injective (point F) := by
  intro a b he
  obtain ⟨r,hr⟩ := (mk_eq_mk_iff' F _ _ _ _).mp he
  have hr1 : r = 1 := by simpa using congrFun hr 2
  ext i
  fin_cases i
  · simpa [hr1] using (congrFun hr 0).symm
  · simpa [hr1] using (congrFun hr 1).symm

theorem exists_point (p : PG F) (hp : p ∉ axis F) : ∃ t, point F t = p := by
  induction p using Projectivization.ind with | h v hv =>
  have hv2 : v 2 ≠ 0 := by
    simpa [axis,ofField.mem_iff,orthogonal_mk,dotProduct,Fin.sum_univ_three] using hp
  refine ⟨![v 0 / v 2,v 1 / v 2],?_⟩
  symm
  apply (mk_eq_mk_iff' F _ _ _ _).mpr
  refine ⟨v 2,?_⟩
  ext i
  fin_cases i <;> simp [hv2,div_eq_mul_inv,mul_comm,mul_left_comm]

/-- The standard affine chart, on the actual projectivization. -/
def chart : (Fin 2 → F) ≃ {p : PG F // p ∉ axis F} :=
  Equiv.ofBijective (fun t => ⟨point F t,point_not_mem_axis F t⟩)
    ⟨fun _ _ he => point_injective F (congrArg Subtype.val he),fun p => by
      obtain ⟨t,ht⟩ := exists_point F p p.property
      exact ⟨t,Subtype.ext ht⟩⟩

@[simp] theorem chart_apply (t : Fin 2 → F) : (chart F t).val = point F t := rfl

theorem lineVector_ne_zero (b v : Fin 2 → F) (hv : v ≠ 0) :
    ![-v 1,v 0,b 0 * v 1 - b 1 * v 0] ≠ 0 := by
  intro he
  apply hv
  ext i
  fin_cases i
  · simpa using congrFun he 1
  · simpa using congrFun he 0

/-- The covector of the affine field line b+Fv. -/
def fieldLine (b v : Fin 2 → F) (hv : v ≠ 0) : PG F :=
  mk F ![-v 1,v 0,b 0 * v 1 - b 1 * v 0] (lineVector_ne_zero F b v hv)

private theorem lineEquation (b v t : Fin 2 → F) (hv : v ≠ 0) :
    t 0 * (-v 1) + t 1 * v 0 + (b 0 * v 1 - b 1 * v 0) = 0 ↔
      ∃ r : F, t = b + r • v := by
  constructor
  · intro ht
    have hrel : (t 1 - b 1) * v 0 = (t 0 - b 0) * v 1 := by
      apply sub_eq_zero.mp
      calc
        _ = t 0 * (-v 1) + t 1 * v 0 + (b 0 * v 1 - b 1 * v 0) := by ring
        _ = 0 := ht
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro h
        apply hv
        ext i
        fin_cases i <;> simp [hv0,h]
      have hd0 : t 0 - b 0 = 0 := by
        have hh := hrel
        rw [hv0] at hh
        simp only [mul_zero] at hh
        exact (mul_eq_zero.mp hh.symm).resolve_right hv1
      refine ⟨(t 1 - b 1) / v 1,?_⟩
      ext i
      fin_cases i
      · simp [sub_eq_zero.mp hd0,hv0]
      · change t 1 = b 1 + (t 1 - b 1) / v 1 * v 1
        rw [div_mul_cancel₀ _ hv1]
        ring
    · refine ⟨(t 0 - b 0) / v 0,?_⟩
      ext i
      fin_cases i
      · change t 0 = b 0 + (t 0 - b 0) / v 0 * v 0
        rw [div_mul_cancel₀ _ hv0]
        ring
      · have hh : t 1 - b 1 = ((t 0 - b 0) / v 0) * v 1 := by
          calc
            t 1 - b 1 = ((t 1 - b 1) * v 0) / v 0 := by rw [mul_div_cancel_right₀ _ hv0]
            _ = ((t 0 - b 0) * v 1) / v 0 := by rw [hrel]
            _ = ((t 0 - b 0) / v 0) * v 1 := by ring
        change t 1 = b 1 + (t 0 - b 0) / v 0 * v 1
        rw [←hh]
        ring
  · rintro ⟨r,rfl⟩
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring

/-- The full affine incidence equation of the native projective line. -/
theorem point_mem_fieldLine_iff (b v : Fin 2 → F) (hv : v ≠ 0) (t : Fin 2 → F) :
    point F t ∈ fieldLine F b v hv ↔ ∃ r : F, t = b + r • v := by
  simpa [point,fieldLine,ofField.mem_iff,orthogonal_mk,dotProduct,Fin.sum_univ_three] using
    lineEquation F b v t hv

theorem fieldLine_ne_axis (b v : Fin 2 → F) (hv : v ≠ 0) :
    fieldLine F b v hv ≠ axis F := by
  intro he
  have hb : point F b ∈ fieldLine F b v hv :=
    (point_mem_fieldLine_iff F b v hv b).mpr ⟨0,by simp⟩
  exact point_not_mem_axis F b (he ▸ hb)
end Configuration.TranslationPlane.FieldChart
