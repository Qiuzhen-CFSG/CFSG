module

public import Theory.LinearAlgebra.AlternatingPlane
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.BinaryIrreducibility.NaturalForm
public import Theory.AtlasPort.LinearGroups.G2.PairStabilizer
public import Theory.Representation.G2NaturalFaithfulness
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# A nondegenerate plane in the binary natural G₂ module

The octonion norm polar form gives an alternating nondegenerate form on the
literal six-space. The plane on the two opposite basis vectors is nondegenerate.
An explicit order-three element in its pointwise SL₂(2) stabilizer fixes exactly
this plane and moves its full four-dimensional orthogonal complement.

Source: Aschbacher–Smith, Lemma 13.3.12, printed pp.889–890, especially (*).
The imported split-octonion model retains its ATLAS attribution.
-/

@[expose] public noncomputable section
open Atlas.SplitOctonion Module Submodule Matrix
open scoped MatrixGroups
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Restricted.NaturalCoordinates
abbrev K := ZMod 2
abbrev W := Fin 6 → K
abbrev rho := Atlas.G2.Restricted.NaturalCoordinates.action K
noncomputable def form : LinearMap.BilinForm K W :=
  LinearMap.BilinForm.congr (equiv K) (InvariantPolar.form K)
theorem form_apply (v w : W) :
    form v w=v 0*w 5+v 5*w 0+v 1*w 4+v 4*w 1+v 2*w 3+v 3*w 2 := by
  simp [form, LinearMap.BilinForm.congr_apply, InvariantPolar.form,
    normPolar, representative]
theorem form_alternating : form.IsAlt := fun x => InvariantPolar.form_alternating K ((equiv K).symm x)
theorem form_nondegenerate : form.Nondegenerate :=
  (InvariantPolar.form_nondegenerate K).congr (equiv K)
def firstVector : W := ![1,0,0,0,0,0]
def secondVector : W := ![0,0,0,0,0,1]
def plane : Submodule K W := span K {firstVector,secondVector}
theorem form_first_second : form firstVector secondVector=1 := by
  simp [form_apply,firstVector,secondVector]
theorem plane_geometry : finrank K plane=2 ∧ (form.restrict plane).Nondegenerate :=
  form.span_pair_nondegenerate_of_pairing_ne_zero form_alternating firstVector secondVector
    (form_first_second ▸ one_ne_zero)
theorem mem_plane (v : W) : v∈plane ↔ v 1=0 ∧ v 2=0 ∧ v 3=0 ∧ v 4=0 := by
  rw [plane,mem_span_pair]
  constructor
  · rintro ⟨a,b,rfl⟩
    simp [firstVector,secondVector]
  · rintro ⟨h1,h2,h3,h4⟩
    refine ⟨v 0,v 5,?_⟩
    ext i
    fin_cases i <;> simp [firstVector,secondVector,h1,h2,h3,h4]
theorem mem_orthogonal (v : W) : v∈form.orthogonal plane ↔ v 0=0 ∧ v 5=0 := by
  constructor
  · intro hv
    have h0 := hv firstVector (subset_span (by simp : firstVector∈({firstVector,secondVector}:Set W)))
    have h5 := hv secondVector (subset_span (by simp : secondVector∈({firstVector,secondVector}:Set W)))
    constructor
    · simpa [form_apply,firstVector,secondVector] using h5
    · simpa [form_apply,firstVector,secondVector] using h0
  · rintro ⟨h0,h5⟩ u hu
    have h := (mem_plane u).mp hu
    simp [form_apply,h0,h5,h.1,h.2.1,h.2.2.1,h.2.2.2]
theorem finrank_orthogonal : finrank K (form.orthogonal plane)=4 := by
  rw [form.finrank_orthogonal form_nondegenerate,plane_geometry.1]
  simp

def cubicMatrix : SL(2,K) := ⟨!![0,1;1,1],by decide⟩
def cubic : Model K := PairStabilizer.blockHom cubicMatrix
theorem cubic_action (v : W) : rho cubic v=![v 0,v 2,v 1+v 2,v 4,v 3+v 4,v 5] := by
  ext i
  fin_cases i <;> simp [action_apply,cubic,PairStabilizer.blockHom,PairStabilizer.blockEquiv,
    PairStabilizer.blockLinear,cubicMatrix,Atlas.G2.Restricted.NaturalCoordinates.projection,representative,traceZeroAction_val,
    CharTwo.neg_eq]
theorem cubic_cubed : cubic^3=1 := by
  rw [cubic,←map_pow]
  have h : cubicMatrix^3=1 := by decide +kernel
  rw [h,map_one]
theorem cubic_ne_one : cubic≠1 := by
  intro h
  have hh := cubic_action (![0,1,0,0,0,0] : W)
  rw [h,map_one] at hh
  have he := congrFun hh 1
  exact one_ne_zero (show (1:K)=0 from he)
theorem orderOf_cubic : orderOf cubic=3 :=
  orderOf_eq_prime_iff.mpr ⟨cubic_cubed,cubic_ne_one⟩
theorem cubic_fixes_plane (v : W) (hv : v∈plane) : rho cubic v=v := by
  have h := (mem_plane v).mp hv
  rw [cubic_action]
  ext i
  fin_cases i <;> simp [h.1,h.2.1,h.2.2.1,h.2.2.2]
theorem cubic_fixed_iff (v : W) : rho cubic v=v ↔ v∈plane := by
  constructor
  · intro h
    rw [cubic_action] at h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three] at h1 h2 h3 h4
    apply (mem_plane v).mpr
    have hv1 : v 1=0 := add_right_cancel (h2.trans (zero_add _).symm)
    have hv3 : v 3=0 := add_right_cancel (h4.trans (zero_add _).symm)
    exact ⟨hv1,h1.trans hv1,hv3,h3.trans hv3⟩
  · exact cubic_fixes_plane v

theorem cubic_moved_range : LinearMap.range (rho cubic-1)=form.orthogonal plane := by
  apply le_antisymm
  · rintro v ⟨u,rfl⟩
    apply (mem_orthogonal _).mpr
    simp [cubic_action]
  · intro v hv
    have h := (mem_orthogonal v).mp hv
    refine ⟨![0,v 2,v 1+v 2,v 4,v 3+v 4,0],?_⟩
    ext i
    fin_cases i <;> simp [cubic_action,h.1,h.2]

end Atlas.G2.Natural.BinaryNondegeneratePlane
