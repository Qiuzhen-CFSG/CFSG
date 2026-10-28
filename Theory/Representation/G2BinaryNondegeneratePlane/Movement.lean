module

public import Theory.Representation.G2BinaryNondegeneratePlane.Stabilizer

/-!
# The two cubic actions on the perpendicular four-space

The commuting cubic elements belong to the two actual SL₂(2) factors.
Each moves the full perpendicular four-space. Moreover the product stabilizer
acts faithfully on that space: the four tensor-coordinate basis vectors detect
both binary matrices. This proves the concrete action assertions immediately
before (*) in Aschbacher–Smith, Lemma 13.3.12, printed pp.889–890.
-/

@[expose] public noncomputable section
open Atlas.SplitOctonion Module Submodule Matrix
open scoped MatrixGroups
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Restricted.NaturalCoordinates Representation.BinaryOffender

def secondCubic : Model K := secondHom cubicMatrix
theorem secondCubic_action (v : W) :
    rho secondCubic v=![v 5,v 3,v 4,v 1+v 3,v 2+v 4,v 0+v 5] := by
  rw [secondCubic,secondHom_action]
  simp [cubicMatrix]
theorem orderOf_secondCubic : orderOf secondCubic=3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor
  · rw [secondCubic,←map_pow]
    have h : cubicMatrix^3=1 := by decide +kernel
    rw [h,map_one]
  · intro he
    have h := secondCubic_action firstVector
    rw [he,map_one] at h
    have hi := congrFun h 0
    exact one_ne_zero (show (1:K)=0 from hi)
theorem cubics_commute : Commute cubic secondCubic := factors_commute _ _

theorem secondCubic_moved_orthogonal (v : W) (hv : v∈form.orthogonal plane) :
    ∃w∈form.orthogonal plane,rho secondCubic w-w=v := by
  refine ⟨rho secondCubic v,?_,?_⟩
  · have h := (mem_orthogonal v).mp hv
    rw [secondCubic_action,mem_orthogonal]
    simp [h.1,h.2]
  · rw [secondCubic_action,secondCubic_action]
    ext i
    fin_cases i <;> simp

theorem firstCubic_moved_orthogonal (v : W) (hv : v∈form.orthogonal plane) :
    ∃w∈form.orthogonal plane,rho cubic w-w=v := by
  refine ⟨rho cubic v,?_,?_⟩
  · have h := (mem_orthogonal v).mp hv
    rw [cubic_action,mem_orthogonal]
    exact h
  · have h := (mem_orthogonal v).mp hv
    rw [cubic_action,cubic_action]
    ext i
    fin_cases i <;> simp [h.1,h.2]

private theorem binary_nonzero_eq_one (x : K) (h : x≠0) : x=1 := by
  exact (by decide : ∀x:K,x≠0→x=1) x h

theorem product_faithful_on_orthogonal (M N : SL(2,K))
    (h : ∀v∈form.orthogonal plane,rho (productHom (M,N)) v=v) : M=1 ∧ N=1 := by
  have h1 := h (Pi.single 1 1) ((mem_orthogonal _).mpr (by decide))
  have h2 := h (Pi.single 2 1) ((mem_orthogonal _).mpr (by decide))
  have h3 := h (Pi.single 3 1) ((mem_orthogonal _).mpr (by decide))
  simp only [productHom_apply,map_mul,Module.End.mul_apply,firstHom_action,secondHom_action] at h1 h2 h3
  have h00 : M.val 0 0*N.val 0 0=1 := by simpa using congrFun h1 1
  have hm00 : M.val 0 0=1 := binary_nonzero_eq_one _ (left_ne_zero_of_mul (by rw [h00];exact one_ne_zero))
  have hn00 : N.val 0 0=1 := binary_nonzero_eq_one _ (right_ne_zero_of_mul (by rw [h00];exact one_ne_zero))
  have hm10 : M.val 1 0=0 := by simpa [hn00] using congrFun h1 2
  have hm01 : M.val 0 1=0 := by simpa [hn00] using congrFun h2 1
  have hm11 : M.val 1 1=1 := by simpa [hn00] using congrFun h2 2
  have hn10 : N.val 1 0=0 := by simpa [hm00] using congrFun h1 3
  have hn01 : N.val 0 1=0 := by simpa [hm00] using congrFun h3 1
  have hn11 : N.val 1 1=1 := by simpa [hm00] using congrFun h3 3
  constructor
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm00,hm01,hm10,hm11]
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hn00,hn01,hn10,hn11]

theorem stabilizer_faithful_on_orthogonal (g : Model K)
    (hg : g∈subspaceStabilizer rho plane)
    (h : ∀v∈form.orthogonal plane,rho g v=v) : g=1 := by
  obtain ⟨⟨M,N⟩,he⟩ := (productHom_range ▸ hg : g∈productHom.range)
  obtain ⟨rfl,rfl⟩ := product_faithful_on_orthogonal M N (he ▸ h)
  simpa using he.symm
end Atlas.G2.Natural.BinaryNondegeneratePlane
