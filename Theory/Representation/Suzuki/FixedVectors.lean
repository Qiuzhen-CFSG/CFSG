module

public import Theory.Representation.Suzuki.NaturalMatrix

/-!
# No fixed vectors in the natural Suzuki module

The central root element u(0,1) forces the last two coordinates of a fixed
vector to vanish. The Weyl element interchanges the first and last pairs,
so the first two coordinates also vanish. This uses the literal matrix
representation and is valid even for the field of order two.

Source: Huppert--Blackburn, Finite Groups III, XI.3.1; Aschbacher--Smith,
10.1.1(7) and 10.1.2(5), printed pp.741--742.
-/

public noncomputable section
namespace Representation.SuzukiNatural
open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII Subgroup
noncomputable section

theorem natural_fixed_eq_zero (m : ℕ) (v : W m)
    (h : ∀ g, natural m g v = v) : v = 0 := by
  let u : SuzukiMatrixGroup m :=
    ⟨SuzukiRootGL m 0 1, subset_closure (Or.inl ⟨0,1,rfl⟩)⟩
  let w : SuzukiMatrixGroup m :=
    ⟨SuzukiWeylGL m, subset_closure (Or.inr (Or.inr rfl))⟩
  have hu : natural m u v = ![v 0 + v 2 + v 3,v 1 + v 3,v 2,v 3] := by
    ext i
    fin_cases i <;>
      simp [natural_apply,u,SuzukiRootGL,SuzukiRootMatrix,Matrix.mulVec,
        dotProduct,Fin.sum_univ_four,add_assoc]
  have hw : natural m w v = ![v 3,v 2,v 1,v 0] := by
    ext i
    fin_cases i <;>
      simp [natural_apply,w,SuzukiWeylGL,SuzukiWeylMatrix,Matrix.mulVec,
        dotProduct,Fin.sum_univ_four]
  have h3 : v 3 = 0 := by
    have hh := congrFun ((h u).symm.trans hu) 1
    simpa using (add_eq_left.mp hh.symm)
  have h2 : v 2 = 0 := by
    have hh := congrFun ((h u).symm.trans hu) 0
    have hh' : v 0 + v 2 = v 0 := by simpa [h3] using hh.symm
    exact add_eq_left.mp hh'
  have h0 : v 0 = 0 := by simpa [h3] using congrFun ((h w).symm.trans hw) 0
  have h1 : v 1 = 0 := by simpa [h2] using congrFun ((h w).symm.trans hw) 1
  ext i
  fin_cases i <;> assumption
end
end Representation.SuzukiNatural

