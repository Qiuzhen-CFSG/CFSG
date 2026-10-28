module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.PairModel
public import Theory.GroupTheory.PrimeRankAutomorphismOrder

/-!
# The common centralizer of the regular pair in GL₅(2)

Commutation with the published `regularS` and `regularT` determines the
second, third and fourth columns from the first. Their common fixed space
restricts the fifth column, and invertibility forces both remaining diagonal
entries to be one. Thus the common centralizer consists exactly of the matrices

```
1 0 0 0 0
a 1 0 0 0
b 0 1 0 0
c b a 1 d
e 0 0 0 1
```

with five binary parameters. We construct every such linear equivalence,
prove that these coordinates are unique, and obtain order 32. The elements
with only `d = 1` and only `e = 1` do not commute. Consequently every
abelian subgroup is proper, and the common centralizer has two-rank at most
four. This calculation does not require a normal form for arbitrary pairs.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
H.9.2(3), printed pp.390–391 (PDF pp.401–402). This is the concrete
centralizer step in the alternative linear-algebra proof of actor placement.
-/

namespace BinaryNaturalDual.FiveActors.Classification

private def axis (i : Fin 5) : X := Pi.single i 1

private theorem binary (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z
  decide

private def modelFun (p : X) (x : X) : X :=
  ![x 0, p 0 * x 0 + x 1, p 1 * x 0 + x 2,
    p 2 * x 0 + p 1 * x 1 + p 0 * x 2 + x 3 + p 3 * x 4,
    p 4 * x 0 + x 4]

-- Inverting the displayed matrix replaces c by c + de.
private def invParam (p : X) : X := ![p 0, p 1, p 2 + p 3 * p 4, p 3, p 4]

private def model (p : X) : G where
  toFun := modelFun p
  invFun := modelFun (invParam p)
  left_inv x := by
    ext i
    fin_cases i <;> simp [modelFun, invParam] <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 from rfl]
  right_inv x := by
    ext i
    fin_cases i <;> simp [modelFun, invParam] <;> ring_nf <;> simp [show (2 : ZMod 2) = 0 from rfl]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [modelFun] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [modelFun] <;> ring

private theorem model_mem (p : X) : model p ∈ regularCentralizer := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · ext x i
    fin_cases i <;> simp [regularS, model, modelFun, LinearEquiv.mul_apply] <;> ring
  · rcases Set.mem_singleton_iff.mp hg with rfl
    ext x i
    fin_cases i <;> simp [regularT, model, modelFun, LinearEquiv.mul_apply] <;> ring

-- All restrictions below follow from commutation and injectivity.
private theorem columns (g : regularCentralizer) :
    ∃ p : X, (g : G) = model p := by
  have hs (x : X) : g.val (regularS x) = regularS (g.val x) := by
    have h := Subgroup.mem_centralizer_iff.mp g.property regularS (by simp)
    exact (LinearEquiv.congr_fun h x).symm
  have ht (x : X) : g.val (regularT x) = regularT (g.val x) := by
    have h := Subgroup.mem_centralizer_iff.mp g.property regularT (by simp)
    exact (LinearEquiv.congr_fun h x).symm
  have h1 : g.val (axis 1) =
      ![0, (g.val (axis 0)) 0, 0, (g.val (axis 0)) 2, 0] := by
    have h := hs (axis 0)
    rw [show regularS (axis 0) = axis 0 + axis 1 by decide, map_add] at h
    have hh := eq_sub_of_add_eq' h
    rw [hh]
    ext i
    fin_cases i <;> simp [regularS]
  have h2 : g.val (axis 2) =
      ![0, 0, (g.val (axis 0)) 0, (g.val (axis 0)) 1, 0] := by
    have h := ht (axis 0)
    rw [show regularT (axis 0) = axis 0 + axis 2 by decide, map_add] at h
    have hh := eq_sub_of_add_eq' h
    rw [hh]
    ext i
    fin_cases i <;> simp [regularT]
  have h3 : g.val (axis 3) = ![0, 0, 0, (g.val (axis 0)) 0, 0] := by
    have h := hs (axis 2)
    rw [show regularS (axis 2) = axis 2 + axis 3 by decide, map_add] at h
    have hh := eq_sub_of_add_eq' h
    rw [hh, h2]
    ext i
    fin_cases i <;> simp [regularS]
  -- The fourth column cannot vanish.
  have hk : (g.val (axis 0)) 0 = 1 := by
    rcases binary ((g.val (axis 0)) 0) with hk | hk
    · have hz : g.val (axis 3) = g.val 0 := by
        rw [h3, hk, map_zero]
        ext i
        fin_cases i <;> rfl
      have := g.val.injective hz
      have hne : axis 3 ≠ 0 := by decide
      exact (hne this).elim
    · exact hk
  have h40 : (g.val (axis 4)) 0 = 0 := by
    have h := congrFun (hs (axis 4)) 1
    rw [show regularS (axis 4) = axis 4 by decide] at h
    change (g.val (axis 4)) 1 = (g.val (axis 4)) 1 + (g.val (axis 4)) 0 at h
    exact add_eq_left.mp h.symm
  have h41 : (g.val (axis 4)) 1 = 0 := by
    have h := congrFun (ht (axis 4)) 3
    rw [show regularT (axis 4) = axis 4 by decide] at h
    change (g.val (axis 4)) 3 = (g.val (axis 4)) 3 + (g.val (axis 4)) 1 at h
    exact add_eq_left.mp h.symm
  have h42 : (g.val (axis 4)) 2 = 0 := by
    have h := congrFun (hs (axis 4)) 3
    rw [show regularS (axis 4) = axis 4 by decide] at h
    change (g.val (axis 4)) 3 = (g.val (axis 4)) 3 + (g.val (axis 4)) 2 at h
    exact add_eq_left.mp h.symm
  have h4 : g.val (axis 4) =
      ![0, 0, 0, (g.val (axis 4)) 3, (g.val (axis 4)) 4] := by
    ext i
    fin_cases i <;> simp [h40, h41, h42]
  -- The fifth column cannot be a multiple of the fourth.
  have hf : (g.val (axis 4)) 4 = 1 := by
    rcases binary ((g.val (axis 4)) 4) with hf | hf
    · have hz : g.val (axis 4) = g.val ((g.val (axis 4)) 3 • axis 3) := by
        rw [map_smul, h3, hk, h4, hf]
        ext i
        fin_cases i <;> simp [axis]
      have hz4 := congrFun (g.val.injective hz) 4
      simp [axis] at hz4
    · exact hf
  refine ⟨![(g.val (axis 0)) 1, (g.val (axis 0)) 2, (g.val (axis 0)) 3,
    (g.val (axis 4)) 3, (g.val (axis 0)) 4], ?_⟩
  apply (Pi.basisFun (ZMod 2) (Fin 5)).ext'
  intro i
  simp only [Pi.basisFun_apply]
  change g.val (axis i) = _
  fin_cases i
  · ext j
    fin_cases j <;> simp [model, modelFun, axis]
    exact hk
  · rw [hk] at h1
    simpa [model, modelFun, axis] using h1
  · rw [hk] at h2
    simpa [model, modelFun, axis] using h2
  · rw [hk] at h3
    simpa [model, modelFun, axis] using h3
  · rw [hf] at h4
    simpa [model, modelFun, axis] using h4

private def parameters (g : G) : X :=
  ![(g (axis 0)) 1, (g (axis 0)) 2, (g (axis 0)) 3,
    (g (axis 4)) 3, (g (axis 0)) 4]

private theorem parameters_model (p : X) : parameters (model p) = p := by
  ext i
  fin_cases i <;> simp [parameters, model, modelFun, axis]

private def modelElement (p : X) : regularCentralizer := ⟨model p, model_mem p⟩

private noncomputable def modelEquiv : X ≃ regularCentralizer := Equiv.ofBijective modelElement (by
  constructor
  · intro p q h
    have hh := congrArg (fun g : regularCentralizer => parameters g.val) h
    simpa only [modelElement, parameters_model] using hh
  · intro g
    obtain ⟨p, hp⟩ := columns g
    exact ⟨p, Subtype.ext hp.symm⟩)

/-- The five binary coordinates give the exact centralizer order. -/
public theorem regularCentralizer_card : Nat.card regularCentralizer = 32 := by
  rw [← Nat.card_congr modelEquiv]
  change Nat.card (Fin 5 → ZMod 2) = 32
  simp [Nat.card_eq_fintype_card]

open scoped IsMulCommutative

/-- The two off-block shears in the d and e positions do not commute. -/
public theorem regularCentralizer_not_isMulCommutative : ¬ IsMulCommutative regularCentralizer := by
  intro hc
  let := hc
  have h := mul_comm (modelElement ![0, 0, 0, 1, 0]) (modelElement ![0, 0, 0, 0, 1])
  have he := congrArg (fun g : regularCentralizer => g.val (axis 0) 3) h
  change (1 : ZMod 2) = 0 at he
  exact one_ne_zero he

/-- The concrete common centralizer cannot contain an elementary subgroup of rank five. -/
public theorem regularCentralizer_primeRank_le_four : primeRank 2 regularCentralizer ≤ 4 := by
  apply Theory.GroupTheory.primeRank_le_of_noncommutative_card_prime_pow
  · simpa using regularCentralizer_card
  · exact regularCentralizer_not_isMulCommutative

end BinaryNaturalDual.FiveActors.Classification
