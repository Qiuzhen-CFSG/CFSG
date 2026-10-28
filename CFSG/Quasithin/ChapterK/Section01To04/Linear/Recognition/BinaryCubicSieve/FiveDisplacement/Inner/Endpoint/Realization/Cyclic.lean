module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization.Cyclic.Geometry
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Realization.Cyclic.Coordinates

/-!
# The marked SL₅ endpoint cyclic map

A vector satisfying the two endpoint highest-vector relations receives a
unique prescribed image of E₀₄ under the constructed intertwiner from the
literal trace-zero matrix representation. Incident rank-one matrices and
the two active root relations give its action table. The coordinate map
therefore intertwines four adjacent exchanges and one transvection;
conjugating that transvection supplies all roots and hence all of SL₅(2).

The map sends E₀₄ exactly to the given vector. Its construction needs only
`LocalHighestVector`; the finite-dimensional, faithful, irreducible source
application is consequently an immediate specialization. The downstream
`Endpoint.Realization.exists_equiv_of_cyclicMap` retains the assembly of
the normalized equivalence and the endpoint displacement estimate.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author
manuscript, Lemma 4.5 step 2, pp.23–24. This is a direct finite-group proof
of the local-relation recognition needed for the source's adjoint case.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Representation
open Representation.SL5TenDimensional.Classification
open Representation.SL5TenDimensional.Classification.Separated
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
private def conjugatorWord : Fin 5 → Fin 5 → List (Fin 4) :=
  ![![[], [], [1], [2, 1], [3, 2, 1]],
    ![[0], [], [0, 1], [2, 0, 1], [3, 2, 0, 1]],
    ![[1, 0], [0, 1, 0], [], [1, 2, 0, 1], [3, 1, 2, 0, 1]],
    ![[2, 1, 0], [2, 0, 1, 0], [1, 2, 0, 1, 0], [], [2, 3, 1, 2, 0, 1]],
    ![[3, 2, 1, 0], [3, 2, 0, 1, 0], [3, 1, 2, 0, 1, 0], [2, 3, 1, 2, 0, 1, 0], []]]

private theorem transvection_conjugate (a b : Fin 5) (hab : a ≠ b) :
    Matrix.SpecialLinearGroup.transvection hab (1 : ZMod 2) =
      swapWord (conjugatorWord a b) * generator 4 *
        swapWord (conjugatorWord a b).reverse := by
  revert a b hab
  decide +kernel

private theorem generators_induction (P : Group → Prop) (hone : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b))
    (hgen : ∀ k, P (generator k)) (g : Group) : P g := by
  have hs (i : Fin 4) : P (simpleSwap i) := by
    fin_cases i
    · exact hgen 0
    · exact hgen 1
    · exact hgen 2
    · exact hgen 3
  have hw (w : List (Fin 4)) : P (swapWord w) := by
    induction w with
    | nil => exact hone
    | cons i w ih => exact hmul _ _ (hs i) ih
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' P g
  · intro i j hij c hc
    have hc1 : c = 1 := (show ∀ c : ZMod 2, c ≠ 0 → c = 1 by decide) c hc
    subst c
    have hd : Matrix.SpecialLinearGroup.diag2n hij (1 : ZMod 2) hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe]
    rw [hd]
    exact hone
  · intro i j hij c
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
    · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using hone
    · rw [transvection_conjugate]
      exact hmul _ _ (hmul _ _ (hw _) (hgen 4)) (hw _)
  · exact hmul

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

theorem linearMap_generator (h : LocalHighestVector σ {0, 3} v) (k : Fin 5) :
    (linearMap σ v).comp (SL5Adjoint.action (generator k)) =
      (σ (generator k)).comp (linearMap σ v) := by
  apply ext_basis
  intro b
  change linearMap σ v (SL5Adjoint.action (generator k) (basisVector b)) =
    σ (generator k) (linearMap σ v (basisVector b))
  rw [action_basis, linearMap_basis, image_action h]
  simp only [map_list_sum, List.map_map, Function.comp_def, linearMap_basis]

theorem linearMap_equivariant (h : LocalHighestVector σ {0, 3} v) (g : Group)
    (X : SL5Adjoint.Space) :
    linearMap σ v (SL5Adjoint.action g X) = σ g (linearMap σ v X) := by
  have hall := generators_induction
    (fun g => ∀ X, linearMap σ v (SL5Adjoint.action g X) = σ g (linearMap σ v X))
    (by intro X; simp)
    (by intro a b ha hb X; rw [apply_mul, ha, hb, apply_mul])
    (fun k X => LinearMap.congr_fun (linearMap_generator h k) X) g
  exact hall X

/-- The marked cyclic map from the literal trace-zero matrix representation. -/
def cyclicMap (h : LocalHighestVector σ {0, 3} v) :
    IntertwiningMap SL5Adjoint.action σ where
  toLinearMap := linearMap σ v
  isIntertwining' g := by
    ext X
    exact linearMap_equivariant h g X

/-- The cyclic map has the prescribed highest vector, with no rescaling. -/
theorem cyclicMap_highestRoot (h : LocalHighestVector σ {0, 3} v) :
    cyclicMap h SL5Adjoint.highestRoot = v := by
  change linearMap σ v SL5Adjoint.highestRoot = v
  rw [highestRoot_basis, linearMap_basis, imageVector_highest]

/-- Endpoint relations construct the actual SL₅ intertwiner. In particular this
applies to every finite-dimensional faithful irreducible target in the source
endpoint contract; none of those extra restrictions is needed for the map. -/
theorem exists_cyclicMap (h : LocalHighestVector σ {0, 3} v) :
    ∃ f : IntertwiningMap SL5Adjoint.action σ, f SL5Adjoint.highestRoot = v :=
  ⟨cyclicMap h, cyclicMap_highestRoot h⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Cyclic
