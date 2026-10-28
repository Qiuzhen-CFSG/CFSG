module

public import Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap.Contracts
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.CentralModule
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index

/-!
# The plane-local image of a maximum elementary subgroup

Let `A` be an elementary abelian subgroup of order `q³` in the actual
symplectic plane local. If `a ∈ A` lies outside the radical, commutativity
embeds the kernel of `Plane.quotientMap` on `A` into the symmetric matrices
fixed by congruence with `Plane.quotientMap a`.

Symmetric two by two matrices form a three-dimensional space. In
characteristic two, congruence by a nonidentity matrix is nonidentity:
its values on the two diagonal matrix units recover the squares of all
four matrix entries, and squaring is injective. Thus the fixed space has
dimension at most two and the kernel has order at most `q²`. The exact
kernel-image cardinality formula gives an image of order at least `q`.

This proves the published `PlaneImageBound` contract without a geometric
or rank premise. It supplies the plane calculation in the intrinsic
symplectic rank-gap route to Aschbacher--Smith E.1.14(1), printed p.214,
citing [Asc82a], Lemma 4.7. The actual local matrix coordinates underlie
F.1.12(I)(2), printed pp.262--264. The rank-one core calculation and final
source-theorem assembly belong to the parent module.
-/

public section

open Matrix
open Theory.SpecificGroups.SymplecticFour.Plane

namespace Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap
noncomputable section
variable {F : Type*} [Field F]

private def coordinates : symmetricMatrices F ≃ₗ[F] (F × F × F) where
  toFun B := (B.val 0 0, B.val 0 1, B.val 1 1)
  invFun v := ⟨!![v.1, v.2.1; v.2.1, v.2.2], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  left_inv B := by
    apply Subtype.ext
    ext i j
    have hs : B.val 1 0 = B.val 0 1 := congrFun (congrFun B.property 0) 1
    fin_cases i <;> fin_cases j <;> simp [hs]
  right_inv v := by rcases v with ⟨a, b, c⟩; rfl
  map_add' B C := rfl
  map_smul' t B := rfl

private def action (g : SpecialLinearGroup (Fin 2) F) :
    symmetricMatrices F →ₗ[F] symmetricMatrices F where
  toFun := congruence g
  map_add' B C := by
    apply Subtype.ext
    change g.val * (B.val + C.val) * g.valᵀ = _
    simp [mul_add, add_mul, congruence]
  map_smul' t B := by
    apply Subtype.ext
    change g.val * (t • B.val) * g.valᵀ = _
    simp [congruence]

private def fixedSpace (g : SpecialLinearGroup (Fin 2) F) :
    Submodule F (symmetricMatrices F) := (action g - LinearMap.id).ker

private theorem mem_fixedSpace (g : SpecialLinearGroup (Fin 2) F)
    (B : symmetricMatrices F) : B ∈ fixedSpace g ↔ congruence g B = B := by
  change congruence g B - B = 0 ↔ _
  exact sub_eq_zero

private theorem fixedSpace_ne_top [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (hg : g ≠ 1) : fixedSpace g ≠ ⊤ := by
  intro h
  have hf (B : symmetricMatrices F) : congruence g B = B :=
    (mem_fixedSpace g B).mp (h ▸ Submodule.mem_top)
  let B₀ : symmetricMatrices F := coordinates.symm (1, 0, 0)
  let B₁ : symmetricMatrices F := coordinates.symm (0, 0, 1)
  have h₀ (i : Fin 2) := congrArg (fun B : symmetricMatrices F => B.val i i) (hf B₀)
  have h₁ (i : Fin 2) := congrArg (fun B : symmetricMatrices F => B.val i i) (hf B₁)
  have h00 : g.val 0 0 ^ 2 = 1 := by simpa [congruence_diagonal, B₀, coordinates] using h₀ 0
  have h10 : g.val 1 0 ^ 2 = 0 := by simpa [congruence_diagonal, B₀, coordinates] using h₀ 1
  have h01 : g.val 0 1 ^ 2 = 0 := by simpa [congruence_diagonal, B₁, coordinates] using h₁ 0
  have h11 : g.val 1 1 ^ 2 = 1 := by simpa [congruence_diagonal, B₁, coordinates] using h₁ 1
  apply hg
  apply Subtype.ext
  ext i j
  apply CharTwo.sq_injective
  fin_cases i <;> fin_cases j
  · change g.val 0 0 ^ 2 = (1 : F) ^ 2
    simpa only [one_pow] using h00
  · change g.val 0 1 ^ 2 = (0 : F) ^ 2
    simpa only [zero_pow (by decide : 2 ≠ 0)] using h01
  · change g.val 1 0 ^ 2 = (0 : F) ^ 2
    simpa only [zero_pow (by decide : 2 ≠ 0)] using h10
  · change g.val 1 1 ^ 2 = (1 : F) ^ 2
    simpa only [one_pow] using h11

private theorem card_fixedSpace_le [Finite F] [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (hg : g ≠ 1) :
    Nat.card (fixedSpace g) ≤ Nat.card F ^ 2 := by
  have hd : Module.finrank F (symmetricMatrices F) = 3 := by
    rw [coordinates.finrank_eq]
    simp [Module.finrank_prod]
  have hlt := Submodule.finrank_lt (fixedSpace_ne_top hg)
  rw [hd] at hlt
  rw [Module.natCard_eq_pow_finrank (K := F)]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

private theorem card_kernel_le [Finite F] [CharP F 2]
    (A : Subgroup (planeLocal (F := F))) [IsElementaryAbelian 2 A]
    (a : planeLocal (F := F)) (ha : a ∈ A) (hra : a ∉ radical) :
    Nat.card (quotientMap.comp A.subtype).ker ≤ Nat.card F ^ 2 := by
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let π := quotientMap.comp A.subtype
  have hqa : quotientMap a ≠ 1 := hra
  let coordinate (x : π.ker) : radical (F := F) := ⟨x.val.val, x.property⟩
  have fixed (x : π.ker) :
      congruence (quotientMap a) (radicalEquiv (coordinate x)).toAdd =
        (radicalEquiv (coordinate x)).toAdd := by
    have hc : conjugate a (coordinate x) = coordinate x := by
      apply Subtype.ext
      change a * x.val.val * a⁻¹ = x.val.val
      have hcomm : a * x.val.val = x.val.val * a :=
        congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) x.val)
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [← radicalEquiv_conjugate, hc]
  let embedding : π.ker → fixedSpace (quotientMap a) := fun x =>
    ⟨(radicalEquiv (coordinate x)).toAdd, (mem_fixedSpace _ _).mpr (fixed x)⟩
  have hinj : Function.Injective embedding := by
    intro x y h
    have he : (radicalEquiv (coordinate x)).toAdd =
        (radicalEquiv (coordinate y)).toAdd := congrArg Subtype.val h
    have hq : coordinate x = coordinate y :=
      radicalEquiv.injective (Multiplicative.toAdd.injective he)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : radical (F := F) => q.val) hq
  exact (Nat.card_le_card_of_injective embedding hinj).trans (card_fixedSpace_le hqa)

/-- A maximum elementary subgroup of the actual determinant-one plane local
lies in the radical or has at least `|F|` elements in its literal SL₂ image.
This holds over every finite field of characteristic two, including the binary field. -/
theorem planeImageBound [Finite F] [CharP F 2] : PlaneImageBound F := by
  intro A hA horder
  let _ : IsElementaryAbelian 2 A := hA
  by_cases hrad : A ≤ radical
  · exact Or.inl hrad
  · right
    obtain ⟨a, ha, hra⟩ : ∃ a, a ∈ A ∧ a ∉ radical := by
      exact SetLike.not_le_iff_exists.mp hrad
    let π := quotientMap.comp A.subtype
    have hker : Nat.card π.ker ≤ Nat.card F ^ 2 := card_kernel_le A a ha hra
    have hrange : π.range = A.map quotientMap := by
      dsimp [π]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcount := π.ker.card_mul_index
    rw [Subgroup.index_ker, hrange, horder] at hcount
    have hle : Nat.card F ^ 2 * Nat.card F ≤
        Nat.card F ^ 2 * Nat.card (A.map quotientMap) := by
      calc
        _ = Nat.card F ^ 3 := by ring
        _ = Nat.card π.ker * Nat.card (A.map quotientMap) := hcount.symm
        _ ≤ _ := Nat.mul_le_mul_right _ hker
    exact Nat.le_of_mul_le_mul_left hle (pow_pos Nat.card_pos 2)

end
end Theory.SpecificGroups.SymplecticFour.ElementaryCoreRankGap
