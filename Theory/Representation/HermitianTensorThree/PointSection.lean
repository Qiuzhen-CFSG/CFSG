module
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.Representation.BinaryOffender.RestrictionComparison
import all Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# The central point of the field-four Hermitian module

The nonzero vector fixed by a Sylow two-subgroup is, after conjugation
by an actual inner image element, the first diagonal matrix. Its stabilizer
in the SL₃ cover is the full point parabolic: the diagonal entries of its
image force the lower first-column entries to vanish, and the norm of every
nonzero element of F₄ is one.

This supplies the literal point marking for the involution centralizer in
Aschbacher–Smith H.4.6(4) and 8.2.11, printed pp.382 and 722,
refs/quasithin.pdf. The internal import reuses the established Sylow image
and its exact unipotent map, without changing that module's public boundary.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.HermitianTensorThree.PointSection
local instance : Finite (Space 1 ≃ₗ[ZMod 2] Space 1) :=
  Finite.of_injective (fun e : Space 1 ≃ₗ[ZMod 2] Space 1 => (e : Space 1 → Space 1))
    DFunLike.coe_injective

/-- The nonzero vector of the standard Sylow-fixed line over F₂. -/
@[expose] def pointVector : Space 1 :=
  (coordinates 1).symm (![1,0,0],![0,0,0])

theorem pointVector_ne_zero : pointVector ≠ 0 := by
  intro h
  have hh := congrArg (fun X : Space 1 => X.val 0 0) h
  exact one_ne_zero hh

private theorem point_fixed_eq (X : Space 1)
    (hX : X ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.point 1))
    (hne : X ≠ 0) : X = pointVector := by
  let e := UnipotentRadicals.pointFixedCoordinates 1
  let a : F 1 := e ⟨X,hX⟩
  have ha : a ≠ 0 := by
    intro h
    apply hne
    exact congrArg Subtype.val (e.injective
      (h.trans (show e ⟨0,Submodule.zero_mem _⟩ = 0 from rfl).symm))
  have he : a.val^2 = a.val := a.property
  have h1 : a.val = 1 := (eq_zero_or_one_of_sq_eq_self he).resolve_left
    (fun hz => ha (Subtype.ext hz))
  have he := e.symm_apply_apply ⟨X,hX⟩
  change e.symm a = ⟨X,hX⟩ at he
  have ha1 : a = 1 := Subtype.ext h1
  rw [ha1] at he
  exact (congrArg Subtype.val he).symm

/-- An actual Sylow-fixed nonzero vector can be marked by an inner image actor. -/
theorem sylow_fixed_marking (S : Sylow 2 (binaryImage 1)) (X : Space 1)
    (hX : X ∈ fixedSpace (overgroupAction 1 (binaryImage 1)) S) (hne : X ≠ 0) :
    ∃ c : binaryImage 1, c.val X = pointVector := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq (binaryImage 1)
    (UnipotentRadicals.imageSylow 1) S
  have hf : g.val.symm X ∈ fixedSpace (UnipotentRadicals.ambientAction 1)
      (UnipotentRadicals.point 1) := by
    intro a
    have ha : a.val ∈ (UnipotentRadicals.unipotentHom 1).range := map_le_range _ _ a.property
    rw [←UnipotentRadicals.imageSylow_map] at ha
    obtain ⟨b,hb,hba⟩ := ha
    have hgb : g*b*g⁻¹ ∈ (g • UnipotentRadicals.imageSylow 1 : Sylow 2 (binaryImage 1)) :=
      mem_map_of_mem (MulAut.conj g).toMonoidHom hb
    have hh := hX ⟨g*b*g⁻¹,hgb⟩
    change g.val (b.val (g.val.symm X)) = X at hh
    change a.val (g.val.symm X) = g.val.symm X
    rw [←hba]
    exact g.val.injective (hh.trans (g.val.apply_symm_apply X).symm)
  have hn : g.val.symm X ≠ 0 := fun hz => hne
    (by simpa only [map_zero,LinearEquiv.apply_symm_apply] using congrArg g.val hz)
  exact ⟨g⁻¹, point_fixed_eq _ hf hn⟩

private theorem norm_one (d : E 1) (hd : d ≠ 0) : d * sigma 1 d = 1 := by
  let : Fintype (E 1) := Fintype.ofFinite _
  have hh := FiniteField.pow_card_sub_one_eq_one d hd
  have hc : Fintype.card (E 1) = 4 := by rw [←Nat.card_eq_fintype_card,card_E]; norm_num
  rw [hc] at hh
  change d * d^(2^1) = 1
  simpa [pow_succ,mul_assoc] using hh

/-- The point-vector stabilizer in the cover is the whole point parabolic. -/
theorem fixes_pointVector_iff (a : Cover 1) :
    binaryActionHom 1 a pointVector = pointVector ↔ a 1 0 = 0 ∧ a 2 0 = 0 := by
  have hentry (i j : Fin 3) :
      (binaryActionHom 1 a pointVector).val i j = a i 0 * sigma 1 (a j 0) := by
    change (a.val * pointVector.val * adjoint 1 a.val) i j = _
    simp [pointVector,coordinates,adjoint,Matrix.mul_apply,Fin.sum_univ_three]
  constructor
  · intro h
    have hh (i : Fin 3) (hi : i = 1 ∨ i = 2) : a i 0 = 0 := by
      have he := congrArg (fun X : Space 1 => X.val i i) h
      rw [hentry] at he
      have hz : a i 0 * sigma 1 (a i 0) = 0 := by
        rcases hi with rfl | rfl <;> exact he
      exact (mul_eq_zero.mp hz).elim id (fun hz => (sigma 1).injective (hz.trans (map_zero _).symm))
    exact ⟨hh 1 (Or.inl rfl),hh 2 (Or.inr rfl)⟩
  · rintro ⟨h10,h20⟩
    have hn : a 0 0 ≠ 0 := by
      intro hz
      have hh := congrArg (fun b : Cover 1 => b 0 0) (inv_mul_cancel a)
      change (a⁻¹.val * a.val) 0 0 = 1 at hh
      simp [Matrix.mul_apply,Fin.sum_univ_three,h10,h20,hz] at hh
    have h00 := norm_one _ hn
    apply Subtype.ext
    ext i j
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [h10,h20,h00,pointVector,coordinates]

end Representation.HermitianTensorThree.PointSection
