module

public import Theory.Representation.OrthogonalFourPlusMatrix.SylowFixedDimension
public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement

/-!
# Singular lines fixed by tensor Sylow subgroups

In the determinant module for SL₂(4) × SL₂(4), the common fixed space
of the two upper unipotent groups consists of matrices supported at (0,1).
It is one-dimensional over F₄. Sylow conjugacy transports this calculation
to every Sylow 2-subgroup, giving a fixed space of exactly four elements.

This supplies the literal singular line used in Aschbacher–Smith 9.1.2
and the tensor branch of 9.2.2(3), combined manuscript, printed pp.729–731.
-/

@[expose] public section
open Matrix Subgroup Representation Representation.BinaryOffender
open scoped Pointwise
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

noncomputable section

def pointMap : F →ₗ[ZMod 2] V where
  toFun c := !![0,c;0,0]
  map_add' a b := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a b := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp

def point : Submodule (ZMod 2) V := pointMap.range

def planeMap : (Fin 2 → F) →ₗ[ZMod 2] V where
  toFun v := !![0,v 0;0,v 1]
  map_add' a b := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a b := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp

def plane : Submodule (ZMod 2) V := planeMap.range

private theorem pointMap_injective : Function.Injective pointMap := by
  intro a b h
  exact congrArg (fun v : V => v 0 1) h

private theorem planeMap_injective : Function.Injective planeMap := by
  intro a b h
  funext i
  have he := congrArg (fun v : V => v i 1) h
  fin_cases i <;> simpa [planeMap] using he

theorem card_point : Nat.card point = 4 := by
  change Nat.card pointMap.range = 4
  rw [Nat.card_congr (LinearEquiv.ofInjective pointMap pointMap_injective).toEquiv.symm]
  simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_field

theorem card_plane : Nat.card plane = 16 := by
  change Nat.card planeMap.range = 16
  rw [Nat.card_congr (LinearEquiv.ofInjective planeMap planeMap_injective).toEquiv.symm]
  simpa only [Nat.card_eq_fintype_card] using Representation.SL2FourNatural.card_vector

def upperPairSylow : Sylow 2 G := by
  let S := SpecialLinearGroup.upperUnipotent F
  have hp : IsPGroup 2 (S.prod S) := by
    apply IsPGroup.of_card (n := 4)
    rw [Nat.card_congr (S.prodEquiv S).toEquiv, Nat.card_prod,
      SpecialLinearGroup.card_upperUnipotent, Nat.card_eq_fintype_card,
      Representation.SL2FourNatural.card_field]
    decide
  refine ⟨S.prod S,hp,?_⟩
  intro Q hQ hSQ
  have hfst : Q.map (MonoidHom.fst _ _) = S := by
    apply (SpecialLinearGroup.upperUnipotentSylow F 2).is_maximal' (hQ.map _)
    intro a ha
    exact ⟨(a,1), hSQ ⟨ha,S.one_mem⟩, rfl⟩
  have hsnd : Q.map (MonoidHom.snd _ _) = S := by
    apply (SpecialLinearGroup.upperUnipotentSylow F 2).is_maximal' (hQ.map _)
    intro a ha
    exact ⟨(1,a), hSQ ⟨S.one_mem,ha⟩, rfl⟩
  apply le_antisymm ?_ hSQ
  intro a ha
  exact ⟨hfst ▸ mem_map_of_mem _ ha, hsnd ▸ mem_map_of_mem _ ha⟩

private theorem coordinates_of_upper_fixed (v : V)
    (hl : action (SpecialLinearGroup.transvection zero_ne_one (1 : F),1) v = v)
    (hr : action (1,SpecialLinearGroup.transvection zero_ne_one (1 : F)) v = v) :
    v 0 0 = 0 ∧ v 1 0 = 0 ∧ v 1 1 = 0 := by
  have hl' := (Displacement.fixed_iff_intertwines _ _).mp hl
  have hr' := (Displacement.fixed_iff_intertwines _ _).mp hr
  simp only [SpecialLinearGroup.coe_one, mul_one, one_mul] at hl' hr'
  have hrow (j : Fin 2) : v 1 j = 0 := by
    have he := congrArg (fun w : V => w 0 j) hl'
    simpa [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two] using he
  have hcol : v 0 0 = 0 := by
    have he := congrArg (fun w : V => w 0 1) hr'
    simpa [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two] using he.symm
  exact ⟨hcol,hrow 0,hrow 1⟩

theorem fixedSpace_upperPair : fixedSpace action (upperPairSylow : Subgroup G) = point := by
  apply le_antisymm
  · intro v hv
    have hu : SpecialLinearGroup.transvection zero_ne_one (1 : F) ∈ SpecialLinearGroup.upperUnipotent F := ⟨Multiplicative.ofAdd 1,rfl⟩
    obtain ⟨h00,h10,h11⟩ := coordinates_of_upper_fixed v
      (hv ⟨_,⟨hu,one_mem _⟩⟩) (hv ⟨_,⟨one_mem _,hu⟩⟩)
    refine ⟨v 0 1,?_⟩
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pointMap,h00,h10,h11]
  · rintro _ ⟨c,rfl⟩ a
    change action a.val (pointMap c) = pointMap c
    obtain ⟨x,hx⟩ := a.property.1
    obtain ⟨y,hy⟩ := a.property.2
    apply (Displacement.fixed_iff_intertwines _ _).mpr
    rw [←hx,←hy]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.upperUnipotentHom,SpecialLinearGroup.transvection_coe,
        pointMap,Matrix.mul_apply,Fin.sum_univ_two]

private theorem action_mul_apply (a b : G) (v : V) :
    action (a*b) v = action a (action b v) :=
  congrArg (fun f : Module.End (ZMod 2) V => f v) (action.map_mul a b)

theorem sylow_fixedSpace_conjugate_point (P : Sylow 2 G) :
    ∃ g : G, fixedSpace action (P : Subgroup G) = point.map (action g) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G upperPairSylow P
  refine ⟨g,?_⟩
  apply le_antisymm
  · intro v hv
    refine ⟨action g⁻¹ v,?_,?_⟩
    · rw [←fixedSpace_upperPair]
      intro a
      have ha : g*a.val*g⁻¹ ∈ P := by
        rw [←hg]
        change g*a.val*g⁻¹ ∈ MulAut.conj g • (upperPairSylow : Set G)
        exact ⟨a,a.property,rfl⟩
      calc
        action a.val (action g⁻¹ v) = action (a.val*g⁻¹) v := (action_mul_apply _ _ _).symm
        _ = action (g⁻¹*(g*a.val*g⁻¹)) v := by rw [mul_assoc g a.val g⁻¹,inv_mul_cancel_left]
        _ = action g⁻¹ (action (g*a.val*g⁻¹) v) := action_mul_apply _ _ _
        _ = action g⁻¹ v := congrArg (action g⁻¹) (hv ⟨_,ha⟩)
    · rw [←action_mul_apply,mul_inv_cancel,action.map_one]
      rfl
  · rintro _ ⟨v,hv,rfl⟩ a
    have ha : a.val ∈ MulAut.conj g • (upperPairSylow : Set G) := by
      change a.val ∈ (g • upperPairSylow : Sylow 2 G)
      rw [hg]
      exact a.property
    obtain ⟨b,hb,he⟩ := ha
    change g*b*g⁻¹ = a.val at he
    have hfix := (fixedSpace_upperPair.ge hv) ⟨b,hb⟩
    calc
      action a.val (action g v) = action ((g*b*g⁻¹)*g) v := by rw [he,action_mul_apply]
      _ = action (g*b) v := by rw [inv_mul_cancel_right]
      _ = action g (action b v) := action_mul_apply _ _ _
      _ = action g v := congrArg (action g) hfix

theorem card_fixedSpace_sylow (P : Sylow 2 G) :
    Nat.card (fixedSpace action (P : Subgroup G)) = 4 := by
  obtain ⟨g,hg⟩ := sylow_fixedSpace_conjugate_point P
  rw [hg]
  change Nat.card (point.map (linearAction g).toLinearMap) = 4
  rw [Nat.card_congr ((linearAction g).submoduleMap point).toEquiv.symm]
  exact card_point

/-- The first SL₂ factor has no nonzero common fixed matrix. -/
theorem first_factor_common_fixed_eq_zero (v : V)
    (hv : ∀ g : SpecialLinearGroup (Fin 2) F, action (g,1) v = v) : v = 0 := by
  have hu := hv (Representation.SL2FourNatural.upper 1)
  have hl := hv (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1)
  rw [Displacement.fixed_iff_intertwines] at hu hl
  simp only [SpecialLinearGroup.coe_one,mul_one] at hu hl
  apply Matrix.ext
  intro i j
  fin_cases i
  · have h := congrArg (fun w : V => w 1 j) hl
    simpa [SpecialLinearGroup.transvection_coe,Matrix.transvection,
      Matrix.mul_apply,Fin.sum_univ_two] using h
  · have h := congrArg (fun w : V => w 0 j) hu
    simpa [Representation.SL2FourNatural.upper,
      Matrix.mul_apply,Fin.sum_univ_two] using h

end
end ClassicalOrthogonal.FourPlusMatrix.Binary
