module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases

/-!
# The rank-two four-group attached to an isotropic binary plane

Pointwise plane fixers are symmetric shears. Among their additive four-groups,
there is exactly one whose three nonidentity elements have no fixed vector
outside the plane. The finite certificate concerns pairs of symmetric 2×2
matrices, rather than enumerating subgroups of the symplectic group.
-/

noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
open Matrix Plane

local notation "Bit" => ZMod 2
private abbrev Pair := Bit × Bit

private def rootMatrix (a : Pair) : Matrix (Fin 2) (Fin 2) Bit :=
  !![a.1, a.1 + a.2; a.1 + a.2, a.2]

private def rootHom : Multiplicative Pair →* Sp Bit where
  toFun a := shearSp ⟨rootMatrix a.toAdd, by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  map_one' := by apply Subtype.ext; decide +kernel
  map_mul' := by decide +kernel

private theorem rootHom_injective : Function.Injective rootHom := by
  intro a b h
  have hm := congrArg (fun g : Sp Bit => g.val) h
  have h0 := congrFun (congrFun hm (.inl 0)) (.inr 0)
  have h1 := congrFun (congrFun hm (.inl 1)) (.inr 1)
  exact Prod.ext h0 h1

private def rootFour : Subgroup (Sp Bit) := rootHom.range

private theorem rootFour_card : Nat.card rootFour = 4 := by
  change Nat.card rootHom.range = 4
  rw [Nat.card_congr (MonoidHom.ofInjective rootHom_injective).toEquiv.symm]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem shear_of_fixes_plane (g : Sp Bit)
    (hf : ∀ v ∈ plane Bit, g • v = v) :
    ∃ B : symmetricMatrices Bit, g = shearSp B := by
  have hA : g.val.toBlocks₁₁ = 1 := by
    ext i j
    have hh := congrFun (hf (e j) (e_mem_plane j)) (.inl i)
    simpa [smul_eq_mulVec, e, Matrix.mulVec_single, Matrix.toBlocks₁₁,
      Matrix.one_apply, Pi.single_apply] using hh
  have hC : g.val.toBlocks₂₁ = 0 := by
    ext i j
    have hh := congrFun (hf (e j) (e_mem_plane j)) (.inr i)
    simpa [smul_eq_mulVec, e, Matrix.mulVec_single, Matrix.toBlocks₂₁] using hh
  have hs := g.property
  rw [← g.val.fromBlocks_toBlocks, SymplecticGroup.fromBlocks_mem_iff] at hs
  simp only [hA, hC, transpose_one, one_mul, mul_zero, transpose_zero,
    zero_mul, sub_zero, true_and] at hs
  have hD := hs.2
  have hB : g.val.toBlocks₁₂.IsSymm := by
    change _ᵀ = _
    simpa [hD] using hs.1
  refine ⟨⟨g.val.toBlocks₁₂, hB⟩, ?_⟩
  apply Subtype.ext
  change g.val = fromBlocks 1 g.val.toBlocks₁₂ 0 1
  nth_rw 1 [← g.val.fromBlocks_toBlocks]
  rw [hA, hC, hD]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem nonsingular_pair (B C : Matrix (Fin 2) (Fin 2) Bit)
    (hB : B.IsSymm) (hC : C.IsSymm)
    (hBn : ∀ v : Fin 2 → Bit, B *ᵥ v = 0 → v = 0)
    (hCn : ∀ v : Fin 2 → Bit, C *ᵥ v = 0 → v = 0)
    (hBCn : ∀ v : Fin 2 → Bit, (B + C) *ᵥ v = 0 → v = 0) :
    B 0 1 = B 0 0 + B 1 1 := by
  revert B C
  decide +kernel

private theorem shear_kernel (B : symmetricMatrices Bit)
    (hf : ∀ v : Vector Bit, shearSp B • v = v → v ∈ plane Bit) :
    ∀ v : Fin 2 → Bit, B.val *ᵥ v = 0 → v = 0 := by
  intro v hv
  have hh : shearSp B • Sum.elim (0 : Fin 2 → Bit) v = Sum.elim (0 : Fin 2 → Bit) v := by
    change (fromBlocks 1 B.val 0 1) *ᵥ Sum.elim (0 : Fin 2 → Bit) v = _
    simp [Matrix.fromBlocks_mulVec, hv]
  have hp := hf (Sum.elim (0 : Fin 2 → Bit) v) hh
  funext i
  exact hp i

private theorem exists_third (R : Subgroup (Sp Bit)) (hc : Nat.card R = 4) (r : R) :
    ∃ s : R, s ≠ 1 ∧ s ≠ r := by
  classical
  let := Fintype.ofFinite R
  have ht : 2 < Fintype.card R := by simp [← Nat.card_eq_fintype_card, hc]
  obtain ⟨a,b,c,hab,hac,hbc⟩ := Fintype.two_lt_card_iff.mp ht
  by_cases ha : a = 1 ∨ a = r
  · by_cases hb : b = 1 ∨ b = r
    · rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (hab (ha.trans hb.symm)).elim
      · exact ⟨c, fun he => hac (ha.trans he.symm), fun he => hbc (hb.trans he.symm)⟩
      · exact ⟨c, fun he => hbc (hb.trans he.symm), fun he => hac (ha.trans he.symm)⟩
      · exact (hab (ha.trans hb.symm)).elim
    · exact ⟨b, not_or.mp hb⟩
  · exact ⟨a, not_or.mp ha⟩

private theorem eq_rootFour (R : Subgroup (Sp Bit)) (hc : Nat.card R = 4)
    (hf : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ plane Bit) :
    R = rootFour := by
  apply Subgroup.eq_of_le_of_card_ge ?_ (by rw [hc, rootFour_card])
  intro r hr
  by_cases h1 : r = 1
  · subst r
    exact rootFour.one_mem
  obtain ⟨s, hs1, hsr⟩ := exists_third R hc ⟨r,hr⟩
  have hs1' : s.val ≠ 1 := fun hh => hs1 (Subtype.ext hh)
  obtain ⟨B, rfl⟩ := shear_of_fixes_plane r (fun v hv => (hf r hr h1 v).mpr hv)
  obtain ⟨C, hC⟩ := shear_of_fixes_plane s.val
    (fun v hv => (hf s.val s.property hs1' v).mpr hv)
  have hmul : shearSp B * shearSp C = shearSp (B+C) := by
    exact congrArg Subtype.val (shear_add B C).symm
  have hprod1 : shearSp B * s.val ≠ 1 := by
    intro hh
    have hinv : (shearSp B)⁻¹ = shearSp B := by
      apply inv_eq_of_mul_eq_one_left
      have hz : B+B=0 := by ext i j; exact CharTwo.add_self_eq_zero _
      rw [← show shearSp (B+B) = shearSp B * shearSp B from
        congrArg Subtype.val (shear_add B B), hz]
      exact congrArg Subtype.val shear_zero
    have hh' : s.val = shearSp B := by
      calc s.val = (shearSp B)⁻¹ := (eq_inv_of_mul_eq_one_right hh)
           _ = shearSp B := hinv
    exact hsr (Subtype.ext hh')
  have hnB := shear_kernel B (fun v hv => (hf _ hr h1 v).mp hv)
  have hnC := shear_kernel C (fun v hv =>
    (hf _ s.property hs1' v).mp (hC ▸ hv))
  have hnBC := shear_kernel (B+C) (fun v hv =>
    (hf _ (R.mul_mem hr s.property) hprod1 v).mp (by simpa [hC, hmul] using hv))
  have hrel := nonsingular_pair B.val C.val B.property C.property hnB hnC hnBC
  refine ⟨Multiplicative.ofAdd (B.val 0 0, B.val 1 1), ?_⟩
  apply Subtype.ext
  change fromBlocks 1 (rootMatrix _) 0 1 = fromBlocks 1 B.val 0 1
  congr 1
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact hrel.symm
  · exact hrel.symm.trans (congrFun (congrFun B.property 0) 1).symm
  · rfl

/-- The actual plane uniquely determines its four-group of rank-two shears. -/
public theorem eq_of_common_fixed_plane
    (W : Submodule Bit (Vector Bit)) (hd : Module.finrank Bit W = 2)
    (hi : ∀ x ∈ W, ∀ y ∈ W, form Bit x y = 0)
    (R S : Subgroup (Sp Bit)) (hR : Nat.card R = 4) (hS : Nat.card S = 4)
    (hfR : ∀ r ∈ R, r ≠ 1 → ∀ v : Vector Bit, r • v = v ↔ v ∈ W)
    (hfS : ∀ s ∈ S, s ≠ 1 → ∀ v : Vector Bit, s • v = v ↔ v ∈ W) : R = S := by
  have hn : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd
    omega
  obtain ⟨g,hg⟩ := TwoLocalCover.isotropic_subspace_conjugate_standard W hn hi
  have hp : W.map (toLinear g).toLinearMap = plane Bit := by
    rcases hg with hg | hg
    · have hh := (toLinear g).finrank_map_eq W
      rw [hg, finrank_point, hd] at hh
      omega
    · exact hg
  have align (A : Subgroup (Sp Bit)) (hc : Nat.card A = 4)
      (hf : ∀ a ∈ A, a ≠ 1 → ∀ v : Vector Bit, a • v = v ↔ v ∈ W) :
      A.map (MulAut.conj g).toMonoidHom = rootFour := by
    apply eq_rootFour _ (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc])
    rintro r ⟨a,ha,rfl⟩ hr v
    have ha1 : a ≠ 1 := by intro h; simp [h] at hr
    constructor
    · intro hv
      change (g*a*g⁻¹) • v = v at hv
      have hw : g⁻¹ • v ∈ W := (hf a ha ha1 _).mp (by
        have hh := congrArg (fun w : Vector Bit => g⁻¹ • w) hv
        simpa only [mul_smul, inv_smul_smul] using hh)
      rw [←hp]
      exact ⟨g⁻¹ • v, hw, smul_inv_smul g v⟩
    · intro hv
      rw [←hp] at hv
      obtain ⟨w,hw,rfl⟩ := hv
      change (g*a*g⁻¹) • (g • w) = g • w
      simp only [mul_smul, inv_smul_smul, (hf a ha ha1 w).mpr hw]
  exact Subgroup.map_injective (MulAut.conj g).injective ((align R hR hfR).trans (align S hS hfS).symm)

end Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive
