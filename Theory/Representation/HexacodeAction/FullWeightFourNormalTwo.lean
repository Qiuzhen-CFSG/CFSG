module

public import Theory.Representation.HexacodeAction.FullWeightFourVectorStabilizer
public import Theory.GroupTheory.SpecificGroups.SymmetricFourProductNormalTwo

/-!
# Normal two-subgroups at a literal weight-four vector

Conjugation in S2 × S4 depends only on the second factor. Consequently
normalization by the even sign graph already implies full normality. The
product calculation gives the Klein four, central involution, and elementary
eight alternatives. Fixing the entire scalar point removes the latter two
possibilities, while retaining the same coordinate marking throughout.

Source: Aschbacher--Smith, 12.7.15(2--3), printed p.843.
-/

public noncomputable section
open Atlas.Codes Subgroup
namespace Representation.Hexacode
open BinaryOffender Theory.SpecificGroups.SymmetricSix
open DuadCalculation

private theorem conjugate_sign_graph (x y : DuadProduct) :
    x * y * x⁻¹ = (signPermTwo x.2, x.2) * y * (signPermTwo x.2, x.2)⁻¹ := by
  apply Prod.ext
  · have hc : ∀ a b : Two, a * b = b * a := by decide
    simp only [Prod.fst_mul, Prod.fst_inv]
    rw [hc x.1 y.1, mul_inv_cancel_right, hc (signPermTwo x.2) y.1,
      mul_inv_cancel_right]
  · rfl

/-- The literal normal two-subgroup alternatives require normalization only
by the even vector stabilizer. Pointwise scalar-plane fixation selects the
same marked Klein four. -/
theorem fullWeightFour_normal_two_cases (v : hexacode)
    (hv : hammingNorm v.val = 4) (N : Subgroup HexAutomorphisms)
    (hN : N ≤ fullVectorStabilizer v) (hp : IsPGroup 2 N) (hne : N ≠ ⊥)
    (hn : (fullWeightVectorStabilizer v).map hexSign.ker.subtype ≤
      normalizer (N : Set HexAutomorphisms)) :
    ∃ e : fullVectorStabilizer v ≃* DuadProduct,
      ∃ r : alternatingGroup (Fin 6),
        (∀ g : fullVectorStabilizer v,
          duadProductHom (e g) = r.val * hexCoordinateSixHom g.val * r.val⁻¹) ∧
        (∀ g : fullVectorStabilizer v,
          hexSign g.val = 1 ↔ (e g).1 = signPermTwo (e g).2) ∧
        (let B := (N.subgroupOf (fullVectorStabilizer v)).map e.toMonoidHom
         (B = (⊥ : Subgroup Two).prod core ∨ B = centralFactor ∨ B = productCore) ∧
         (N ≤ subspaceKernel action ((Submodule.span F {v}).restrictScalars Bit) ⊤ →
           B = (⊥ : Subgroup Two).prod core)) := by
  obtain ⟨e, r, he, heven⟩ := fullWeightFourVectorStabilizer_model v hv
  let A := N.subgroupOf (fullVectorStabilizer v)
  let B := A.map e.toMonoidHom
  have hBn : B.Normal := by
    refine ⟨?_⟩
    intro y hy x
    obtain ⟨a, ha, rfl⟩ := hy
    let z : fullVectorStabilizer v := e.symm (signPermTwo x.2, x.2)
    have hzEven : hexSign z.val = 1 := by
      apply (heven z).mpr
      rw [show e z = (signPermTwo x.2, x.2) from e.apply_symm_apply _]
    have hz : z.val ∈ (fullWeightVectorStabilizer v).map hexSign.ker.subtype :=
      ⟨⟨z.val, hzEven⟩, z.property, rfl⟩
    have hh : z.val * a.val * z.val⁻¹ ∈ N :=
      le_normalizer_iff.mp hn z.val hz a.val ha
    refine ⟨z * a * z⁻¹, hh, ?_⟩
    change e (z * a * z⁻¹) = x * e a * x⁻¹
    rw [map_mul, map_mul, map_inv, show e z = (signPermTwo x.2, x.2) from
      e.apply_symm_apply _]
    exact (conjugate_sign_graph x (e a)).symm
  let := hBn
  have hB2 : IsPGroup 2 B := hp.comap_subtype.map e.toMonoidHom
  have hBne : B ≠ ⊥ := by
    intro hh
    have hA : A = ⊥ := (map_eq_bot_iff_of_injective A e.injective).mp hh
    apply hne
    apply bot_unique
    intro x hx
    have hm : (⟨x, hN hx⟩ : fullVectorStabilizer v) ∈ A := hx
    rw [hA] at hm
    exact congrArg Subtype.val (mem_bot.mp hm)
  have hcases := (normal_two_subgroup_cases B hB2).resolve_left hBne
  refine ⟨e, r, he, heven, hcases, ?_⟩
  intro hpoint
  have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
  rw [scalar_point_kernel_eq_even_vector v hv0] at hpoint
  have hBe (x : DuadProduct) (hx : x ∈ B) : x.1 = signPermTwo x.2 := by
    obtain ⟨a, ha, rfl⟩ := hx
    exact (heven a).mp (hpoint ha).2
  rcases hcases with hR | hZ | hE
  · exact hR
  · have hh := hBe (Equiv.swap 0 1, 1) (hZ.symm ▸ ⟨mem_top _, one_mem _⟩)
    exact (by decide : (Equiv.swap 0 1 : Two) ≠ signPermTwo 1) hh |>.elim
  · have hh := hBe (Equiv.swap 0 1, 1) (hE.symm ▸ ⟨mem_top _, one_mem _⟩)
    exact (by decide : (Equiv.swap 0 1 : Two) ≠ signPermTwo 1) hh |>.elim

end Representation.Hexacode
