module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.CentralProduct
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.EvenBorel.Coordinates
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The root-or-module dichotomy for the source four-group

The kernel of multiplication of the commuting blocks is central, hence killed
by their characteristic-two rank-one projections. The image of the actual
four-group in the product quotient is therefore a two-group of order at most
four. Borel normalization places it in the root Sylow subgroup. A nontrivial
image gives the root bound directly. If the image is trivial, the four-group
lies in the product of the two cores; its commutator identity then puts it in
the intrinsic module layers, where the preceding module bound applies.

Thus Borel containment and block commutation suffice: no root placement,
module placement, nontrivial projection, or internal direct-product
isomorphism is assumed. Construction of that Borel and commutation from the
source geometry remain earlier structural obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
characteristic-two paragraph of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement
namespace ExchangedBlock
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)
variable (hc : ⁅b.first, second b⁆ = ⊥)
variable {F : Type*} [Field F]
variable (model : BlockModuleModel b.first (Matrix.SL2.naturalAction F))

theorem productMap_ker_le_centers :
    (productMap b hc).ker ≤ (center b.first).prod (center (second b)) := by
  intro u hu
  have he : (u.1 : G) * (u.2 : G) = 1 := hu
  have h₁ : (u.1 : G) = (u.2 : G)⁻¹ := mul_eq_one_iff_eq_inv.mp he
  have h₂ : (u.2 : G) = (u.1 : G)⁻¹ := by rw [h₁, inv_inv]
  constructor
  · apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    change (x : G) * (u.1 : G) = (u.1 : G) * (x : G)
    rw [h₁]
    exact ((mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc x.property)) _
        ((second b).inv_mem u.2.property)).symm
  · apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : G) * (u.2 : G) = (u.2 : G) * (y : G)
    rw [h₂]
    exact (mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc (b.first.inv_mem u.1.property))) _
        y.property

private theorem projection_ker {L : Type*} [Group L]
    (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    (projection m).ker = pCore 2 L := by
  ext x
  simp [projection]

private theorem center_le_projection_ker {L : Type*} [Group L] [CharP F 2]
    (m : BlockModuleModel L (Matrix.SL2.naturalAction F)) :
    center L ≤ (projection m).ker := by
  intro z hz
  have hcentral : projection m z ∈ center _ := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨y, rfl⟩ := projection_surjective m x
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
  simpa only [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot, mem_bot,
    MonoidHom.mem_ker] using hcentral

theorem productMap_ker_le_pairProjection [CharP F 2] :
    (productMap b hc).ker ≤
      (pairProjection model (conjugateModel b.first b.exchanger model)).ker := by
  intro u hu
  have hh := productMap_ker_le_centers b hc hu
  exact Prod.ext (center_le_projection_ker model hh.1)
    (center_le_projection_ker (conjugateModel b.first b.exchanger model) hh.2)

private theorem image_factor {D A E : Type*} [Group D] [Group A] [Group E]
    (f : D →* A) (g : D →* E) (hker : f.ker ≤ g.ker) (W : Subgroup D) :
    ∃ φ : W.map f →* W.map g, Function.Surjective φ := by
  let fW := f.subgroupMap W
  let gW := g.subgroupMap W
  have hkg : fW.ker ≤ gW.ker := by
    intro w hw
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact hker (congrArg Subtype.val (MonoidHom.mem_ker.mp hw))
  let q := QuotientGroup.lift fW.ker gW (fun w hw => hkg hw)
  let e := QuotientGroup.quotientKerEquivOfSurjective fW (f.subgroupMap_surjective W)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, rfl⟩ := g.subgroupMap_surjective W y
    exact ⟨QuotientGroup.mk' fW.ker w, rfl⟩
  exact ⟨q.comp e.symm.toMonoidHom, hq.comp e.symm.surjective⟩

theorem four_preimage_normalized
    (hBM : ambientBorel b hc model ≤ d.M₁) :
    pairBorelLift model (conjugateModel b.first b.exchanger model) ≤
      normalizer ((d.V₁ i).comap (productMap b hc) : Set (b.first × second b)) := by
  apply le_trans _ ((d.V₁ i).le_normalizer_comap (productMap b hc))
  intro l hl
  exact c.normalizes_four hBM (ambientBorel_perfect b hc model)
    (mem_map_of_mem _ hl)

/-- Both quotient branches force field four from Borel containment alone. -/
theorem field_eq_four_of_borel_placement [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) (hBM : ambientBorel b hc model ≤ d.M₁) :
    Nat.card F = 4 := by
  let m₂ := conjugateModel b.first b.exchanger model
  let f := productMap b hc
  let π := pairProjection model m₂
  let W := (d.V₁ i).comap f
  have hW : W.map f = d.V₁ i := map_comap_eq_self (by
    rw [productMap_range]
    exact ContraryData.four_le_K c)
  have hVtwo : IsPGroup 2 (W.map f) := by
    rw [hW]
    exact IsPGroup.of_card (n := 2) (c.V₁_card i)
  obtain ⟨φ, hφ⟩ := image_factor f π (productMap_ker_le_pairProjection b hc model) W
  have hQtwo : IsPGroup 2 (W.map π) := hVtwo.of_surjective φ hφ
  have hQcard : Nat.card (W.map π) ≤ 4 := by
    simpa only [hW, c.V₁_card i] using Nat.card_le_card_of_surjective φ hφ
  have hB := four_preimage_normalized b hc model hBM
  have hQnorm : (BenderSuzuki.Converse.Borel F).prod (BenderSuzuki.Converse.Borel F) ≤
      normalizer (W.map π : Set _) := by
    rw [← pairBorelLift_map model m₂ hq]
    exact (map_mono hB).trans (le_normalizer_map π)
  by_cases hQ : W.map π = ⊥
  · have hWker : W ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp hQ
    have hker : π.ker = (pCore 2 b.first).prod (pCore 2 (second b)) := by
      ext x
      change (projection model x.1, projection m₂ x.2) = (1, 1) ↔ _
      simp only [Prod.mk.injEq, ← MonoidHom.mem_ker, projection_ker, mem_prod]
    have hVcore : d.V₁ i ≤
        ((pCore 2 b.first).prod (pCore 2 (second b))).map f := by
      rw [← hW]
      exact map_mono (hker ▸ hWker)
    exact field_eq_four_of_module_placement b hc model hq hBM
      (four_le_module_of_le_core_product b hc hVcore)
  · let S := ComponentElimination.evenRootProductSylow F
    have hSQ : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)) ≤ normalizer (W.map π : Set _) := by
      apply le_trans _ hQnorm
      rw [← rankOneBorel_eq_sourceBorel]
      intro x hx
      exact ⟨(Matrix.SpecialLinearGroup.upperUnipotent F).le_normalizer hx.1,
        (Matrix.SpecialLinearGroup.upperUnipotent F).le_normalizer hx.2⟩
    have hroot : W.map π ≤
        (Matrix.SpecialLinearGroup.upperUnipotent F).prod
          (Matrix.SpecialLinearGroup.upperUnipotent F) := by
      exact sup_eq_right.mp (S.is_maximal'
        (hQtwo.to_sup_of_normal_left' S.isPGroup' hSQ) le_sup_right)
    have hbound := Matrix.SpecialLinearGroup.card_le_of_root_prod_normalized
      (W.map π) hroot hQ (by rwa [rankOneBorel_eq_sourceBorel])
    exact Nat.le_antisymm (hbound.trans hQcard) hq

/-- The field-order conclusion gives the exact source exponent. -/
theorem parameter_eq_two_of_borel_placement [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ b.n)
    (hBM : ambientBorel b hc model ≤ d.M₁) : b.n = 2 := by
  have hq : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) b.model.1
  exact Nat.pow_right_injective (by decide : 2 ≤ 2)
    (hcard.symm.trans (field_eq_four_of_borel_placement b hc model hq hBM))

end ExchangedBlock
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement
