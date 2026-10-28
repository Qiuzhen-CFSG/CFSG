module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.SourceData
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.ModelTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.PairQuotient
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Multiplication and module maps for the exchanged blocks

Given commutation of the two actual blocks, multiplication defines a surjection
onto K. It need not be injective. On the commutator layers its kernel lies in
the central fixed layers, and those layers centralize K. Pulling the actual
four-group back along this map preserves its ambient image and its Borel
invariance. Its commutator identity therefore prevents its module image from
vanishing, allowing the quotient-compatible field bound.

Commutation is an explicit structural hypothesis here. These constructions do
not assert the distinct-block theorem C.1.9 or the source Borel containment.
The following quotient dichotomy will remove the module-placement hypothesis.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7–9,
printed pp.123–124, and the final paragraph of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable (c : ContraryData κ d i j)

/-- The actual normal closure contains X. -/
theorem ContraryData.X_le_K : d.wholeX ≤ c.K := by
  rw [← c.conjugate_closure]
  intro x hx
  exact ⟨⟨x, c.X_le_H hx⟩, subset_normalClosure hx, rfl⟩

theorem ContraryData.four_le_K : d.V₁ i ≤ c.K := by
  apply (c.V₁_le_X i).trans
  apply le_trans _ (ContraryData.X_le_K c)
  cases i
  · exact le_sup_left
  · exact le_sup_right

namespace ExchangedBlock
variable {c} (b : ExchangedBlock c)

abbrev second : Subgroup G := b.first.map (MulAut.conj b.exchanger).toMonoidHom

theorem second_ne_first : (second b) ≠ b.first := by
  intro he
  exact b.exchanger_moves (mem_normalizer_iff_map_conj_eq.mpr he)

variable (hc : ⁅b.first, (second b)⁆ = ⊥)

/-- Multiplication of commuting blocks; no splitting is required. -/
def productMap : (b.first × (second b)) →* G :=
  b.first.subtype.noncommCoprod (second b).subtype (by
    intro x y
    exact ((mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc x.property)) y y.property).symm)

theorem productMap_range : ((productMap b) hc).range = c.K := by
  calc
    ((productMap b) hc).range = b.first.subtype.range ⊔ (second b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    _ = c.K := by simpa only [range_subtype] using b.product

/-- Multiplication restricted to the two intrinsic commutator layers. -/
def moduleProductMap : (blockU b.first × blockU (second b)) →* G :=
  ((productMap b) hc).comp pairModuleInclusion

theorem moduleProductMap_range : ((moduleProductMap b) hc).range =
    ((blockU b.first).prod (blockU (second b))).map ((productMap b) hc) := by
  rw [moduleProductMap, MonoidHom.range_comp, pairModuleInclusion,
    MonoidHom.range_prodMap, range_subtype, range_subtype]

theorem core_product_commutator :
    ⁅((pCore 2 b.first).prod (pCore 2 (second b))).map ((productMap b) hc), c.K⁆ =
      ((moduleProductMap b) hc).range := by
  rw [← (productMap_range b) hc, MonoidHom.range_eq_map, ← map_commutator,
    ← top_prod_top, commutator_prod_prod, (moduleProductMap_range b) hc]
  rfl

theorem four_le_module_of_le_core_product
    (hV : d.V₁ i ≤ ((pCore 2 b.first).prod (pCore 2 (second b))).map ((productMap b) hc)) :
    d.V₁ i ≤ ((moduleProductMap b) hc).range := by
  have hXK : d.X i ≤ c.K := by
    cases i
    · exact le_sup_left.trans (ContraryData.X_le_K c)
    · exact le_sup_right.trans (ContraryData.X_le_K c)
  rw [← c.four_commutator, ← (core_product_commutator b) hc]
  exact commutator_mono hV hXK

/-- The overlap of the two layers is lost only in their central fixed layers. -/
theorem moduleProductMap_ker :
    ((moduleProductMap b) hc).ker ≤ (blockFixed b.first).prod (blockFixed (second b)) := by
  intro u hu
  have he : ((u.1 : b.first) : G) * ((u.2 : (second b)) : G) = 1 := hu
  have h₁ : ((u.1 : b.first) : G) = ((u.2 : (second b)) : G)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp he
  have h₂ : ((u.2 : (second b)) : G) = ((u.1 : b.first) : G)⁻¹ := by
    rw [h₁, inv_inv]
  constructor
  · apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    change (x : G) * ((u.1 : b.first) : G) = ((u.1 : b.first) : G) * (x : G)
    rw [h₁]
    exact ((mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc x.property)) _
        ((second b).inv_mem u.2.val.property)).symm
  · apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    change (y : G) * ((u.2 : (second b)) : G) = ((u.2 : (second b)) : G) * (y : G)
    rw [h₂]
    exact (mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hc (b.first.inv_mem u.1.val.property))) _
        y.property

theorem fixed_product_centralizes :
    ((blockFixed b.first).prod (blockFixed (second b))).map ((moduleProductMap b) hc) ≤
      centralizer (c.K : Set G) := by
  rintro _ ⟨u, hu, rfl⟩
  apply mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨l, rfl⟩ := ((productMap_range b) hc).symm ▸ hx
  change (productMap b) hc l * (productMap b) hc (pairModuleInclusion u) =
    (productMap b) hc (pairModuleInclusion u) * (productMap b) hc l
  rw [← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (mem_center_iff.mp hu.1 l.1) (mem_center_iff.mp hu.2 l.2)

theorem moduleProductMap_conjugate (l : b.first × (second b))
    (u : blockU b.first × blockU (second b)) :
    (moduleProductMap b) hc
      (blockConjugate b.first l.1 u.1, blockConjugate (second b) l.2 u.2) =
        (productMap b) hc l * (moduleProductMap b) hc u * ((productMap b) hc l)⁻¹ := by
  change (productMap b) hc (l * pairModuleInclusion u * l⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

variable {F : Type*} [Field F]
variable (model : BlockModuleModel b.first (Matrix.SL2.naturalAction F))

/-- The image of the two-perfect lift of the full matrix Borel product. -/
def ambientBorel : Subgroup G :=
  (pairBorelLift model (conjugateModel b.first b.exchanger model)).map ((productMap b) hc)

theorem ambientBorel_perfect : IsPPerfect 2 ((ambientBorel b) hc model) :=
  (pairBorelLift_perfect model (conjugateModel b.first b.exchanger model)).of_surjective
    (((productMap b) hc).subgroupMap _) (((productMap b) hc).subgroupMap_surjective _)

theorem four_preimage_invariant
    (hBM : (ambientBorel b) hc model ≤ d.M₁) :
    ∀ l ∈ pairBorelLift model (conjugateModel b.first b.exchanger model),
      ∀ w ∈ (d.V₁ i).comap ((moduleProductMap b) hc),
        (blockConjugate b.first l.1 w.1, blockConjugate (second b) l.2 w.2) ∈
          (d.V₁ i).comap ((moduleProductMap b) hc) := by
  intro l hl w hw
  change (moduleProductMap b) hc _ ∈ d.V₁ i
  rw [(moduleProductMap_conjugate b) hc]
  exact le_normalizer_iff.mp (c.normalizes_four hBM ((ambientBorel_perfect b) hc model))
    _ (mem_map_of_mem _ hl) _ hw

theorem field_eq_four_of_module_placement [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F)
    (hBM : (ambientBorel b) hc model ≤ d.M₁)
    (hV : d.V₁ i ≤ ((moduleProductMap b) hc).range) : Nat.card F = 4 := by
  let W := (d.V₁ i).comap ((moduleProductMap b) hc)
  have hW : W.map ((moduleProductMap b) hc) = d.V₁ i := map_comap_eq_self hV
  have hXK : d.X i ≤ c.K := by
    cases i
    · exact le_sup_left.trans (ContraryData.X_le_K c)
    · exact le_sup_right.trans (ContraryData.X_le_K c)
  apply pairBorelLift_image_field_bound model (conjugateModel b.first b.exchanger model)
    hq ((moduleProductMap b) hc) ((moduleProductMap_ker b) hc) (d.X i)
    (((fixed_product_centralizes b) hc).trans (centralizer_le hXK)) W
  · rw [hW]
    exact c.V₁_card i
  · rw [hW]
    exact c.four_commutator
  · exact (four_preimage_invariant b) hc model hBM

theorem parameter_eq_two_of_module_placement [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ b.n)
    (hBM : (ambientBorel b) hc model ≤ d.M₁)
    (hV : d.V₁ i ≤ ((moduleProductMap b) hc).range) : b.n = 2 := by
  have hq : 4 ≤ Nat.card F := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) b.model.1
  have he := (field_eq_four_of_module_placement b) hc model hq hBM hV
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) (hcard.symm.trans he)

end ExchangedBlock
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement
