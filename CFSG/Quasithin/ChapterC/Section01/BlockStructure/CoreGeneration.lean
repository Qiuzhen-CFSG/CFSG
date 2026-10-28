module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreSquares
/-!
# Recovering block cores from a fully moved ambient core

Suppose two subnormal short blocks commute and their product moves the
entire ambient two-core. The subnormal core-action theorem puts that core
in the product of their U-layers. A core element of the first block fixes
the second block, so its second U-coordinate is central there. When the
second block has trivial center, the first block's two-core is exactly U.

Source: Aschbacher--Smith C.1.7--11, pp.123--124, applied in
10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- A fully moved ambient core has no extra layer above either commuting block. -/
theorem IsBlock.core_eq_blockU_of_pair_core_generated
    {A B : Subgroup G} (hA : IsBlock A) (hB : IsBlock B)
    (hc : ⁅A,B⁆ = ⊥) (hZ : center B = ⊥)
    (hm : pCore 2 G = ⁅pCore 2 G,A ⊔ B⁆) :
    pCore 2 A = blockU A := by
  let U := (blockU A).map A.subtype
  let V := (blockU B).map B.subtype
  let W := U ⊔ V
  have hUA : U ≤ A := map_subtype_le _
  have hVB : V ≤ B := map_subtype_le _
  have hAB : A ≤ centralizer (B : Set G) := commutator_eq_bot_iff_le_centralizer.mp hc
  have hBA : B ≤ centralizer (A : Set G) := le_centralizer_iff.mp hAB
  have hAU : A ≤ normalizer (U : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (blockU A))
  have hBV : B ≤ normalizer (V : Set G) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  have hAV : A ≤ normalizer (V : Set G) :=
    ((hAB.trans (centralizer_le hVB)).trans (centralizer_le_normalizer _))
  have hBU : B ≤ normalizer (U : Set G) :=
    ((hBA.trans (centralizer_le hUA)).trans (centralizer_le_normalizer _))
  have hAW : A ≤ normalizer (W : Set G) :=
    (le_inf hAU hAV).trans (normalizer_inf_normalizer_le_normalizer_sup U V)
  have hBW : B ≤ normalizer (W : Set G) :=
    (le_inf hBU hBV).trans (normalizer_inf_normalizer_le_normalizer_sup U V)
  have hcommA : ⁅A,pCore 2 G⁆ ≤ W := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal A (pCore 2 G)
      hA.subnormal hA.short.twoPerfect pCore_isPGroup le_normalizer_of_normal).trans le_sup_left
  have hcommB : ⁅B,pCore 2 G⁆ ≤ W := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal B (pCore 2 G)
      hB.subnormal hB.short.twoPerfect pCore_isPGroup le_normalizer_of_normal).trans le_sup_right
  have hQW : pCore 2 G ≤ W := by
    rw [hm,commutator_comm]
    exact (le_commutatorPreimage_iff (normalizer (W : Set G)) (pCore 2 G) W (A ⊔ B)
      le_rfl).mp (sup_le (le_commutatorPreimage hAW hcommA)
        (le_commutatorPreimage hBW hcommB)) |>.2
  apply le_antisymm ?_ blockU_le_core
  intro x hx
  have hxQ : (x : G) ∈ pCore 2 G :=
    pCoreIn_le_of_subnormal 2 hA.subnormal (mem_map_of_mem A.subtype hx)
  have hxW : (x : G) ∈ (W : Set G) := hQW hxQ
  rw [show (W : Set G) = (U : Set G) * (V : Set G) from
    coe_mul_of_left_le_normalizer_right U V (hUA.trans hAV)] at hxW
  obtain ⟨a,ha,b,hb,hab⟩ := hxW
  have hbC : b ∈ centralizer (B : Set G) := by
    have he : a⁻¹*(x:G) = b := by rw [←hab]; group
    exact he ▸ (centralizer (B : Set G)).mul_mem
      ((centralizer (B : Set G)).inv_mem (hAB (hUA ha))) (hAB x.property)
  have hb1 : b = 1 := by
    have hz : (⟨b,hVB hb⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (hbC k k.property)
    exact congrArg B.subtype (mem_bot.mp (hZ ▸ hz))
  have hxU : (x : G) ∈ U := by
    change a * b = (x:G) at hab
    rw [hb1,mul_one] at hab
    exact hab ▸ ha
  obtain ⟨y,hy,he⟩ := hxU
  exact (Subtype.ext he : y = x) ▸ hy
end CFSG.Quasithin.ChapterC
