module

public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The literal inclusion B/U → P/U

The tensor factors in 8.2.8 use the original subgroup quotients. Their
inclusion is induced by the two quotient maps and converted to a binary
linear map. Equality modulo U is detected in the original subgroup B, so
the inclusion is injective. This is the common marking used by the cubic
and noncubic tensor calculations; it imposes no tensor-recognition premise.

Source: Aschbacher–Smith, Proposition 8.2.8(5), printed pp.718–719.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G : Type*} [Group G]
variable (P B U : Subgroup G) (hBP : B ≤ P)
  [(U.subgroupOf B).Normal] [(U.subgroupOf P).Normal]
  [IsElementaryAbelian 2 (B ⧸ U.subgroupOf B)]
  [IsElementaryAbelian 2 (P ⧸ U.subgroupOf P)]

/-- The original subgroup inclusion, modulo the same U on both sides. -/
def quotientInclusion : Additive (B ⧸ U.subgroupOf B) →ₗ[ZMod 2]
    Additive (P ⧸ U.subgroupOf P) :=
  (QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl) hBP).toAdditive.toZModLinearMap 2

theorem quotientInclusion_mk (b : B) :
    quotientInclusion P B U hBP (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b)) =
      Additive.ofMul (QuotientGroup.mk' (U.subgroupOf P) (inclusion hBP b)) := rfl

theorem quotientInclusion_injective : Function.Injective (quotientInclusion P B U hBP) := by
  let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl) hBP
  have hi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) x
    have hb : (inclusion hBP b) ∈ U.subgroupOf P :=
      (QuotientGroup.eq_one_iff _).mp hx
    exact (QuotientGroup.eq_one_iff b).mpr hb
  intro x y he
  exact hi he

/-- The literal binary carrier P/U with P=O₂(I). -/
abbrev CoreSection (I U : Subgroup G) [(U.subgroupOf (I.pCoreIn 2)).Normal] :=
  Additive (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))

/-- The literal carrier B/U with B=V∩O₂(I). -/
abbrev IntersectionSection (I V U : Subgroup G)
    [(U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal] :=
  Additive ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2))

/-- The source marking B/U → P/U, using the original inclusions and quotient maps. -/
def intersectionInclusion (I V U : Subgroup G)
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    [(U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal]
    [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
    [IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸
      U.subgroupOf (V ⊓ I.pCoreIn 2))] :
    IntersectionSection I V U →ₗ[ZMod 2] CoreSection I U :=
  quotientInclusion (I.pCoreIn 2) (V ⊓ I.pCoreIn 2) U inf_le_right

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
