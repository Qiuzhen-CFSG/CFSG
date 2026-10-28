module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.Product
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.Control

/-!
# The literal Chapter 2 consumer of C.1.29

The χ₀ product theorem is applied inside the original local subgroup H.
Membership in He supplies F*(H)=O₂(H). The subgroup inclusion transports
both the outside condition and the actual Thompson commutator, while the
ordered element factorization remains intrinsic to H. This constructs the
exact LocalC129Input consumed by 2.3.8(4), 2.3.9(7), and block normality.

Only the independent earlier C.1.28 outside-block source remains explicit;
its producer is the ChapterC RankOne/ChiProduct family. No final block
recognition or product certificate is an input.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter2
universe u
variable {G : Type u} [Group G] [Finite G] {C : GroupClass.{u}}

/-- The literal C.1.29 input consumed in Chapter 2, derived from the actual
universal C.1.28 source. Every module, outside condition, Thompson action,
and ordered product is carried through the original subgroup inclusion. -/
theorem localC129Input_of_c128_outside
    (outside : ∀ {A : Type u} [Group A] [Finite A], IsSQTK C A →
      generalizedFitting A = pCore 2 A → ∀ (S : Sylow 2 A) (N : Subgroup A),
      (S : Subgroup A).characteristicNormalizerClosure ≤ N → N ≠ ⊤ →
      ∃ L : Subgroup A, ¬L ≤ N ∧ ChapterC.IsChiBlockIn L ∧
        L = ⁅L, elementaryAbelianMaxJ (S : Subgroup A)⁆) :
    LocalC129Input C G := by
  intro H M S hsq hH hc
  have hf : generalizedFitting H = pCore 2 H :=
    (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr (Chapter1.mem_He_iff.mp hH)
  obtain ⟨r, hr, L, hz, hout, hm, hprod⟩ :=
    ChapterC.LocalC129.ordered_chiZero_product_of_c128_outside outside hsq hf S
      (M.subgroupOf H) hc
  refine ⟨⟨r, hr, L, hz, ?_, ?_, hprod⟩⟩
  · intro i hi
    exact hout i (map_le_iff_le_comap.mp hi)
  · intro i
    have hh := congrArg (Subgroup.map H.subtype) (hm i)
    rw [map_commutator, ← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective] at hh
    exact hh
end CFSG.Quasithin.Chapter2
