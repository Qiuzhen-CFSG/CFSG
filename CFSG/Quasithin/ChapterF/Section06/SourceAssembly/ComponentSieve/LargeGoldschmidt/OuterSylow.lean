module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.Models
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.ExponentBounds
public import Theory.Mathieu.SylowSixteenObstructions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowElementaryObstruction

/-!
# The catalogue under the marked outer Sylow invariants

A Sylow two-subgroup of order between 64 and 128, of exponent eight and
containing an order-eight element, leaves four sporadic candidates after
the full catalogue sieve. The degree-three bound removes those families.
When its order is 128, a unique elementary sixteen excludes J₂, M₂₂
and M₂₃. Thus the literal component model is M₁₂.
Source: Aschbacher–Smith F.6.18(13), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
open CFSG.Quasithin.ClassificationModels CFSG.Quasithin.ChapterA.Section02
variable {G : Type*} [Group G] [Finite G]

theorem theoremC_mathieu_of_outer_sylow_invariants
    (P : Sylow 2 G) (hlo : 64 ≤ Nat.card P) (hhi : Nat.card P ≤ 128)
    (hexp : ∀ x : P, x ^ 8 = 1) (x : P) (hx : orderOf x = 8)
    (hu : Nat.card P = 128 →
      ∃! E : Subgroup P, IsElementaryAbelian 2 E ∧ Nat.card E = 16)
    (hm : IsTheoremCModel G) : Nonempty (G ≃* Sporadic.Mathieu.M12) := by
  rcases theoremC_models_of_large_sylow_exponent_eight P (by omega) hhi hexp x hx hm with
    hd | h12 | h22 | h23 | hj2
  · obtain ⟨p,hp,ho,hm⟩ := hd
    have hb : Nat.card P ≤ 32 := hm.elim
      (linear_three_model_sylow_card_le_32 P hexp hp ho)
      (unitary_three_model_sylow_card_le_32 P hexp hp ho)
    omega
  · exact h12
  · obtain ⟨e⟩ := h22
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let ePQ : P ≃* Q := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
    have hP : Nat.card P = 128 := by
      rw [Nat.card_congr ePQ.toEquiv, Q.card_eq_multiplicity, Sporadic.Mathieu.m22_order]
      decide +kernel
    exact (Sporadic.Mathieu.m22_sylow_not_unique_elementary_sixteen Q
      (existsUnique_elementary_subgroup_of_equiv ePQ (hu hP))).elim
  · obtain ⟨e⟩ := h23
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let ePQ : P ≃* Q := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
    have hP : Nat.card P = 128 := by
      rw [Nat.card_congr ePQ.toEquiv, Q.card_eq_multiplicity, Sporadic.Mathieu.m23_order]
      decide +kernel
    exact (Sporadic.Mathieu.m23_sylow_not_unique_elementary_sixteen Q
      (existsUnique_elementary_subgroup_of_equiv ePQ (hu hP))).elim
  · obtain ⟨e⟩ := hj2
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let ePQ : P ≃* Q := (P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
    have hP : Nat.card P = 128 := by
      rw [Nat.card_congr ePQ.toEquiv, Q.card_eq_multiplicity,
        Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
      decide +kernel
    exact (Sporadic.LeechRelated.J2.sylow_not_unique_elementary_sixteen Q
      (existsUnique_elementary_subgroup_of_equiv ePQ (hu hP))).elim
end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve.LargeGoldschmidt
