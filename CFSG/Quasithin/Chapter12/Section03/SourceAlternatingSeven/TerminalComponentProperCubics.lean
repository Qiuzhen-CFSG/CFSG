module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentPreparation
public import Theory.GroupTheory.CComponent.SevenCoverTheta
public import Theory.GroupTheory.PResidual.CubicGenerationModuloTwoCore
public import Theory.GroupTheory.PResidual.FiniteLocalPair

/-!
# Cubic containment in the proper-overcomponent branch

If the point-centralizer component E equals the maximal overcomponent Y,
its relative normality and the actual point-centralizer three-rank bound
put every cubic of that centralizer in Y. The original central quotient
of Y is transported through its subgroup inclusion, retaining both A7
central covers.

For the original Le = O²(C_L(e)), an exponent-three two-core quotient
implies generation by its own cubic elements, hence Le is contained in Y.
The quotient-exponent calculation remains an explicit earlier input; these
lemmas do not assert E=Y, the intermediate-component restriction, or the
remaining uniqueness and natural-action conclusions of 12.3.12.

Source: Aschbacher--Smith, 12.2.8 and the proper-overcomponent paragraph
of 12.3.12, printed pp.797 and 811.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}

private def centralQuotientEquiv (A : Type*) [Group A] :
    ((A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A)) ≃*
      (A ⧸ (center (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))) := by
  let f := (QuotientGroup.mk' (center (A ⧸ pCore 2 A))).comp
    (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = (center (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A)) := by
    ext a
    simp [f]
  exact (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)

private def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

namespace TerminalPoint
variable {P : TerminalPoint S D}

/-- Cubic generation of the literal two-residual; no perfectness is assumed. -/
theorem Le_cubic_generated_of_quotient_cube
    (hcube : ∀ x : P.Le ⧸ pCore 2 P.Le, x ^ 3 = 1) :
    closure {x : G | x ∈ P.Le ∧ orderOf x = 3} = P.Le := by
  have hp : IsPPerfect 2 P.Le :=
    isPPerfect_embedded_pResidual_of_finite 2 (L ⊓ P.pointCentralizer)
  have he := congrArg (map P.Le.subtype)
    (cubic_closure_eq_top_of_twoPerfect_of_quotient_cube hp hcube)
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at he
  have hs : P.Le.subtype '' {x : P.Le | orderOf x = 3} =
      {x : G | x ∈ P.Le ∧ orderOf x = 3} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, (P.Le.orderOf_coe y).trans hy⟩
    · rintro ⟨hx, h3⟩
      exact ⟨⟨x, hx⟩, (P.Le.orderOf_coe ⟨x, hx⟩).symm.trans h3, rfl⟩
  rwa [hs] at he

namespace Overcomponents
variable (F : P.Overcomponents)

/-- The 12.2.8 containment in the original point centralizer, including 3.A7. -/
theorem cubic_mem_of_eq_maximal {W : Subgroup G} (SY : Setup T F.Y W)
    (hEY : F.E = F.Y) {x : G} (hx : x ∈ P.pointCentralizer)
    (h3 : orderOf x = 3) : x ∈ F.Y := by
  let C := P.pointCentralizer
  have hYC : F.Y ≤ C := hEY ▸ F.component.1
  let X := F.Y.subgroupOf C
  let : X.Normal := (normal_subgroupOf_iff_le_normalizer hYC).mpr (hEY ▸ F.normalizes)
  have hX : X.IsCComponent := by
    change (F.Y.subgroupOf C).IsCComponent
    rw [← hEY]
    exact F.component.2
  let eX : (X ⧸ pCore 2 X) ≃* (F.Y ⧸ pCore 2 F.Y) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hYC) (pCore_map_iso 2 _)
  let : IsQuasisimple (F.Y ⧸ pCore 2 F.Y) := SY.hypothesis.quasisimple
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv eX.symm
  let e := (centerQuotientCongr eX).trans ((centralQuotientEquiv F.Y).trans SY.quotient)
  exact SevenCComponentTheta.order_three_mem_of_central_quotient_seven X hX e
    (P.pointCentralizer_sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    ((C.orderOf_coe ⟨x, hx⟩).symm.trans h3)

/-- All cubic generators of the point centralizer lie in the same overcomponent. -/
theorem cubic_closure_le_of_eq_maximal {W : Subgroup G} (SY : Setup T F.Y W)
    (hEY : F.E = F.Y) :
    closure {x : G | x ∈ P.pointCentralizer ∧ orderOf x = 3} ≤ F.Y := by
  apply (closure_le F.Y).mpr
  intro x hx
  exact F.cubic_mem_of_eq_maximal SY hEY hx.1 hx.2

/-- The original Le containment from its source cubic-generation input. -/
theorem Le_le_of_eq_maximal_of_cubic_generation {W : Subgroup G}
    (SY : Setup T F.Y W) (hEY : F.E = F.Y)
    (hgen : P.Le ≤ closure {x : G | x ∈ P.Le ∧ orderOf x = 3}) : P.Le ≤ F.Y := by
  apply hgen.trans
  apply (Subgroup.closure_mono ?_).trans (F.cubic_closure_le_of_eq_maximal SY hEY)
  intro x hx
  exact ⟨((map_subtype_le (pResidual 2 (L ⊓ P.pointCentralizer : Subgroup G))).trans
    inf_le_right) hx.1, hx.2⟩

/-- The point-stabilizer quotient calculation feeds the literal Le consumer. -/
theorem Le_le_of_eq_maximal_of_quotient_cube {W : Subgroup G}
    (SY : Setup T F.Y W) (hEY : F.E = F.Y)
    (hcube : ∀ x : P.Le ⧸ pCore 2 P.Le, x ^ 3 = 1) : P.Le ≤ F.Y :=
  F.Le_le_of_eq_maximal_of_cubic_generation SY hEY
    (Le_cubic_generated_of_quotient_cube hcube).ge

end Overcomponents
end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
