module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSixC28
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJankoCore
-- The mapped-core commutant argument and residual-core transport are independent
-- of the A7 module; reuse those private general lemmas on the actual A6 orbit.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.SevenOrdinaryJankoCore

/-!
# The actual alternating-six orbit in the center of a placed two-core

The original graph-pair action has trivial invertible commutant. Its odd
fixed residual covers the original component modulo the two-core, so the
same commutant is trivial for the literal residual. An ambient normal
two-core therefore centralizes the whole orbit, whose actual order 256
bounds the center of that core after faithful native placement.
Source: Aschbacher--Smith 4.4.3 and H.7, printed pp.622--623 and 388--389,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem six_residual_centralizer_eq_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (alternatingNatural 6)))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (f : Additive D.sourceOrbit ≃ₗ[ZMod 2] Additive D.sourceOrbit)
    (hf : ∀ r : oddActorResidual L A, ∀ v,
      f (doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes
        (inclusion ((oddActorResidual_le L A).trans inf_le_left) r) v) =
      doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes
        (inclusion ((oddActorResidual_le L A).trans inf_le_left) r) (f v)) :
    f = LinearEquiv.refl _ _ := by
  obtain ⟨hcover,_,_,_⟩ := D.doubledOrbit_oddActorResidual_cover h A
    (by simpa only [←D.sourceOrbit_eq] using hA) ho
  have hcore := D.component_core_centralizes h
  apply D.sourceOrbit_six_centralizer_eq_one h hd hmodel f
  intro l v
  have hl : l.val ∈ (oddActorResidual L A : Set G) * (L.pCoreIn 2 : Set G) :=
    hcover ▸ l.property
  obtain ⟨r,hr,c,hc,he⟩ := hl
  let rL : L := ⟨r,(oddActorResidual_le L A hr).1⟩
  let cL : L := ⟨c,pCoreIn_le 2 L hc⟩
  have heL : l = rL * cL := Subtype.ext he.symm
  let ρ := doubledSeedAction L D.sourceOrbit D.sourceOrbit_component_normalizes
  have hcfix (w : Additive D.sourceOrbit) : ρ cL w = w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change c * (w.toMul : G) * c⁻¹ = (w.toMul : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hcore hc w.toMul w.toMul.property).symm
  change f (ρ l v) = ρ l (f v)
  simp only [heL,map_mul,Module.End.mul_apply,hcfix]
  exact hf ⟨r,hr⟩ v

/-- The actual doubled A₆ orbit embeds in the center of the placed full two-core.
The native equivalence preserves the original residual and orbit inclusions. -/
theorem sourceOrbit_six_mapped_core_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (alternatingNatural 6)))
    (A : Subgroup G) (hAC : A ≤ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A)) (K₀ : Subgroup G)
    (hr : oddActorResidual L A ≤ K₀) (hWK : D.sourceOrbit ≤ K₀)
    {Q : Type*} [Group Q] (m : K₀ ≃* Q) (M : Subgroup Q)
    (hrM : (m.toMonoidHom.comp (inclusion hr)).range ≤ M)
    (hwM : (m.toMonoidHom.comp (inclusion hWK)).range ≤ M)
    (hnR : M ≤ normalizer ((m.toMonoidHom.comp (inclusion hr)).range : Set Q))
    (hnW : M ≤ normalizer ((m.toMonoidHom.comp (inclusion hWK)).range : Set Q)) :
    256 ≤ Nat.card (center (pCore 2 M)) := by
  let : Finite Q := Finite.of_surjective m m.surjective
  let R := oddActorResidual L A
  let U := D.sourceOrbit
  let r := m.toMonoidHom.comp (inclusion hr)
  let w := m.toMonoidHom.comp (inclusion hWK)
  have hir : Function.Injective r := m.injective.comp (inclusion_injective hr)
  have hiw : Function.Injective w := m.injective.comp (inclusion_injective hWK)
  have hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) :=
    le_inf (hAC.trans (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd).centralizer_le) hAC
  have hRL : R ≤ L := (oddActorResidual_le L A).trans inf_le_left
  let ψ : R →* MulAut U := U.normalizerMonoidHom.comp
    (inclusion (hRL.trans D.sourceOrbit_component_normalizes))
  have hcore : pCore 2 R ≤ ψ.ker := by
    intro x hx
    change ψ x = 1
    ext y
    change (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      (D.residual_core_centralizes h A hA ho (mem_map_of_mem R.subtype hx) y y.property).symm
  have hmark (x : R) (y : U) : w (ψ x y) = r x * w y * (r x)⁻¹ := by
    change m (inclusion hWK (ψ x y)) =
      m (inclusion hr x) * m (inclusion hWK y) * (m (inclusion hr x))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    apply congrArg m
    rfl
  have hc := mapped_core_centralizes_of_commutant M r w hir hiw hrM hnR hnW
    ψ hcore hmark (by
      intro f hf
      apply D.six_residual_centralizer_eq_one h hd hmodel A hA ho f
      exact hf)
  have hp : IsPGroup 2 w.range :=
    (IsElementaryAbelian.isPGroup 2 U).of_surjective w.rangeRestrict w.rangeRestrict_surjective
  have hWP : w.range ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes hp hwM hnW
  have hZ : w.range ≤ (center (M.pCoreIn 2)).map (M.pCoreIn 2).subtype := by
    intro x hx
    refine ⟨⟨x,hWP hx⟩,mem_center_iff.mpr (fun p => ?_),rfl⟩
    exact Subtype.ext (hc p.property x hx).symm
  have hh := card_le_of_le hZ
  rw [card_map_of_injective (M.pCoreIn 2).subtype_injective] at hh
  let eP : pCore 2 M ≃* M.pCoreIn 2 :=
    (pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  have hcard : Nat.card w.range = 256 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hiw).symm.toEquiv]
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,D.sourceOrbit_six_dimension h hd hmodel] at he
    exact he
  exact hcard ▸ hh.trans_eq (Nat.card_congr (centerCongr eP).toEquiv).symm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
