module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingSylow
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.ComponentEscape

/-!
# The equality-row binary G₂ contradiction on the original plane

The actual wreath quotient gives three-rank two to `K = O²(H)` and makes
K a two-perfect {2,3}-group.  Hence K lies in `O^{3'}(I)` for each original
escaping group I.  For a normalized binary G₂ component X, the existing
core/star identification gives `X = O^{3'}(I)`.  Thus `Mc ∩ X` contains K
and a full Sylow two-subgroup of X.  Equality-row cubic generation makes
this intersection proper, contradicting the genuine binary G₂
proper-Sylow-overgroup three-rank bound.

This applies directly to `ResidualInput` and the literal offender plane.
It neither assumes nor constructs the missing identity `Kc = O^{3'}(Mc)`
or the oversized `PlaneUniquenessPreceding` packet.

Source: Aschbacher--Smith, 15.2.23, printed pp.1116--1117,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open ComponentCatalogue PlaneUniquenessPreceding ChapterC.C27Source
open Chapter13.Section08.Components.Swapped.LinearThree
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The original embedded wreath residual has three-rank exactly two. -/
theorem ResidualInput.residual_rank_two (r : ResidualInput h H B) :
    primeRank 3 (residual H) = 2 := by
  let e := residualQuotientEquiv H r.quotient.some
  let : IsElementaryAbelian 3 (residual H ⧸ pCore 2 (residual H)) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
    (pCore 2 (residual H)) pCore_isPGroup,
    ←IsElementaryAbelian.log_card_eq_primeRank (p := 3),
    Nat.card_congr e.toEquiv,WreathModel.cubicBase_card]
  decide

/-- The actual two-perfect {2,3}-residual lies in the cubic residual of
every original escaping overgroup. -/
theorem ResidualInput.residual_le_threeResidual
    (r : ResidualInput h H B) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    residual H ≤ (primeToResidual 3 I).map I.subtype := by
  have hpi := twoThree_of_wreath H r.quotient.some
  let K := residual H
  have hKI : K ≤ I := le_sup_left.trans
    ((r.residual_sup_planeCentralizer_le hI).trans inf_le_right)
  let K' := K.subgroupOf I
  let e : (pResidual 2 H) ≃* K' :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKI).symm
  have hp : IsPPerfect 2 K' := (isPPerfect_pResidual 2 (G := H)).of_surjective
    e.toMonoidHom e.surjective
  have hKpi : IsPiGroup twoThreePrimes K' :=
    (hpi.of_injective (pResidual 2 H).subtype (pResidual 2 H).subtype_injective).of_equiv e.symm
  have hr : primeToResidual 3 K' = ⊤ := by
    rw [←twoResidual_eq_primeToResidual_three hKpi]
    exact (pResidual_eq_top_iff 2 K').mpr hp
  have hh := map_mono (f := I.subtype) (le_primeToResidual_of_eq_top 3 K' hr)
  rwa [map_subgroupOf_eq_of_le hKI] at hh

/-- The actual binary G₂ component is impossible in the equality row,
using the original plane's Sylow group and residual rank. -/
theorem ResidualInput.binaryG2_false_of_eq
    (r : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : ComponentCatalogue.Normalized H M I X)
    (e : starImage X ((M ⊓ I).pCoreIn 2) X ≃*
      commutator (Atlas.G2.Model (ZMod 2))) : False := by
  let K := residual H
  have hKX : K ≤ X := by
    rw [binaryG2_eq_threeResidual (hsource := h) hI hcore s e]
    exact r.residual_le_threeResidual hI
  have hKM : K ≤ Mc :=
    (le_sup_left.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_left
  have hproper : Mc.subgroupOf X ≠ ⊤ := by
    intro ht
    exact r.binaryG2_component_not_le_partner_of_eq he hI hcore s e
      (subgroupOf_eq_top.mp ht)
  have hP : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ Mc.subgroupOf X := by
    obtain ⟨R,hR⟩ := r.sylow_in_escape hI
    obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal
      (X.subgroupOf I) s.component.2.subnormal
    let a := subgroupOfEquivOfLe s.component.1
    refine ⟨Q.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
    rintro x ⟨y,hy,rfl⟩
    have hyR : (y : I) ∈ R := by
      change y ∈ (R : Subgroup I).subgroupOf (X.subgroupOf I)
      rwa [←hQ]
    have hyS : ((y : I) : G) ∈ planeCentralizer T ⁅V,B⁆ :=
      hR ▸ mem_map_of_mem I.subtype hyR
    exact ((le_sup_right.trans (r.residual_sup_planeCentralizer_le hI)).trans inf_le_left) hyS
  obtain ⟨P,hP⟩ := hP
  let a := normalized_component_input (hsource := h) hI hcore s
  have hu := Atlas.G2.BinaryProperSylowCore.twoCoreQuotient_sylow_overgroup_three_rank_le_one
    (binaryG2CoreEquiv a e) P (Mc.subgroupOf X) hP hproper
  have hl : 2 ≤ primeRank 3 (Mc.subgroupOf X) := by
    have hh := primeRank_mono 3
      (show K.subgroupOf X ≤ Mc.subgroupOf X from fun _ hx => hKM hx)
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hKX),r.residual_rank_two] at hh
    exact hh
  omega

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
