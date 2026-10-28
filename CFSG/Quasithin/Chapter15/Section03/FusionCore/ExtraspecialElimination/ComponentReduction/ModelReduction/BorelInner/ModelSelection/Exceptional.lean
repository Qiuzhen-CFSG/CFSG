module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Transport
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.Representation.HexacodeAction.ThreeRank
public import Theory.Representation.HexacodeAction.OuterTwo
public import Theory.GroupTheory.CComponent.ExceptionalQuotients
public import Theory.GroupTheory.CComponent.HexacodeTheta

/-!
# Exceptional component cases in 15.3.49(k)

Both exceptional models give the strict three-rank hypothesis in A.3.18
through actual multiplicative equivalences. Their component images in
H/O₂(H) and H/O₃′(H) are isomorphic because the kernels restricted to the
component agree. No equality between the ambient cores is asserted.

The ordinary residual argument for A₇ and the central-cover theta argument
for the concrete hexacode group work inside the relative normalizer: every
order-three generator of Y₀ lies in L. For the cover, its exponent-three
Sylow subgroup and outer two-group exclude outside order-three actors.
Thus both models imply Y₀ ≤ L, contradicting Y₀ ≰ ⟨L^T⟩. These intrinsic
arguments discharge the needed A.3.18 alternatives without a catalogue
premise or an ambient normality assumption.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.18,
printed pp.51–52, and proof of 15.3.49(k), pp.1143–1144.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Exceptional

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z A : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : SourceSetup κ H M Y V Y0 L ZS Z A T)

include d

/-- The relative component quotient is the actual star image. -/
noncomputable def relativeStarEquiv :
    ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* starImage H L :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (component_le d))
    (pCore_map_iso 2 _)).trans
      (starQuotientEquiv H L (component_le d) d.component_in_H.subnormal)

/-- Transporting the concrete model rank supplies the intrinsic component rank. -/
theorem component_threeRank_of_star (hr : 2 ≤ primeRank 3 (starImage H L)) :
    2 ≤ primeRank 3 (L.subgroupOf H) := by
  rw [← primeRank_congr 3 (relativeStarEquiv d)] at hr
  exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide)
    (pCore 2 (L.subgroupOf H)) pCore_isPGroup)

/-- The two independent three-cycles in A₇ give the required strict rank. -/
theorem seven_threeRank (e : starImage H L ≃* alternatingGroup (Fin 7)) :
    1 < primeRank 3 (L.subgroupOf H) := by
  apply component_threeRank_of_star d
  rw [primeRank_congr 3 e]
  exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)

/-- This uses the elementary nine in the genuine triple cover itself. -/
theorem cover_threeRank (e : starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) :
    1 < primeRank 3 (L.subgroupOf H) := by
  apply component_threeRank_of_star d
  rw [primeRank_congr 3 e]
  exact Representation.Hexacode.two_le_primeRank_even

/-- All A.3.18 hypotheses for this relative component; quasisimplicity is
precisely the independently supplied input of the task. -/
theorem application_hypotheses (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (he : Nonempty (starImage H L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    IsSQTK κ H ∧ (L.subgroupOf H).IsCComponent ∧
      IsQuasisimple ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ∧
      1 < primeRank 3 (L.subgroupOf H) := by
  let _ := hq
  refine ⟨d.sqtk, d.component_in_H, ?_, ?_⟩
  · exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (component_le d))
        (pCore_map_iso 2 _)).symm
  · rcases he with h7 | h6
    · exact h7.elim (seven_threeRank d)
    · exact h6.elim (cover_threeRank d)

private theorem relative_primeCore_bot
    (hc : pPrimeCore 3 (starImage H L) = ⊥) :
    pPrimeCore 3 ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) = ⊥ := by
  apply map_injective (f := (relativeStarEquiv d).toMonoidHom) (relativeStarEquiv d).injective
  rw [pPrimeCore_map_iso, Subgroup.map_bot, hc]

/-- The kernel on L of H → H/O₃′(H) is exactly its intrinsic two-core. -/
theorem threePrimeCore_comap (hc : pPrimeCore 3 (starImage H L) = ⊥) :
    (pPrimeCore 3 H).comap (L.subgroupOf H).subtype = pCore 2 (L.subgroupOf H) :=
  CComponentExceptionalQuotient.core_comap _ d.component_in_H.subnormal
    (relative_primeCore_bot d hc)

/-- Compare the component images, keeping both distinct ambient quotients. -/
noncomputable def starThreePrimeEquiv (hc : pPrimeCore 3 (starImage H L) = ⊥) :
    starImage H L ≃* (L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 3 H)) :=
  (relativeStarEquiv d).symm.trans
    (CComponentExceptionalQuotient.quotientEquiv _ d.component_in_H.subnormal
      (relative_primeCore_bot d hc))

omit d [Finite G] in
/-- Triviality of the three-prime core is transported through the actual model. -/
theorem seven_star_primeCore (e : starImage H L ≃* alternatingGroup (Fin 7)) :
    pPrimeCore 3 (starImage H L) = ⊥ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [pPrimeCore_map_iso, Subgroup.map_bot, CComponentExceptionalQuotient.seven_primeCore_bot]

omit d [Finite G] in
/-- The central subgroup of the triple cover has order three and survives
this quotient; it is not removed as part of a three-prime kernel. -/
theorem cover_star_primeCore (e : starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) :
    pPrimeCore 3 (starImage H L) = ⊥ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [pPrimeCore_map_iso, Subgroup.map_bot, CComponentExceptionalQuotient.even_primeCore_bot]

/-- The A₇ identification in the precise quotient used by A.3.18. -/
noncomputable def sevenThreePrimeEquiv (e : starImage H L ≃* alternatingGroup (Fin 7)) :
    (L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 3 H)) ≃*
      alternatingGroup (Fin 7) :=
  (starThreePrimeEquiv d (seven_star_primeCore e)).symm.trans e

/-- The genuine triple cover, including its center, survives the three-prime quotient. -/
noncomputable def coverThreePrimeEquiv (e : starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) :
    (L.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 3 H)) ≃*
      Atlas.Codes.HexEvenAutomorphisms :=
  (starThreePrimeEquiv d (cover_star_primeCore e)).symm.trans e

/-- The ordinary A.3.18 residual argument forces Y₀ into the A₇ component. -/
theorem y0_le_of_seven (e : starImage H L ≃* alternatingGroup (Fin 7)) : Y0 ≤ L := by
  rw [← d.theta_eq]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hx, hx3⟩
  have hxY : x ∈ Y0 := d.theta_eq ▸ (subset_closure ⟨hx, hx3⟩)
  have hxN : x ∈ normalizer (L : Set G) :=
    (le_normalizer_iff_commutator_le_left.mpr d.commutator_eq.ge) hxY
  exact alternatingGroup.SevenComponent.order_three_mem (L.subgroupOf H)
    d.component_in_H ((relativeStarEquiv d).trans e)
    (d.sqtk.stronglyQuasithin 3 (by decide) (by decide))
    (x := ⟨x, hx.2⟩) (by simpa using hx3) (by
      rw [← subgroupOf_normalizer_eq (component_le d)]
      exact hxN)

/-- The A₇ branch is impossible under the contrary containment assumption. -/
theorem not_seven (hout : ¬ Y0 ≤ localSpan L T) :
    ¬ Nonempty (starImage H L ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  exact hout ((y0_le_of_seven d e).trans (le_conjugateSpanBy L T))

/-- The concrete triple-cover case of A.3.18(3a) puts each theta generator
in the relative component, hence forces Y₀ into L. -/
theorem y0_le_of_cover (e : starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) :
    Y0 ≤ L := by
  rw [← d.theta_eq]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hx, hx3⟩
  have hxY : x ∈ Y0 := d.theta_eq ▸ (subset_closure ⟨hx, hx3⟩)
  have hxN : x ∈ normalizer (L : Set G) :=
    (le_normalizer_iff_commutator_le_left.mpr d.commutator_eq.ge) hxY
  exact HexacodeTheta.order_three_mem (L.subgroupOf H)
    d.component_in_H ((relativeStarEquiv d).trans e)
    (d.sqtk.stronglyQuasithin 3 (by decide) (by decide))
    (x := ⟨x, hx.2⟩) (by simpa using hx3) (by
      rw [← subgroupOf_normalizer_eq (component_le d)]
      exact hxN)

/-- The genuine triple cover is impossible under the contrary containment
assumption; its central subgroup of order three has not been factored out. -/
theorem not_cover (hout : ¬ Y0 ≤ localSpan L T) :
    ¬ Nonempty (starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rintro ⟨e⟩
  exact hout ((y0_le_of_cover d e).trans (le_conjugateSpanBy L T))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Exceptional
