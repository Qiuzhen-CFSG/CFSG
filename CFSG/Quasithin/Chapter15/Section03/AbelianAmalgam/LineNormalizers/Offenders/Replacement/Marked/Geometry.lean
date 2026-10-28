module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.FixedImages
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.OriginalData
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.FactorRestriction
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Geometry.SourceOperators
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.Inheritance
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked.PairingData
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Marked
/-!
# Actual marked quotient and fixed-space geometry after replacement

Marked quotient factors commute in the quotient, hence in every action killing
the core. The cubic operator calculation identifies the images of actual fixed
subgroups with the complementary quotient fixed spaces. Together these construct
`PairedGeometry`, including centralizer invariance only where it is justified:
on the quotient.

The temporary core acts trivially by the original natural-action kernel theorem
and the proved replacement-core equality. `OriginalData.pairedGeometry` assembles
the inherited marked factors and the operator identities from the original local
data. It retains the original first coordinate and the actual centralizer image.
`chosenPairedGeometry` also chooses the required nonidentity original residual
image; its existence follows from U = [U,Y_E] and the nontrivial four-group E.

The summands are the images of the literal fixed subgroups. Fixed representatives
are obtained by the correction inside E proved in `Geometry.FixedImages`.
Both summands are centralizer-invariant, and the raw fixed subgroups generate U
with trivial intersection. The raw conjugacy and denominator-intersection
identities, and the actual order-two denominator fixed line, remain available
from the narrowly imported geometry and original-operator leaves.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G D : Type*} [Group G] [Group D]

namespace MarkedQuotientFactors
variable {A C Q : Subgroup G} [Q.Normal]

/-- The actual centralizer image commutes with every element of the marked first factor. -/
theorem quotient_commute (d : MarkedQuotientFactors A C Q)
    (c a : G) (hc : c ∈ C) (ha : a ∈ A) :
    Commute (QuotientGroup.mk' Q c) (QuotientGroup.mk' Q a) := by
  apply Commute.of_map (f := d.equiv.toMonoidHom) d.equiv.injective
  have ha' := mem_map_of_mem (d.equiv.toMonoidHom.comp (QuotientGroup.mk' Q)) ha
  rw [d.first_factor] at ha'
  have ha2 : (d.equiv (a : G ⧸ Q)).2 = 1 := ha'.2
  change Commute (d.equiv (QuotientGroup.mk' Q c)) (d.equiv (QuotientGroup.mk' Q a))
  have hae : d.equiv (QuotientGroup.mk' Q a) =
      ((d.equiv (QuotientGroup.mk' Q a)).1, 1) := Prod.ext rfl ha2
  rw [d.centralizer_factor ⟨c, hc⟩, hae]
  apply Prod.ext <;> simp

/-- The factor commutation is inherited by every representation killing the core. -/
theorem action_commute {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (d : MarkedQuotientFactors A C Q) (ρ : Representation (ZMod 2) G X)
    (hQ : Q ≤ ρ.ker) (c a : G) (hc : c ∈ C) (ha : a ∈ A) :
    Commute (ρ c) (ρ a) := by
  exact (d.quotient_commute c a hc ha).map (QuotientGroup.lift Q ρ hQ)

end MarkedQuotientFactors

/-- Construct the literal paired geometry from marked factors and raw operator relations. -/
noncomputable def pairedGeometry_of_operatorRelations
    (U E A C Q : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    [E.Normal] [Q.Normal] (f : G →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer (U : Set G)) (τ y : G)
    (hEU : E ≤ U) (hτA : τ ∈ A) (hyA : y ∈ A)
    (factors : MarkedQuotientFactors A C Q)
    (hQ : Q ≤ (MarkedSection.action U E f hf hker).ker)
    (operators : MarkedOperatorRelations U f hf hker τ y) :
    PairedGeometry U E A C Q f hf hker τ y where
  line_le := hEU
  factors := factors
  core_kills := hQ
  complementary := MarkedSection.fixedImage_isCompl U E f hf hker τ y operators
  conjugate := MarkedSection.fixedImage_conjugate U E f hf hker τ y
  first_invariant c hc w hw := by
    rw [MarkedSection.fixedImage_eq_ker U E f hf hker τ y operators] at hw ⊢
    have hw' : MarkedSection.action U E f hf hker τ w = w := sub_eq_zero.mp hw
    have h := LinearMap.congr_fun
      (factors.action_commute (MarkedSection.action U E f hf hker) hQ c τ hc hτA).eq w
    apply sub_eq_zero.mpr
    exact h.symm.trans (congrArg (MarkedSection.action U E f hf hker c) hw')
  commutes c hc := factors.action_commute (MarkedSection.action U E f hf hker) hQ
    c y⁻¹ hc (A.inv_mem hyA)

namespace PairedGeometry
variable {U E A C Q : Subgroup G} [U.Normal] [IsElementaryAbelian 2 U] [E.Normal] [Q.Normal]
  {f : G →* D} {hf : Function.Surjective f}
  {hker : f.ker = centralizer (U : Set G)} {τ y : G}

/-- Conjugacy and commutation also give invariance of the second literal fixed image. -/
theorem second_invariant (d : PairedGeometry U E A C Q f hf hker τ y)
    (c : G) (hc : c ∈ C) (w : Additive U ⧸ Representation.NormalElementaryQuotient.subspace U (E.subgroupOf U))
    (hw : w ∈ MarkedSection.fixedImage U E (y⁻¹ * τ * y)) :
    MarkedSection.action U E f hf hker c w ∈
      MarkedSection.fixedImage U E (y⁻¹ * τ * y) := by
  rw [d.conjugate] at hw ⊢
  obtain ⟨v, hv, rfl⟩ := hw
  exact ⟨MarkedSection.action U E f hf hker c v, d.first_invariant c hc v hv,
    (LinearMap.congr_fun (d.commutes c hc).eq v).symm⟩
end PairedGeometry

open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
  GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
open scoped commutatorElement
variable [Finite G] {V M : Subgroup G}

/-- The original source action and local core bounds kill the temporary core on U/E. -/
theorem temporary_core_kills_section_of_original_action
    (d : NaturalAction V M) (Y T E : Subgroup G) [IsMulCommutative V]
    [((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))]
    [(E.subgroupOf (temporaryLineNormalizer T V E)).Normal]
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hY : lineNormalizer E ≤ normalizer (lineY Y E : Set G))
    (hVT : V ≤ lineT T E) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hQK : lineQ E ≤ Descent.sectionKernel V E)
    (hlocal : (lineY Y E ⊔ lineT T E).pCoreIn 2 ≤ T ⊓ centralizer (E : Set G))
    (hcomm : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E)
    (hUH : lineV V E ≤ temporaryLineNormalizer T V E)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      (((lineV V E).subgroupOf (temporaryLineNormalizer T V E)) : Set (temporaryLineNormalizer T V E))) :
    (temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E) ≤
      (MarkedSection.action ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
        (E.subgroupOf (temporaryLineNormalizer T V E)) f hf hker).ker := by
  rw [temporary_section_action_ker T V E hUH f hf hker]
  have hQ := temporaryCore_eq_of_original_action d Y T E hYM hEV hcard hs himage
    hYcore hY hVT P hP hQK hlocal hcomm
  have hQK' : temporaryCore T V E ≤ Descent.sectionKernel V E := by
    rw [hQ, Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
    exact inf_le_right
  intro q hq
  exact hQK' hq


namespace Geometry.OriginalData
variable {Y T E Pc : Subgroup G} [IsMulCommutative V]

/-- Intermediate assembly in H from marked factors and raw operator relations. -/
noncomputable def pairedGeometry_of_prerequisites
    (d : Geometry.OriginalData Y T V M E Pc)
    [((lineV V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [IsElementaryAbelian 2 ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))]
    [(E.subgroupOf (temporaryLineNormalizer T V E)).Normal]
    [((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)).Normal]
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      (((lineV V E).subgroupOf (temporaryLineNormalizer T V E)) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (factors : MarkedQuotientFactors
      ((lineY Y E ⊔ zpowers d.marked.tau).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)))
    (operators : MarkedOperatorRelations
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E)) f hf hker d.tau
        (d.residualElement y hy)) :
    PairedGeometry
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
      (E.subgroupOf (temporaryLineNormalizer T V E))
      ((lineY Y E ⊔ zpowers d.marked.tau).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E))
      f hf hker d.tau (d.residualElement y hy) := by
  apply pairedGeometry_of_operatorRelations _ _ _ _ _ f hf hker d.tau
    (d.residualElement y hy) ?_ ?_ ?_ factors ?_ operators
  · intro e he
    exact le_conjugateSpanBy V _ (d.line_le he)
  · exact mem_sup_right (mem_zpowers d.marked.tau)
  · exact mem_sup_left hy
  · exact temporary_core_kills_section_of_original_action d.action Y T E d.Y_le
      d.line_le d.line_card d.singular d.residual_image d.residual_kernel d.residual_normal
      d.module_le_sylow d.sylow d.sylow_image d.core_le_kernel d.local_core
      d.seed_commutator d.span_le_temporary f hf hker

end Geometry.OriginalData

namespace Geometry.OriginalData
variable {Y T E Pc : Subgroup G}
attribute [local instance] temporaryCore_normal

/-- The moved original module supplies a residual element nontrivial in the original core quotient. -/
theorem exists_marked_residual (d : OriginalData Y T V M E Pc) :
    ∃ y : G, ∃ hy : y ∈ lineY Y E,
      Descent.QuotientIdentification.quotientMap E ⟨y, (lineY_le Y E hy).2⟩ ≠ 1 := by
  by_contra! h
  have hcentral : lineY Y E ≤ centralizer (lineV V E : Set G) := by
    intro y hy
    apply d.residual_core_centralizes_span
    change y ∈ (lineY Y E).pCoreIn 2
    rw [Descent.QuotientIdentification.lineY_twoCore Y E
      ((normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_right)).mpr
        d.residual_normal)]
    exact ⟨hy, ⟨⟨y, (lineY_le Y E hy).2⟩,
      (QuotientGroup.eq_one_iff _).mp (h y hy), rfl⟩⟩
  have hzero : lineV V E = ⊥ := by
    rw [d.residual_span, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hE : E = ⊥ := le_bot_iff.mp (by
    rw [← hzero]
    exact d.line_le.trans (le_conjugateSpanBy V _))
  have hc := d.line_card
  rw [hE, Subgroup.card_bot] at hc
  omega

/-- A selected original residual element, independent of the faithful quotient used later. -/
noncomputable def markedResidual (d : OriginalData Y T V M E Pc) : lineY Y E :=
  ⟨d.exists_marked_residual.choose, d.exists_marked_residual.choose_spec.choose⟩

/-- The selected element has the nonidentity original image required in the source. -/
theorem markedResidual_image_ne_one (d : OriginalData Y T V M E Pc) :
    Descent.QuotientIdentification.quotientMap E
      ⟨d.markedResidual, (lineY_le Y E d.markedResidual.property).2⟩ ≠ 1 :=
  d.exists_marked_residual.choose_spec.choose_spec

variable [IsMulCommutative V]

/-- Complete conditional source geometry, with all temporary factors, operator identities and
fixed-representative lifting derived from the original local data. -/
noncomputable def pairedGeometry (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) :
    let := d.module_normal
    let := d.module_elementary
    let := d.line_normal
    PairedGeometry
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E))
      (E.subgroupOf (temporaryLineNormalizer T V E))
      ((lineY Y E ⊔ zpowers d.marked.tau).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E))
      ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E))
      f hf hker d.tau (d.residualElement y hy) := by
  let := d.module_normal
  let := d.module_elementary
  let := d.line_normal
  exact d.pairedGeometry_of_prerequisites f hf hker y hy d.markedQuotientFactors
    (d.markedOperatorRelations f hf hker y hy hne)

/-- The source geometry with the nonidentity residual element chosen from the original data. -/
noncomputable def chosenPairedGeometry (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E))) :=
  d.pairedGeometry f hf hker d.markedResidual d.markedResidual.property
    d.markedResidual_image_ne_one

/-- The assembled geometry keeps the original first coordinate at every element of H. -/
theorem pairedGeometry_first_coordinate (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) (h : temporaryLineNormalizer T V E) :
    let := d.module_normal
    let := d.module_elementary
    let := d.line_normal
    ((d.pairedGeometry f hf hker y hy hne).factors.equiv
      (QuotientGroup.mk' _ h)).1 =
        (d.marked.equiv (Descent.QuotientIdentification.quotientMap E
          (inclusion inf_le_left h))).1 :=
  d.markedQuotientFactors_fst h

/-- The actual ambient fixed subgroups generate the original module and meet trivially. -/
theorem markedFixed_decomposition (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) : Set (temporaryLineNormalizer T V E)))
    (y : G) (hy : y ∈ lineY Y E)
    (hne : Descent.QuotientIdentification.quotientMap E
      ⟨y, (lineY_le Y E hy).2⟩ ≠ 1) :
    markedFixed (lineV V E) d.marked.tau ⊔
        markedFixed (lineV V E) (y⁻¹ * d.marked.tau * y) = lineV V E ∧
      markedFixed (lineV V E) d.marked.tau ⊓
        markedFixed (lineV V E) (y⁻¹ * d.marked.tau * y) = ⊥ := by
  let := d.module_normal
  let := d.module_elementary
  let H := temporaryLineNormalizer T V E
  let U := (lineV V E).subgroupOf H
  have hop := d.markedOperatorRelations f hf hker y hy hne
  constructor
  · have hh := congrArg (Subgroup.map H.subtype)
      (MarkedSection.markedFixed_sup_eq U f hf hker d.tau (d.residualElement y hy) hop)
    rw [Subgroup.map_sup, intrinsic_markedFixed_map H (lineV V E) d.span_le_temporary,
      intrinsic_markedFixed_map H (lineV V E) d.span_le_temporary,
      map_subgroupOf_eq_of_le d.span_le_temporary] at hh
    exact hh
  · have hh := congrArg (Subgroup.map H.subtype)
      (MarkedSection.markedFixed_inf_eq_bot U f hf hker d.tau (d.residualElement y hy) hop)
    rw [map_inf _ _ _ H.subtype_injective,
      intrinsic_markedFixed_map H (lineV V E) d.span_le_temporary,
      intrinsic_markedFixed_map H (lineV V E) d.span_le_temporary, Subgroup.map_bot] at hh
    exact hh


end Geometry.OriginalData

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
