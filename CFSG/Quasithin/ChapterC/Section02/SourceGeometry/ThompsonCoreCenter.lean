module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.CoreStarNormalizerAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalGeometry

/-!
# Central-cover placement from the original Thompson image

If J(R)* lies in X*, its conjugation action on the perfect central cover
X/O₂(X) is inner. The preimage of the center therefore normalizes
J(R)O₂(X). This subgroup lies between J(R) and R, so Thompson heredity
makes its Thompson subgroup J(R). Original C.2.3 characteristic-normalizer
control now places the entire central preimage in the original marked N.
The radical itself may still act externally; no faithful core-to-star
map is assumed in this lifting argument.

Source: Aschbacher--Smith C.2.3 and the Thompson normalizer argument in
C.2.7, printed pp.144--147; used in 15.2.23, pp.1116--1117.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] {X R : Subgroup G}

private theorem central_preimage_normalizes_of_inner
    (hR : R ≤ normalizer (X : Set G))
    (hQ : X.pCoreIn 2 ≤ R)
    (hi : ∀ r : R, pCoreNormalizerAction 2 X (inclusion hR r) ∈
      MulAut.innerSubgroup (X ⧸ pCore 2 X)) :
    (centralPreimage (pCore 2 X)).map X.subtype ≤ normalizer (R : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  apply le_trans (commutator_le.mpr ?_) hQ
  intro r hr c hc
  obtain ⟨x,hx,rfl⟩ := hc
  obtain ⟨z,hz⟩ := hi ⟨r,hr⟩
  have hfix : pCoreNormalizerAction 2 X (inclusion hR ⟨r,hr⟩)
      (QuotientGroup.mk' (pCore 2 X) x) = QuotientGroup.mk' (pCore 2 X) x := by
    rw [←hz]
    change z * QuotientGroup.mk' (pCore 2 X) x * z⁻¹ = _
    rw [mem_center_iff.mp hx z, mul_inv_cancel_right]
  have hmem : X.normalizerMonoidHom (inclusion hR ⟨r,hr⟩) x / x ∈ pCore 2 X :=
    QuotientGroup.eq_iff_div_mem.mp ((pCoreNormalizerAction_mk 2 X _ x).symm.trans hfix)
  refine ⟨_,hmem,?_⟩
  simp only [div_eq_mul_inv, commutatorElement_def]
  rfl

variable [Finite G]

/-- Only the Thompson subgroup needs to act internally on the core quotient.
Its join with O₂(X) has the same Thompson subgroup as R. -/
theorem central_preimage_normalizes_thompson_of_inner
    (hR : R ≤ normalizer (X : Set G))
    (hQ : X.pCoreIn 2 ≤ R)
    (hi : ∀ r : elementaryAbelianMaxJ R,
      pCoreNormalizerAction 2 X ⟨r,hR ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1) r.property)⟩ ∈
        MulAut.innerSubgroup (X ⧸ pCore 2 X)) :
    (centralPreimage (pCore 2 X)).map X.subtype ≤
      normalizer (elementaryAbelianMaxJ R : Set G) := by
  let A := elementaryAbelianMaxJ R ⊔ X.pCoreIn 2
  have hAR : A ≤ R := sup_le (sSup_le fun _ hA => hA.1) hQ
  have hAN : A ≤ normalizer (X : Set G) := hAR.trans hR
  have he : elementaryAbelianMaxJ A = elementaryAbelianMaxJ R :=
    elementaryAbelianMaxJ_eq_of_intermediate R A le_sup_left hAR
  have hinner : A.subgroupOf (normalizer (X : Set G)) ≤
      (MulAut.innerSubgroup (X ⧸ pCore 2 X)).comap (pCoreNormalizerAction 2 X) := by
    rw [subgroupOf_sup (show elementaryAbelianMaxJ R ≤ normalizer (X : Set G) from
      (sSup_le fun _ hA => hA.1).trans hR)
      (show X.pCoreIn 2 ≤ normalizer (X : Set G) from hQ.trans hR)]
    apply sup_le
    · intro r hr
      exact hi ⟨r,hr⟩
    · intro r hr
      have hx : (r : G) ∈ X := pCoreIn_le 2 X hr
      exact ⟨QuotientGroup.mk' (pCore 2 X) ⟨r,hx⟩,
        (pCoreNormalizerAction_on_component 2 X ⟨r,hx⟩).symm⟩
  have hn := central_preimage_normalizes_of_inner hAN le_sup_right
    (fun a => hinner (show inclusion hAN a ∈ A.subgroupOf (normalizer (X : Set G)) from a.property))
  exact hn.trans ((normalizer_le_normalizer_elementaryAbelianMaxJ A).trans_eq
    (congrArg (fun B : Subgroup G => normalizer (B : Set G)) he))

variable {I N : Subgroup G}

/-- An inner Thompson star image induces inner automorphisms on the literal
full core quotient, including its central covering kernel. -/
theorem thompson_core_action_inner_of_star_inner
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hi : starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X)
    (r : elementaryAbelianMaxJ R) :
    pCoreNormalizerAction 2 X ⟨r,h.normalizes ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1) r.property)⟩ ∈
      MulAut.innerSubgroup (X ⧸ pCore 2 X) := by
  have hr : (r : G) ∈ R := (show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1) r.property
  let a : (normalizer (X : Set G) ⊓ normalizer (R : Set G) : Subgroup G) :=
    ⟨r,h.normalizes hr,R.le_normalizer hr⟩
  let q := QuotientGroup.mk' (starKernel X R)
  let j : (X ⊔ R : Subgroup G) := ⟨r,mem_sup_right hr⟩
  have hj : q j ∈ starImage X R X := hi (mem_map_of_mem q r.property)
  apply (starComponentAction_inner_iff h a).mp
  refine ⟨⟨q j,hj⟩,?_⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := toStarImage_surjective X R x
  apply Subtype.ext
  rw [starComponentAction_apply,starComponentAut_toStarImage,MulAut.conj_apply]
  change q j * q ⟨y,mem_sup_left y.property⟩ * (q j)⁻¹ =
    q ⟨(r : G) * (y : G) * (r : G)⁻¹, _⟩
  rw [←map_inv,←map_mul,←map_mul]
  rfl

/-- Original C.2.3 control places the entire central preimage in the original
marked subgroup when the Thompson image is inner. -/
theorem core_center_preimage_le_marked_of_thompson_inner
    (h : Input KnownSimple.IsKnownSimple I R N X)
    (hi : starImage X R (elementaryAbelianMaxJ R) ≤ starImage X R X) :
    (centralPreimage (pCore 2 X)).map X.subtype ≤ N := by
  let D := X ⊔ R
  let : (X.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le X.le_normalizer h.normalizes)
  have hQ : X.pCoreIn 2 ≤ R :=
    (pCoreAmbient_mono_of_isSubnormalIn X D 2 le_sup_left
      (source_join_input h).component.2.subnormal).trans
      (source_joinCore_le_radical (source_join_input h))
  have hn := central_preimage_normalizes_thompson_of_inner h.normalizes hQ
    (thompson_core_action_inner_of_star_inner h hi)
  let RI := R.subgroupOf I
  have hJR : elementaryAbelianMaxJ RI = (elementaryAbelianMaxJ R).subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [←elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
      map_subgroupOf_eq_of_le h.setup.radical_le,
      map_subgroupOf_eq_of_le ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1).trans h.setup.radical_le)]
  have hctl := (normalizer_maxJ_le_characteristicNormalizerClosure RI RI
    (sSup_le fun _ hA => hA.1) le_rfl
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup RI h.setup.radical.isPGroup h.setup.radical.1)).trans
      h.setup.characteristic_control
  intro c hc
  have hcI : c ∈ I := h.component.1 (map_subtype_le _ hc)
  apply hctl (show (⟨c,hcI⟩ : I) ∈ normalizer (elementaryAbelianMaxJ RI : Set I) from ?_)
  rw [hJR,←subgroupOf_normalizer_eq ((show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1).trans h.setup.radical_le)]
  exact hn hc

end CFSG.Quasithin.ChapterC.C27Source
