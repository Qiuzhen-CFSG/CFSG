module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralParametersModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalParameters
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction


/-!
# One common field coefficient through both original triality parabolics

The original Sylow actor normalizes both source parabolics and S. Agreement
of the inverse maps on the whole Borel transports the established right
unipotent image to the left. The marked Hall torus supplies the left torus
invariance. The central signed-root calculation and the coroot compatibility
relation therefore identify its base-field map with the restriction of the
already proved order-two cubic coefficient.

The conclusion retains both original maps and both root signs. The separate
positive-action companion uses these formulas to discharge the full local
action premise in the centralizer bound. Ambient Sylow placement, S=T,
exhaustive comparison and final recognition remain source obligations.

Source: Aschbacher--Smith F.4.37--38, printed pp.293--294, and 5.3.3, p.659
(`refs/quasithin.pdf`); GLS3 §§2.4--2.6. The internal WeylAction import
reuses source normalization and torus-marking transports without widening
those implementation boundaries. Abstract inclusion-amalgam transport lemmas
keep the kernel from repeatedly expanding concrete subgroup maps.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.OuterOdd
open Triality.Standard.OuterOdd.Coverage Triality.Standard.OuterOdd.Coverage.ParameterRigidity
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.GroupTheory TrialityLocalParameters
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem transported_overlap_agree
    {M : Type*} [Group M] (Q R : Subgroup G) (C E B : Subgroup M)
    (hBC : B ≤ C) (hBE : B ≤ E)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups Q (Q ⊓ R) R inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups C B E hBC hBE))
    (t : G) (htQ : t∈normalizer (Q : Set G)) (htR : t∈normalizer (R : Set G))
    (x : B) :
    (MulAut.congr e.left (Q.normalizerMonoidHom ⟨t,htQ⟩) (inclusion hBC x)).val=
      (MulAut.congr e.right (R.normalizerMonoidHom ⟨t,htR⟩) (inclusion hBE x)).val := by
  let y := e.middle.symm x
  let z : (Q ⊓ R : Subgroup G) := ⟨t*y.val*t⁻¹,
    (mem_normalizer_iff.mp htQ y.val).mp y.property.1,
    (mem_normalizer_iff.mp htR y.val).mp y.property.2⟩
  have hl : Q.normalizerMonoidHom ⟨t,htQ⟩ (e.left.symm (inclusion hBC x))=
      inclusion inf_le_left z := by
    apply Subtype.ext
    change t*(e.left.symm (inclusion hBC x)).val*t⁻¹=t*y.val*t⁻¹
    exact congrArg (fun u : G => t*u*t⁻¹) (congrArg Subtype.val (e.symm.left_commutes x))
  have hr : R.normalizerMonoidHom ⟨t,htR⟩ (e.right.symm (inclusion hBE x))=
      inclusion inf_le_right z := by
    apply Subtype.ext
    change t*(e.right.symm (inclusion hBE x)).val*t⁻¹=t*y.val*t⁻¹
    exact congrArg (fun u : G => t*u*t⁻¹) (congrArg Subtype.val (e.symm.right_commutes x))
  change (e.left (Q.normalizerMonoidHom ⟨t,htQ⟩ _)).val=
    (e.right (R.normalizerMonoidHom ⟨t,htR⟩ _)).val
  exact (congrArg (fun v => (e.left v).val) hl).trans
    ((congrArg Subtype.val (e.left_commutes z)).trans
      ((congrArg Subtype.val (e.right_commutes z)).symm.trans
        (congrArg (fun v => (e.right v).val) hr).symm))

omit [Finite G] in
private theorem left_image_of_right
    {M : Type*} [Group M] (X Y : Subgroup G) (C E B U : Subgroup M)
    (hBC : B ≤ C) (hBE : B ≤ E) (hUB : U ≤ B)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X (X ⊓ Y) Y inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups C B E hBC hBE)) :
    (U.subgroupOf C).map (X.subtype.comp e.left.symm.toMonoidHom)=
      (U.subgroupOf E).map (Y.subtype.comp e.right.symm.toMonoidHom) := by
  have hagree (x : B) : (e.left.symm (inclusion hBC x)).val=
      (e.right.symm (inclusion hBE x)).val :=
    (congrArg Subtype.val (e.symm.left_commutes x)).trans
      (congrArg Subtype.val (e.symm.right_commutes x)).symm
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x.val,hBE (hUB hx)⟩,hx,(hagree ⟨x.val,hUB hx⟩).symm⟩
  · rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x.val,hBC (hUB hx)⟩,hx,hagree ⟨x.val,hUB hx⟩⟩

omit [Finite G] in
private theorem transported_subgroup_invariant
    {M : Type*} [Group M] [Finite M] (X S : Subgroup G) (C U : Subgroup M)
    (e : X ≃* C) (he : (U.subgroupOf C).map (X.subtype.comp e.symm.toMonoidHom)=S)
    (t : G) (htX : t∈normalizer (X : Set G)) (htS : t∈normalizer (S : Set G)) :
    (U.subgroupOf C).map (MulAut.congr e (X.normalizerMonoidHom ⟨t,htX⟩)).toMonoidHom=
      U.subgroupOf C := by
  apply torus_action_map X C U e S t htX htS
  intro x
  have hi : Function.Injective (X.subtype.comp e.symm.toMonoidHom) :=
    X.subtype_injective.comp e.symm.injective
  have hx : (X.subtype.comp e.symm.toMonoidHom) (e x)=x.val :=
    congrArg Subtype.val (e.symm_apply_apply x)
  rw [←hx,←he,mem_map_iff_mem hi]
  rfl

omit [Finite G] in
private theorem central_coefficient_of_right_action
    (m : ℕ) (hm : 0<m) (hm2 : 1<m) (X Y S D : Subgroup G)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X (X ⊓ Y) Y inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups
        (parabolic (binaryParameters m hm) .central) (borel (binaryParameters m hm))
        (parabolic (binaryParameters m hm) .arms)
        (borel_le_parabolic _ .central) (borel_le_parabolic _ .arms)))
    (hSR : ((unipotent (binaryParameters m hm)).subgroupOf
      (parabolic (binaryParameters m hm) .arms)).map
      (Y.subtype.comp e.right.symm.toMonoidHom)=S)
    (hml : ∀ x : X, x.val∈D ↔ (e.left x).val∈torus (binaryParameters m hm))
    (t : G) (htX : t∈normalizer (X : Set G)) (htY : t∈normalizer (Y : Set G))
    (htS : t∈normalizer (S : Set G)) (htD : t∈normalizer (D : Set G))
    (v : (ExtensionField (binaryParameters m hm))ˣ) (σ : CoefficientAut (binaryParameters m hm))
    (hs : ∀ s r, t*(e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms r)).val*t⁻¹=
        (e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms
          (signedScalar s v.val*σ r))).val) :
    ∃ c : (fixedField (binaryParameters m hm))ˣ,
      ∀ s r, t*(e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central r)).val*t⁻¹=
        (e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central
          (signedScalar s c.val*coefficientFixedField (binaryParameters m hm) σ r))).val := by
  let P := binaryParameters m hm
  let fL : parabolic P .central →* G := X.subtype.comp e.left.symm.toMonoidHom
  let fR : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hfR : Function.Injective fR := Y.subtype_injective.comp e.right.symm.injective
  let a : MulAut (parabolic P .central) := MulAut.congr e.left (X.normalizerMonoidHom ⟨t,htX⟩)
  let b : MulAut (parabolic P .arms) := MulAut.congr e.right (Y.normalizerMonoidHom ⟨t,htY⟩)
  have ha (x : parabolic P .central) : fL (a x)=t*fL x*t⁻¹ := by
    change (e.left.symm (e.left (X.normalizerMonoidHom ⟨t,htX⟩ (e.left.symm x)))).val=_
    rw [e.left.symm_apply_apply]
    rfl
  have hb (x : parabolic P .arms) : fR (b x)=t*fR x*t⁻¹ := by
    change (e.right.symm (e.right (Y.normalizerMonoidHom ⟨t,htY⟩ (e.right.symm x)))).val=_
    rw [e.right.symm_apply_apply]
    rfl
  have hSL : ((unipotent P).subgroupOf (parabolic P .central)).map fL=S :=
    (left_image_of_right X Y (parabolic P .central) (parabolic P .arms) (borel P) (unipotent P)
      (borel_le_parabolic P .central) (borel_le_parabolic P .arms) (unipotent_le_borel P) e).trans hSR
  have haU := transported_subgroup_invariant X S (parabolic P .central) (unipotent P)
    e.left hSL t htX htS
  have haD := torus_action_map (M := Carrier P) X (parabolic P .central)
    (torus P) e.left D t htX htD hml
  obtain ⟨c,τ,hc⟩ := TrialityCentralAction.central_signed_field_action m hm
    hm2 a haD haU
  have hs' (s r) : b (rootInParabolic P rfl s .arms r)=
      rootInParabolic P rfl s .arms (signedScalar s v.val*σ r) := by
    apply hfR
    exact (hb _).trans (hs s r)
  have hB (x : borel P) : (a (inclusion (borel_le_parabolic P .central) x)).val=
      (b (inclusion (borel_le_parabolic P .arms) x)).val :=
    transported_overlap_agree X Y (parabolic P .central) (parabolic P .arms) (borel P)
      (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e t htX htY x
  have he := TrialityCentralAction.fields_compatible_of_local_actions P rfl a b hB c τ v σ hc hs'
  refine ⟨c,?_⟩
  intro s r
  rw [he]
  exact (ha _).symm.trans (congrArg fL (hc s r))


/-- Both signed simple-root pairs have the same cubic field coefficient
through the original compatible maps; its order is two for an outer involution. -/
theorem Preparation.triality_outer_common_signed_root_action
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉sourceS L H)
    (htD : t.val∈normalizer (D : Set G)) :
    ∃ (c : (fixedField (binaryParameters m hm))ˣ)
      (v : (ExtensionField (binaryParameters m hm))ˣ)
      (σ : CoefficientAut (binaryParameters m hm)),
      orderOf σ=2 ∧ v.val*σ v.val=1 ∧
      (∀ s r, t.val*(e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central r)).val*t.val⁻¹=
        (e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central
          (signedScalar s c.val*coefficientFixedField (binaryParameters m hm) σ r))).val) ∧
      (∀ s r, t.val*(e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms r)).val*t.val⁻¹=
        (e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms
          (signedScalar s v.val*σ r))).val) := by
  obtain ⟨v,σ,hσ,hv,hs⟩ := d.triality_outer_signed_root_action h hTH hp m hm e hD hmark t ht2 htS htD
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  obtain ⟨c,hc⟩ := central_coefficient_of_right_action m hm
    (d.triality_local_structure h hTH hp m hm e).2.1
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1) (sourceS L H) D e
    (d.triality_right_unipotent_image h hTH (binaryParameters m hm) rfl e)
    (source_triality_torus_markings m hm e (hD.trans hC) hmark).1 t.val
    (source_parabolics_normalized h.sylow_normalizes hTH 0 t.property)
    (source_parabolics_normalized h.sylow_normalizes hTH 1 t.property)
    (sylow_normalizes_sourceS h.sylow_normalizes hTH t.property) htD v σ hs
  exact ⟨c,v,σ,hσ,hv,hc,hs⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
