module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralParameters
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityPositiveActionModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterFixed
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralParameters
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction


/-!
# The original triality outer involution on the entire positive subgroup

Both original parabolic maps give the same field coefficient on their signed
simple roots. The compatible six-root generation calculation supplies the
action on all positive elements. The genuine torus realizes the root scalars,
so this is precisely torus conjugation followed by the cubic coefficient
of order two, through the original right-parabolic map.

This discharges the local-action hypothesis in the fixed-point estimate:
|C_S(t)| ≤ q^6 and |C_T(t)| < q^7, retaining the original marked torus and
the exact Sylow extension index. The Chapter 12 companion applies both the
identity and the bound to the literal chosen-module setup, including q=4.

The estimate does not yet assert that C_T(t) is Sylow in C_G(t). The genuine
weak-closure/center argument of F.4.37, S=T, full-extension recognition and
exhaustive comparison remain with the generic-global assembly.

Source: Aschbacher--Smith F.4.37--38, printed pp.293--294, and 5.3.3, p.659
(`refs/quasithin.pdf`); GLS3 §§2.4--2.6. Internal imports reuse the original
source-normalization and overlap transports within this proof family.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.OuterOdd
open Triality.Standard.OuterOdd.Coverage Triality.Standard.OuterOdd.Coverage.ParameterRigidity
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.GroupTheory TrialityLocalParameters
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem transported_positive_action
    (m : ℕ) (hm : 0<m) (X Y : Subgroup G)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups X (X ⊓ Y) Y inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups
        (parabolic (binaryParameters m hm) .central) (borel (binaryParameters m hm))
        (parabolic (binaryParameters m hm) .arms)
        (borel_le_parabolic _ .central) (borel_le_parabolic _ .arms)))
    (t : G) (htX : t∈normalizer (X : Set G)) (htY : t∈normalizer (Y : Set G))
    (c : (fixedField (binaryParameters m hm))ˣ)
    (v : (ExtensionField (binaryParameters m hm))ˣ) (σ : CoefficientAut (binaryParameters m hm))
    (hL : ∀ s r, t*(e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central r)).val*t⁻¹=
        (e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central
          (signedScalar s c.val*coefficientFixedField (binaryParameters m hm) σ r))).val)
    (hR : ∀ s r, t*(e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms r)).val*t⁻¹=
        (e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms
          (signedScalar s v.val*σ r))).val) :
    ∃ g : torus (binaryParameters m hm),
      let gP : parabolic (binaryParameters m hm) .arms := inclusion
        ((torus_le_borel _).trans (borel_le_parabolic _ .arms)) g
      ∀ x : parabolic (binaryParameters m hm) .arms,
        x.val∈unipotent (binaryParameters m hm) →
          t*(e.right.symm x).val*t⁻¹=
            (e.right.symm (gP*coefficientParabolic (binaryParameters m hm) σ .arms x*gP⁻¹)).val := by
  let P := binaryParameters m hm
  let fL : parabolic P .central →* G := X.subtype.comp e.left.symm.toMonoidHom
  let fR : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hfL : Function.Injective fL := X.subtype_injective.comp e.left.symm.injective
  have hfR : Function.Injective fR := Y.subtype_injective.comp e.right.symm.injective
  let a : (i : Node) → MulAut (parabolic P i)
    | .arms => MulAut.congr e.right (Y.normalizerMonoidHom ⟨t,htY⟩)
    | .central => MulAut.congr e.left (X.normalizerMonoidHom ⟨t,htX⟩)
  have ha (x : parabolic P .central) : fL (a .central x)=t*fL x*t⁻¹ := by
    change (e.left.symm (e.left (X.normalizerMonoidHom ⟨t,htX⟩ (e.left.symm x)))).val=_
    rw [e.left.symm_apply_apply]
    rfl
  have hb (x : parabolic P .arms) : fR (a .arms x)=t*fR x*t⁻¹ := by
    change (e.right.symm (e.right (Y.normalizerMonoidHom ⟨t,htY⟩ (e.right.symm x)))).val=_
    rw [e.right.symm_apply_apply]
    rfl
  let u : (i : Node) → (RootField P i)ˣ
    | .arms => v
    | .central => c
  have hB (x : borel P) : (a .central (inclusion (borel_le_parabolic P .central) x)).val=
      (a .arms (inclusion (borel_le_parabolic P .arms) x)).val :=
    transported_overlap_agree X Y (parabolic P .central) (parabolic P .arms) (borel P)
      (borel_le_parabolic P .central) (borel_le_parabolic P .arms) e t htX htY x
  have hr (s i r) : a i (rootInParabolic P rfl s i r)=
      rootInParabolic P rfl s i (signedScalar s (u i).val*coefficientRootField P σ i r) := by
    cases i
    · apply hfR
      exact (hb _).trans (hR s r)
    · apply hfL
      exact (ha _).trans (hL s r)
  obtain ⟨g,hg⟩ := TrialityCentralAction.torus_coefficient_positive_action m hm a hB u σ hr
  refine ⟨g,?_⟩
  dsimp only
  intro x hx
  exact (hb x).symm.trans (congrArg fR (hg x hx))

/-- The original compatible parabolic maps determine the actual torus--field
action on the whole positive subgroup, with an order-two coefficient. -/
theorem Preparation.triality_outer_torus_coefficient_action
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
    ∃ (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm)),
      orderOf σ=2 ∧
      let gP : parabolic (binaryParameters m hm) .arms := inclusion
        ((torus_le_borel _).trans (borel_le_parabolic _ .arms)) g
      ∀ x : parabolic (binaryParameters m hm) .arms,
        x.val∈unipotent (binaryParameters m hm) →
          t.val*(e.right.symm x).val*t.val⁻¹=
            (e.right.symm (gP*coefficientParabolic (binaryParameters m hm) σ .arms x*gP⁻¹)).val := by
  obtain ⟨c,v,σ,hσ,_,hL,hR⟩ := d.triality_outer_common_signed_root_action h hTH hp m hm e hD hmark t ht2 htS htD
  obtain ⟨g,hg⟩ := transported_positive_action m hm
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0)
    (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1) e t.val
    (source_parabolics_normalized h.sylow_normalizes hTH 0 t.property)
    (source_parabolics_normalized h.sylow_normalizes hTH 1 t.property) c v σ hL hR
  exact ⟨g,σ,hσ,hg⟩

/-- The original outer involution has at most q^6 fixed elements in S and
fewer than q^7 in T. The local-action premise is now discharged. -/
theorem Preparation.triality_outer_involution_centralizer_lt
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
    Nat.card (sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ (binaryParameters m hm).q^6 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < (binaryParameters m hm).q^7 := by
  obtain ⟨g,σ,hσ,ha⟩ := d.triality_outer_torus_coefficient_action h hTH hp m hm e hD hmark t ht2 htS htD
  exact d.triality_outer_centralizer_lt_of_torus_coefficient_action h hTH hp m hm e hD hmark t htD g σ hσ ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
