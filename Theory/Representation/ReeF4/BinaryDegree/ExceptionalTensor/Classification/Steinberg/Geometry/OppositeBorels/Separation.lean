module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Candidates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Unipotence
public import Theory.AlgebraicGroup.Unipotent.Contraction.OppositeSeparation

/-!
# Opposite separation for the literal F4 candidates

The integral chamber functional supplies a cocharacter contracting the original
positive root groups under inverse conjugation. Composing that cocharacter with
regular parameter inversion contracts the negative root groups. For an element
of the negative candidate, its exact torus/root factorization therefore gives a
regular direct-conjugation orbit: the torus factor commutes with the cocharacter.
The two affine-line extensions force every coordinate of an element in the
positive-unipotent/opposite-candidate intersection to be constant, hence one.
The published candidate factorization then identifies the candidate intersection
with the fixed split torus.

This proves separation without Borel maximality or a representation flag, using
the corrected raw cocharacters and the original positive-root labels.
Sources: GLS3, Theorem 1.11.4 (`refs/KGroup/GLS3/Chapter1.tex`), and Steinberg
(6.2) (`refs/KGroup/GLS3/Chapter2St2.tex`).
-/

noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
open RootModel.Corrected
universe u
variable (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2]
local instance (S : ClosedSubgroup (F4Chevalley.Carrier (k := F))) :
    AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup

/-- The positive root-generated group meets the full opposite candidate only
in the identity, with no additional geometric hypotheses. -/
public theorem opposite_disjoint : Disjoint (positiveUnipotent F).toSubgroup (negativeCandidate F).toSubgroup := by
  let T := F4Chevalley.splitTorus (k := F)
  let D : RootGroupData (F4Chevalley.Carrier (k := F)) T := rootData (F := F)
  let phi := chamberFunctional (F := F)
  obtain ⟨lambda, hlambda⟩ := exists_cocharacter_realizing_characterFunctional
    T F4Chevalley.splitTorus_isSubtorus phi
  let mu := lambda.comp (parameterInversion (F := F))
  let rho := T.inclusion.comp lambda
  have hpos (r : Roots F) (hr : r ∈ positiveRoots F) :
      0 < phi (Additive.ofMul (D.rootWeight r)) :=
    chamberFunctional_root_positive r.down hr
  have hneg (r : Roots F) (hr : r ∈ negativeRoots F) :
      0 < -phi (Additive.ofMul (D.rootWeight r)) := by
    have h := hpos (D.neg r) hr
    have heq : D.rootWeight (D.neg r) = (D.rootWeight r)⁻¹ :=
      (rootData_isRealization_charTwo (F := F)).2.2.2.1 r
    rw [heq] at h
    change 0 < phi (-Additive.ofMul (D.rootWeight r)) at h
    simpa only [map_neg] using h
  have hmu (r : Roots F) :
      WeightCocharacterEquation T (D.rootWeight r) mu
        (-phi (Additive.ofMul (D.rootWeight r))) := by
    intro s
    change (D.rootWeight r).pointCharacter (lambda.onPoints s⁻¹) = _
    rw [hlambda, dPointEquiv_inv]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, inv_zpow, zpow_neg]
  rw [Subgroup.disjoint_def]
  intro g hg hb
  have hc : IsCocharacterContracted rho g :=
    rootSubgroupGenerated_isCocharacterContracted D rootData_isRealization_charTwo
      (positiveRoots F) lambda (fun r => phi (Additive.ofMul (D.rootWeight r)))
      hpos (fun r _ => hlambda (D.rootWeight r)) hg
  obtain ⟨t, v, ht, hv, rfl⟩ :=
    (mem_torusRootGenerated_iff F (negativeRoots F) g).mp hb
  have hcv : IsCocharacterContracted (T.inclusion.comp mu) v :=
    rootSubgroupGenerated_isCocharacterContracted D rootData_isRealization_charTwo
      (negativeRoots F) mu (fun r => -phi (Additive.ofMul (D.rootWeight r)))
      hneg (fun r _ => hmu r) hv
  obtain ⟨q, _, hq⟩ := hcv
  let oppositeCurve := (Theory.AlgebraicGroup.mulMorphism _).comp
    ((Variety.Morphism.const (KPlus F) _ t).pair q)
  apply hc.eq_one_of_opposite_curve oppositeCurve
  intro s
  change t * q.toFun (kPlusPoint (dPointEquiv 1 s 0 : F)) =
    rho.onPoints s * (t * v) * (rho.onPoints s)⁻¹
  have hqs := hq s
  change q.toFun (kPlusPoint (dPointEquiv 1 s 0 : F)) =
    (rho.onPoints s⁻¹)⁻¹ * v * rho.onPoints s⁻¹ at hqs
  rw [map_inv, inv_inv] at hqs
  rw [hqs]
  let tT := T.pointEquiv.symm ⟨t, ht⟩
  have htT : T.inclusion.onPoints tT = t :=
    congrArg Subtype.val (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
  have hcomm : rho.onPoints s * t = t * rho.onPoints s := by
    change T.inclusion.onPoints (lambda.onPoints s) * t =
      t * T.inclusion.onPoints (lambda.onPoints s)
    rw [← htT, ← map_mul, ← map_mul]
    rw [isMulCommutative_iff.mp F4Chevalley.splitTorus_isSubtorus.isMulCommutative]
  simp only [← mul_assoc, hcomm]


/-- The literal positive and opposite candidates intersect in their fixed
split torus. This discharges the intersection clause for big-cell assembly. -/
public theorem intersection_eq_torus :
    (positiveCandidate F).toSubgroup ⊓ (negativeCandidate F).toSubgroup =
      (F4Chevalley.splitTorus (k := F)).toSubgroup :=
  intersection_eq_torus_of_disjoint F (opposite_disjoint F)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
