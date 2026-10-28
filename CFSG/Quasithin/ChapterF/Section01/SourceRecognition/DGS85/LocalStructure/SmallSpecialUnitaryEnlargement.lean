module
public import Theory.SpecificGroups.SU3.SmallSpecialInnerness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallUnitaryThreeCore

/-!
# Unconditional SU3(2) enlargement on the original F.1.1 data

The actual Borel-core action preserves a common quotient Sylow and fixes
the cubic scalar center. The extraspecial three-core argument makes each
two-power actor inner, hence gives its concrete identity-field semilinear
formula. This discharges the previously explicit coverage premise and
identifies the enlarged endpoint with the original starred endpoint.

The original quotient marking now gives the enlarged marking, both 6.5
obstructions on the original cores, and the actual 6.6 application. No
nonsolvability or automorphism-coverage hypothesis has been added.
The separate PSU3(2) enlargement and the full source assembly remain open.
Source: Aschbacher--Smith F.1.1 and F.1.9, pp.259--262; DGS, Groups and
Graphs (1985), reduction p.95, 6.1 and 6.5--6.6, pp.118--123.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G:Type*} [Group G] {P B:Subgroup G}

/-- Innerness at the literal local Borel-core action, with no semilinear coverage premise. -/
theorem small_special_borel_core_inner (d:LocalRankOneData P B)
    (hB:∃ T:Sylow 2 B,(T:Subgroup B)=pCore 2 B)
    {F:Type*} [Field F] [Finite F] (J:HermitianForm 3 F)
    (hc:Nat.card F=2^2) (hconj:∀ x,J.conj x=x^2)
    (e:(d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup)
    (r:B.pCoreIn 2) : ∃ t:J.specialSubgroup, MulAut.conj t=markedBorelCoreAction d e r := by
  obtain ⟨T,hT⟩ := markedBorelCoreAction_normalizer_displacements d hB e
  obtain ⟨k,hk⟩ := isPGroup_pCoreIn 2 B r
  have hp : markedBorelCoreAction d e r ^ (2^k)=1 := by rw [←map_pow,hk,map_one]
  obtain ⟨t,ht⟩ := HermitianForm.SmallThreeCore.special_inner_of_two_power_center_fixed
    J hc hconj T (markedBorelCoreAction d e r) hp (hT r).1
    (small_special_borel_core_fixes_center d hB J hc hconj e r)
  exact ⟨t,ht⟩

private theorem special_semilinear_of_inner {F:Type*} [Field F] (J:HermitianForm 3 F)
    (a:MulAut J.specialSubgroup) (ht:∃ t:J.specialSubgroup,MulAut.conj t=a) :
    J.HasSpecialUnitarySemilinearForm a 1 := by
  obtain ⟨t,rfl⟩ := ht
  refine ⟨⟨t.val,t.property.1⟩,fun x => ?_⟩
  change t.val*x.val*t.val⁻¹=t.val*Matrix.GeneralLinearGroup.map (RingHom.id F) x.val*t.val⁻¹
  simp

/-- The actual small special-unitary enlargement equals its starred subgroup without an extra actor hypothesis. -/
theorem localEnlargement_eq_star_of_small_special (d:LocalRankOneData P B)
    (hB:∃ T:Sylow 2 B,(T:Subgroup B)=pCore 2 B)
    {F:Type*} [Field F] [Finite F] (J:HermitianForm 3 F)
    (hc:Nat.card F=2^2) (hconj:∀ x,J.conj x=x^2)
    (e:(d.Pstar ⧸ pCore 2 d.Pstar) ≃* J.specialSubgroup) :
    localEnlargement d=d.Pstar :=
  localEnlargement_eq_star_of_small_special_semilinear d hB J hc hconj e
    (fun r => ⟨1,special_semilinear_of_inner J _ (small_special_borel_core_inner d hB J hc hconj e r)⟩)

namespace Reduction
variable {L:Fin 2 → Subgroup G} {S:Subgroup G}

/-- The original full-Borel-core actor is inner in the original small special-unitary quotient. -/
theorem original_small_special_borel_core_inner (h:HypothesisF11 L S) (i:Fin 2)
    {F:Type*} [Field F] [Finite F] (J:HermitianForm 3 F)
    (hc:Nat.card F=2^2) (hconj:∀ x,J.conj x=x^2)
    (e:(L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (r:(commonBorel L S).pCoreIn 2) :
    ∃ t:J.specialSubgroup,MulAut.conj t=originalMarkedBorelCoreAction h i e r := by
  obtain ⟨T,hT⟩ := original_marked_borel_core_preserves_sylow h i e
  obtain ⟨k,hk⟩ := isPGroup_pCoreIn 2 (commonBorel L S) r
  have hp : originalMarkedBorelCoreAction h i e r ^ (2^k)=1 := by rw [←map_pow,hk,map_one]
  obtain ⟨t,ht⟩ := HermitianForm.SmallThreeCore.special_inner_of_two_power_center_fixed
    J hc hconj T (originalMarkedBorelCoreAction h i e r) hp (hT r)
    (original_small_special_borel_core_fixes_center h i J hc hconj e r)
  exact ⟨t,ht⟩

/-- The semilinear coverage premise is discharged at the literal original action, with identity field parameter. -/
theorem original_small_special_semilinear (h:HypothesisF11 L S) (i:Fin 2)
    {F:Type*} [Field F] [Finite F] (J:HermitianForm 3 F)
    (hc:Nat.card F=2^2) (hconj:∀ x,J.conj x=x^2)
    (e:(L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (r:(commonBorel L S).pCoreIn 2) :
    J.HasSpecialUnitarySemilinearForm (originalMarkedBorelCoreAction h i e r) 1 :=
  special_semilinear_of_inner J _ (original_small_special_borel_core_inner h i J hc hconj e r)

/-- The original small special-unitary endpoint has no strict enlargement. -/
theorem original_small_special_enlargement (h:HypothesisF11 L S) (i:Fin 2)
    {F:Type*} [Field F] [Finite F] (J:HermitianForm 3 F)
    (hc:Nat.card F=2^2) (hconj:∀ x,J.conj x=x^2)
    (e:(L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    enlargedEndpoint L S i=starredParabolic L S i :=
  original_small_special_enlargement_of_semilinear h i J hc hconj e
    (fun r => ⟨1,original_small_special_semilinear h i J hc hconj e r⟩)

/-- The original marking now supplies the actual enlarged small special-unitary marking. -/
theorem original_small_special_enlarged_marking (h:HypothesisF11 L S) (i:Fin 2)
    (hm:IsSU (L i ⧸ pCore 2 (L i)) 3 2) :
    IsSU (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) 3 2 := by
  obtain ⟨F,hF,hfin,J,hc,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  exact original_small_special_enlarged_marking_of_semilinear h i J hc hconj e
    (fun r => ⟨1,original_small_special_semilinear h i J hc hconj e r⟩)

/-- Both original-core 6.5 obstructions for the degree-one special-unitary row. -/
theorem original_small_special_obstruction (h:HypothesisF11 L S) (i:Fin 2)
    (hm:IsSU (L (other i) ⧸ pCore 2 (L (other i))) 3 2) :
    (¬ enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    (¬ parabolic L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G)) ∧
    ¬ ∃ T : Sylow 2 (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))),
      (T : Subgroup (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)))).map
        (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))).subtype =
          (parabolic L S i).pCoreIn 2 :=
  original_small_unitary_enlargement_obstruction h i
    (Or.inr (original_small_special_enlarged_marking h (other i) hm))

open Subgroup.CosetGeometry.RankTwo in
/-- Source 6.6 at the original small special-unitary row, with the scalar and actor premises discharged. -/
theorem reduced_small_special_center_product (h:HypothesisF11 L S) (j:Bool)
    (hm:IsSU (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) 3 2)
    (hn : stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ normalizer
      (↑(Z (reducedFamily L S) (base (reducedFamily L S) j) ⊔
        Z (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S))) :
    (∀ T : Sylow 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) j)),
      Z (reducedFamily L S) (base (reducedFamily L S) j) = omegaCenterIn
        ((T : Subgroup (stabilizer (reducedFamily L S) (base (reducedFamily L S) j))).map
          (stabilizer (reducedFamily L S) (base (reducedFamily L S) j)).subtype)) ∧
      Z (reducedFamily L S) (base (reducedFamily L S) j) ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!j)) :=
  reduced_small_unitary_enlargement_center_product h j
    (Or.inr (original_small_special_enlarged_marking h (other (if j then 1 else 0)) hm)) hn
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
