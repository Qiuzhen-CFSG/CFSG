module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientOmegaAction

/-!
# The literal quotient omega-center on the original binary center

The ambient omega preimage maps onto the full omega-center of the specified
quotient Sylow. Identity coordinates on Z_lambda turn the proved group
triple-commutator identity into quadraticity of its actual representation.
No replacement of Z_lambda by an isomorphic unmarked vector space occurs.

Source: DGS, *Groups and Graphs* (1985), 8.1(h), pp.132–134. The reduced
application is in `ReducedOmegaAction`; later 5.12 applications also retain
its independently proved Sylow-fixed generation and residual fixed-space
premises from `ModulePreparation`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- The entire lifted quotient omega-center maps onto the original quotient
omega-center. This is equality through the specified map, not an order comparison. -/
theorem quotientSylowOmegaPreimage_image (L : Subgroup G) (S : Sylow 2 L) :
    ((quotientSylowOmegaPreimage L S).subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) =
      omegaCenterIn ((S : Subgroup L).map (QuotientGroup.mk' (pCore 2 L))) := by
  unfold quotientSylowOmegaPreimage
  rw [subgroupOf, comap_map_eq_self_of_injective L.subtype_injective,
    map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _)]

/-- Literal source representation of 8.1(h): the whole quotient omega-center
acts quadratically on the unchanged original neighboring center. -/
theorem source_critical_quotient_omega_module
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let L := d.localGroup w.val
    let q := QuotientGroup.mk' (pCore 2 L)
    ∃ ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (Z F w.val)),
      (∀ (l : L) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      IsQuadratic ρ (omegaCenterIn ((R : Subgroup L).map q)) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  let F := family P
  let L := d.localGroup w.val
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨ρ, hact⟩ := source_exists_center_quotient_action h d w.val (MulEquiv.refl _)
  obtain ⟨_, hquad⟩ := source_critical_quotient_omega_action h hB d hc hab hd hb hcomm models w hm R hR
  have hZL : Z F w.val ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  let c := centerSection L (Z F w.val) hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) q ρ hact
  refine ⟨ρ, hact, ?_⟩
  have hq := BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    L (Z F w.val) ⊥ (quotientSylowOmegaPreimage L R) ρ q c (by
      rw [commutator_comm (quotientSylowOmegaPreimage L R),
        commutator_comm (quotientSylowOmegaPreimage L R)]
      exact hquad.le)
  rwa [quotientSylowOmegaPreimage_image] at hq

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
