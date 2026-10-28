module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.FirstChoice.Frattini
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Cores
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalBranches.QuotientTheta.Generation
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction

/-!
# The first-choice quotient by O₂,Φ

The given natural action maps YS onto the plane-preserving base, identified
with S₃ × S₃. The cubic Y-image and the two-group S-image intersect trivially,
so an element of the action kernel factors into elements centralizing V in Y
and in S. The latter belongs to O₂(YS)=C_T(V). In the ordinary alternative
the former belongs to O₂(Y); in the extraspecial alternative its image in
Y/O₂(Y) belongs to the center and hence to the Frattini subgroup. Normality
of Y in YS transfers this Frattini containment to YS/O₂(YS).

Conversely Φ(S₃ × S₃)=1 puts the entire Frattini preimage into the action
kernel. Thus the two subgroups are equal, giving the literal quotient by
O₂,Φ(YS), including the central factor in the extraspecial case.

Only the authorized earlier 15.3.7 alternatives, image equality and core
equality remain inputs. The calculation does not require any extra outputs
from 15.3.2–9 or the outside-overgroup Sylow witness.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.7 and 15.3.11(5i), printed pp.1122–1124.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta
open FusionCore.CosetSetup.ExtraspecialLocal
open DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem ys_le_m (d : CharacteristicTwo.LocalData G) : d.Y ⊔ d.S ≤ d.M :=
  sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
    (inf_le_left.trans d.sylow_le)

private theorem y_normal_in_ys (d : CharacteristicTwo.LocalData G) :
    (d.Y.subgroupOf (d.Y ⊔ d.S)).Normal :=
  normal_subgroupOf_of_le_normalizer ((ys_le_m d).trans (m_normalizes_y d))

private theorem residual_eq_cubic :
    twoResidualAmbient (⊤ : Subgroup OrthogonalActor) = cubicBase := by
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · apply (Subgroup.closure_le _).mpr
    exact fun a ha => RankTwo.orthogonal_cubic_mem_twoResidual a ha
  · rw [baseModelFacts.card_cubic, RankTwo.orthogonal_twoResidual_card]

private theorem ys_actor_range (d : CharacteristicTwo.LocalData G)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    (restrictedActor d.action (ys_le_m d)).range = planeBase := by
  apply image_YS_eq baseModelFacts d.T d.action d.sylow_le (ys_le_m d) inf_le_left
  · rw [restrictedActor, RankTwo.natural_restricted_actor_range, h7image, residual_eq_cubic]
  · intro t
    change ((t : G) ∈ (d.T : Subgroup G) ∧
      (t : G) ∈ normalizer (d.action.plane 1 : Set G)) ↔ _
    rw [and_iff_right (show (t : G) ∈ (d.T : Subgroup G) from t.property)]
    change (inclusion d.sylow_le t) ∈
      (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M ↔ _
    rw [d.action.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker]
    rfl

private theorem core_le_actor_ker (d : CharacteristicTwo.LocalData G)
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    pCore 2 ↥(d.Y ⊔ d.S) ≤ (restrictedActor d.action (ys_le_m d)).ker := by
  rw [restrictedActor, RankTwo.natural_restricted_actor_ker]
  intro x hx
  exact ((ys_core_eq_centralizer d hcore).le (mem_map_of_mem (d.Y ⊔ d.S).subtype hx)).2

private theorem y_core_le_ys_core (d : CharacteristicTwo.LocalData G) :
    pCore 2 d.Y ≤ (pCore 2 ↥(d.Y ⊔ d.S)).comap (inclusion le_sup_left) := by
  have h := pCoreIn_mono_of_normalizes (show d.Y ≤ d.Y ⊔ d.S from le_sup_left)
    ((ys_le_m d).trans (m_normalizes_y d)) (p := 2)
  intro y hy
  obtain ⟨z, hz, he⟩ := h (mem_map_of_mem d.Y.subtype hy)
  have he' : z = inclusion (show d.Y ≤ d.Y ⊔ d.S from le_sup_left) y := Subtype.ext he
  change inclusion le_sup_left y ∈ pCore 2 ↥(d.Y ⊔ d.S)
  exact he' ▸ hz

private theorem y_centralizer_mem_coreFrattini (d : CharacteristicTwo.LocalData G)
    (h7 : EarlierThreeAlternatives d) (y : d.Y)
    (hy : (y : G) ∈ centralizer (d.V : Set G)) :
    inclusion (show d.Y ≤ d.Y ⊔ d.S from le_sup_left) y ∈
      coreFrattiniSubgroup ↥(d.Y ⊔ d.S) := by
  let H := d.Y ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : d.Y →* H ⧸ pCore 2 H := q.comp (inclusion le_sup_left)
  have hk : pCore 2 d.Y ≤ f.ker := by
    intro z hz
    exact (QuotientGroup.eq_one_iff _).mpr (y_core_le_ys_core d hz)
  have hnormal : f.range.Normal := by
    rw [MonoidHom.range_comp, inclusion_range]
    let := y_normal_in_ys d
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  rcases h7 with ho | ⟨he, _, _⟩
  · have hycore : y ∈ pCore 2 d.Y := by
      obtain ⟨z, hz, hzy⟩ := ho.centralizer_eq.le ⟨y.property, hy⟩
      exact (Subtype.ext hzy : z = y) ▸ hz
    change q (inclusion le_sup_left y) ∈ frattini (H ⧸ pCore 2 H)
    rw [show q (inclusion le_sup_left y) = 1 from hk hycore]
    exact one_mem _
  · have hycenter : QuotientGroup.mk' (pCore 2 d.Y) y ∈ center (d.Y ⧸ pCore 2 d.Y) := by
      obtain ⟨z, hz, hzy⟩ := he.centralizer_eq.le ⟨y.property, hy⟩
      exact (Subtype.ext hzy : z = y) ▸ hz
    have hyphi := extraspecial27_center_le_frattini he.extraspecial he.quotient_card hycenter
    exact frattini_quotient_lift_map_le (pCore 2 d.Y) f hk
      (mem_map_of_mem (QuotientGroup.lift (pCore 2 d.Y) f hk) hyphi)

private theorem actor_ker_le_coreFrattini (d : CharacteristicTwo.LocalData G)
    (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    (restrictedActor d.action (ys_le_m d)).ker ≤ coreFrattiniSubgroup ↥(d.Y ⊔ d.S) := by
  let H := d.Y ⊔ d.S
  let f := restrictedActor d.action (ys_le_m d)
  let := y_normal_in_ys d
  have hgen : d.Y.subgroupOf H ⊔ d.S.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have htwo : IsPGroup 2 (d.S.subgroupOf H) :=
    (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).comap_subtype
  have hdis : Disjoint cubicBase ((d.S.subgroupOf H).map f) :=
    (IsPGroup.of_card (p := 3) (n := 2) baseModelFacts.card_cubic).disjoint_of_coprime
      (htwo.map f) (by decide)
  intro x hx
  obtain ⟨y, hy, s, hs, hys⟩ := mem_sup_of_normal_left.mp
    (show x ∈ d.Y.subgroupOf H ⊔ d.S.subgroupOf H from hgen ▸ mem_top _)
  have hyc : f y ∈ cubicBase := by
    rw [← residual_eq_cubic, ← h7image]
    exact ⟨⟨y, ys_le_m d y.property⟩, hy, rfl⟩
  have hprod : f y * f s = 1 := by
    rw [← map_mul, hys]
    exact hx
  have hfy : f y = 1 := by
    apply disjoint_def.mp hdis hyc
    rw [mul_eq_one_iff_eq_inv.mp hprod]
    exact ((d.S.subgroupOf H).map f).inv_mem (mem_map_of_mem f hs)
  have hfs : f s = 1 := by simpa only [hfy, one_mul] using hprod
  have hk := RankTwo.natural_restricted_actor_ker d.action (ys_le_m d)
  have hycent : (y : G) ∈ centralizer (d.V : Set G) := by
    change y ∈ (centralizer (d.V : Set G)).subgroupOf (d.Y ⊔ d.S)
    exact hk ▸ (show y ∈ f.ker from hfy)
  have hscent : (s : G) ∈ centralizer (d.V : Set G) := by
    change s ∈ (centralizer (d.V : Set G)).subgroupOf (d.Y ⊔ d.S)
    exact hk ▸ (show s ∈ f.ker from hfs)
  have hyphi : y ∈ coreFrattiniSubgroup H :=
    y_centralizer_mem_coreFrattini d h7 ⟨y, hy⟩ hycent
  have hscore : s ∈ pCore 2 H := by
    have hm : (s : G) ∈ H.pCoreIn 2 :=
      (ys_core_eq_centralizer d hcore).ge ⟨(show (s : G) ∈ d.S from hs).1, hscent⟩
    obtain ⟨z, hz, he⟩ := hm
    exact (Subtype.ext he : z = s) ▸ hz
  have hsphi : s ∈ coreFrattiniSubgroup H := by
    change QuotientGroup.mk' (pCore 2 H) s ∈ frattini (H ⧸ pCore 2 H)
    have hsone : QuotientGroup.mk' (pCore 2 H) s = 1 :=
      (QuotientGroup.eq_one_iff s).mpr hscore
    rw [hsone]
    exact one_mem _
  rw [← hys]
  exact mul_mem hyphi hsphi

private theorem coreFrattini_le_actor_ker (d : CharacteristicTwo.LocalData G)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    coreFrattiniSubgroup ↥(d.Y ⊔ d.S) ≤ (restrictedActor d.action (ys_le_m d)).ker := by
  let H := d.Y ⊔ d.S
  let f := restrictedActor d.action (ys_le_m d)
  let e : f.range ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    (MulEquiv.subgroupCongr (ys_actor_range d h7image)).trans planeBaseEquiv
  let r : H →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
    e.toMonoidHom.comp f.rangeRestrict
  have hr : Function.Surjective r := e.surjective.comp f.rangeRestrict_surjective
  have hk : pCore 2 H ≤ r.ker := by
    intro x hx
    have hf : f.rangeRestrict x = 1 := Subtype.ext (core_le_actor_ker d hcore hx)
    change e (f.rangeRestrict x) = 1
    rw [hf, map_one]
  let l := QuotientGroup.lift (pCore 2 H) r hk
  have hl : Function.Surjective l := QuotientGroup.lift_surjective_of_surjective _ r hr hk
  intro x hx
  have hm := frattini_le_comap_frattini_of_surjective hl hx
  have hx' : r x = 1 := by
    change l (QuotientGroup.mk' (pCore 2 H) x) ∈
      frattini (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) at hm
    rw [symmetricThreeSquare_frattini] at hm
    exact mem_bot.mp hm
  have hf : f.rangeRestrict x = 1 := e.injective (hx'.trans e.map_one.symm)
  exact congrArg f.range.subtype hf

/-- The action kernel is exactly the literal Frattini preimage, in both earlier alternatives. -/
theorem first_choice_actor_kernel (d : CharacteristicTwo.LocalData G)
    (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    (centralizer (d.V : Set G)).subgroupOf (d.Y ⊔ d.S) =
      coreFrattiniSubgroup ↥(d.Y ⊔ d.S) := by
  rw [← RankTwo.natural_restricted_actor_ker d.action (ys_le_m d)]
  exact le_antisymm (actor_ker_le_coreFrattini d h7 h7image hcore)
    (coreFrattini_le_actor_ker d h7image hcore)

/-- The actual first-choice quotient of 15.3.11(5i). No outside-overgroup
hypotheses are needed for this calculation once 15.3.7 is supplied. -/
theorem first_choice_frattini_quotient (d : CharacteristicTwo.LocalData G)
    (hfirst : d.Yplus = d.Y) (h7 : EarlierThreeAlternatives d)
    (h7image : d.action.image d.Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (d.Y ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      (d.T : Subgroup G) ⊓ centralizer (d.V : Set G)) :
    Nonempty ((↥(d.Yplus ⊔ d.S) ⧸ coreFrattiniSubgroup ↥(d.Yplus ⊔ d.S)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rw [hfirst]
  let f := restrictedActor d.action (ys_le_m d)
  have hk : f.ker = coreFrattiniSubgroup ↥(d.Y ⊔ d.S) :=
    (RankTwo.natural_restricted_actor_ker d.action (ys_le_m d)).trans
      (first_choice_actor_kernel d h7 h7image hcore)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr (ys_actor_range d h7image)).trans planeBaseEquiv))⟩

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches.QuotientTheta

end
