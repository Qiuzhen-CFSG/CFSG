module
public import Stellmacher.SectionNine.DistanceOneChiefThreeChoice
public import Stellmacher.SectionNine.DistanceOneChiefThreeLift
public import Stellmacher.SectionNine.DistanceOneChiefThreeContradiction

/-!
# Excluding the noncentral distance-one chief branch

The canonical noncentral chief branch is impossible. The actual two-module
comparison selects an order-three subgroup in the chief action range whose
fixed plane is moved by U, while its full preimage is fixed-point-free on Z_a.
The odd subgroup lifting theorem realizes this image by D in the original
initial stabilizer.

The lift satisfies Q_aD equal to the full preimage. Since Z_a centralizes
Q_a, fixed-freeness transfers from the full preimage to D. Mapping the chosen
normalizer and moving fixed-point witnesses from the faithful action range
into its automorphism group gives exactly the three-actor contradiction's
hypotheses. That contradiction uses the proved terminal extraspecial bound.

This completes the noncentral-chief-factor argument in Stellmacher (9.1),
Journal of Algebra190 (1997), pp.47–48. The subsequent center-free core
collapse supplies relation (11).
-/
namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_chief_branch_false
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) : False := by
  let P := stabilizer ctx.Γ ctx.criticalPath.a
  let Q := q ctx.Γ ctx.criticalPath.a
  let Z := z ctx.Γ ctx.criticalPath.a
  let W := DistanceOneChiefQuotient ctx.toLocalContext
  let action : P →* MulAut W := distanceOneChiefAction ctx.toLocalContext
  let X := action.range
  let projection := action.rangeRestrict
  let J := (branch.U.subgroupOf P).map projection
  obtain ⟨Dbar,hDbar,hnorm,hfixedcard,hfreepre,a,w,hw,hmoved⟩ :=
    distance_one_chief_three_image_choice ctx hb hfaith branch
  change Subgroup X at Dbar
  change Nat.card Dbar = 3 at hDbar
  change J ≤ Subgroup.normalizer (Dbar : Set X) at hnorm
  change Z ⊓ Subgroup.centralizer ((Dbar.comap projection).map P.subtype : Set G) = ⊥ at hfreepre
  change J at a
  change w ∈ FixedPoints.subgroup Dbar W at hw
  obtain ⟨D,hDP,hDcard,hDmap,hcover,_⟩ := distance_one_chief_three_actor_lift ctx hb hfaith branch Dbar hDbar
  change D ≤ P at hDP
  change (D.subgroupOf P).map projection = Dbar at hDmap
  change Q ⊔ D = (Dbar.comap projection).map P.subtype at hcover
  have hDodd : Odd (Nat.card D) := by rw [hDcard]; decide
  have hZcentral : Z ≤ Subgroup.centralizer (Q : Set G) :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core ctx.criticalPath.a ctx.criticalPath.firstStep
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj)).trans
        ((omegaOneCenter_le_centerAmbient Q).trans (centerAmbient_le_centralizer Q))
  have hfree : Z ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
    apply bot_unique
    intro z hz
    apply hfreepre.le
    refine ⟨hz.1, ?_⟩
    have hQcent : Q ≤ Subgroup.centralizer ({z} : Set G) := by
      intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hZcentral hz.1) q hq)
    have hDcent : D ≤ Subgroup.centralizer ({z} : Set G) := by
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hz.2 d hd)
    have hjoin : Q ⊔ D ≤ Subgroup.centralizer ({z} : Set G) := sup_le hQcent hDcent
    rw [← hcover]
    change z ∈ Subgroup.centralizer ((Q ⊔ D : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (hjoin hp)
  have hmap (E : Subgroup P) : (E.map projection).map X.subtype = E.map action := by
    rw [Subgroup.map_map]
    rfl
  have hDimage : (D.subgroupOf P).map action = Dbar.map X.subtype := by rw [← hmap,hDmap]
  have hnormalizes : (branch.U.subgroupOf P).map action ≤
      Subgroup.normalizer ((D.subgroupOf P).map action : Set (MulAut W)) := by
    rw [hDimage, ← hmap]
    exact (Subgroup.map_mono (f := X.subtype) hnorm).trans
      (Subgroup.le_normalizer_map (H := Dbar) X.subtype)
  have hactor : ((a : X) : MulAut W) ∈ (branch.U.subgroupOf P).map action := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem X.subtype a.property
  have hpoint : w ∈ FixedPoints.subgroup ((D.subgroupOf P).map action) W := by
    rw [hDimage]
    intro d
    obtain ⟨d0,hd0,heq⟩ := d.property
    change (d : MulAut W) w = w
    rw [← heq]
    exact hw ⟨d0,hd0⟩
  apply distance_one_chief_three_actor_contradiction ctx hb hfaith branch D hDP hDodd hfree hnormalizes
  exact ⟨((a : X) : MulAut W), hactor, w, hpoint, hmoved⟩
end Stellmacher.SectionNine
