module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarLayer

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalRefinement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.StarDualCoordinates

/-!
# The literal natural submodule in the source star quotient

The moving cover and the star quotient have the same kernel on U. Their actual
projections therefore identify the natural module with the image of U inside
the star modulo the full fixed core. The first star bound makes this inclusion
a dual cover. The ambient quotient marking also supplies refinement-free
critical actors on this same module, so no change of field or actor is hidden.

The coordinate argument is shared with the original-graph source in
`StarDualCoordinates`; this module preserves the replacement-specific interface.

Source: MS93 (3.4), printed p.869, on the characteristic replacement from Section 7.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
universe u w
variable {H : Type u} {F : Type w} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit h in
private theorem sourceStarDualCover_of_marked_cover
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (Y : Subgroup d.radical) (s₀ : MovedSection ρ B)
    (e : ActionEquiv (s₀.action.comp B.subtype) (binaryNatural (K := E)))
    (he : IsCover (MovedSection.coverProjection s₀ e))
    (j : Multiplicative s₀.space.toSubmodule →* FreeAmalgam d.radical)
    (hjr : j.range = U d.radical (alpha d.radical))
    (s : SourceStarQuotient d.radical Y J)
    (hκL : ((Ltilde d.radical (alpha d.radical)).subgroupOf
      (stabilizer d.radical (alpha d.radical))).map s.quotient = B)
    (hconj : ∀ (g : stabilizer d.radical (alpha d.radical)) (v : s₀.space.toSubmodule),
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (s.quotient g) v)) =
        (g : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam d.radical)⁻¹)
    (hker : ∀ v : s₀.space.toSubmodule, MovedSection.coverProjection s₀ e v = 0 ↔
      j (Multiplicative.ofAdd v) ∈
        centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)))
    (hAQ : sourceStarAlpha d.radical Y ≤ Q d.radical (alpha d.radical))
    (hcomm : ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
      U d.radical (alpha d.radical)) :
    let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
    ∃ i : (binaryNatural (K := E)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      ∀ w, w ∈ i.toLinearMap.range ↔
        ∃ a : sourceStarAlpha d.radical Y, (a : FreeAmalgam d.radical) ∈
          U d.radical (alpha d.radical) ∧ (s.sectionData.coordinates a).toAdd = w := by
  exact marked_star_dual_cover d.radical Y s₀ e he j hjr s hκL hconj hker hAQ hcomm

/-- The actual star modulo the full fixed core is a dual cover of the natural
module over the original field degree. The natural inclusion has exactly the
image of the original moving subgroup. -/
theorem Input.exists_replacement_sourceStarDualCover
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ∃ E : ChapterB.QuasisimpleSource.BinaryField, E.degree = n ∧
    ∃ s : SourceStarQuotient d.radical Y (d.overgroup ⧸ pCore 2 d.overgroup),
    ∃ γ : L (K := E.Carrier) →* (d.overgroup ⧸ pCore 2 d.overgroup),
      Function.Injective γ ∧
      γ.range = (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup)) ∧
      ((Ltilde d.radical (alpha d.radical)).subgroupOf
        (stabilizer d.radical (alpha d.radical))).map s.quotient = γ.range ∧
    ∃ i : (binaryNatural (K := E.Carrier)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      (∀ w, w ∈ i.toLinearMap.range ↔
        ∃ a : sourceStarAlpha d.radical Y, (a : FreeAmalgam d.radical) ∈
          U d.radical (alpha d.radical) ∧ (s.sectionData.coordinates a).toAdd = w) ∧
      ∀ (z : Vertex d.radical) (_path : CriticalPath d.radical geometry (alpha d.radical) z),
        ∃ β : Z d.radical z →* L (K := E.Carrier),
          (∀ (x : Z d.radical z) (hx : (x : FreeAmalgam d.radical) ∈
            stabilizer d.radical (alpha d.radical)), γ (β x) = s.quotient ⟨x,hx⟩) ∧
          ¬ ∃ c : Natural (K := E.Carrier), ∀ b : β.range, ∀ v,
            Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c
              (binaryNatural b.val v) =
            Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c v := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C₀ := (K.subgroupOf d.overgroup).map q
  let : C₀.Normal := (h.replacement_component_image_structure d).2.1
  let ρ₀ := NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)
  let s₀ := MovedSection.ofNormal ρ₀ C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d (a := alpha d.radical) rfl
  change ActionEquiv (s₀.action.comp C₀.subtype) (binaryNatural (K := E.Carrier)) at e
  change IsCover (MovedSection.coverProjection s₀ e) at he
  change Multiplicative s₀.space.toSubmodule →* FreeAmalgam d.radical at j
  obtain ⟨s,hs⟩ := h.exists_replacement_sourceStarQuotient_over d geometry hb Y P hY hn κ hκ hκQ
  let γ : L (K := E.Carrier) →* (d.overgroup ⧸ pCore 2 d.overgroup) :=
    C₀.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = C₀ := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hγinj : Function.Injective γ := Subtype.val_injective.comp e.groupEquiv.symm.injective
  obtain ⟨i,hi,hdual,hrange⟩ := sourceStarDualCover_of_marked_cover d Y s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro g v; rw [hs]; exact hconj g v) hker
    (h.replacement_sourceStarAlpha_le_own_core d geometry (by omega) Y P hY hn)
    (h.replacement_sourceStarAlpha_commutator_le_U d geometry (by omega) Y P hY hn)
  refine ⟨E,hE,s,γ,hγinj,hγ,?_,i,hi,hdual,hrange,?_⟩
  · rw [hs,hγ]
    exact hκL
  · intro z path
    have hpos : 0 < geometry.b d.radical := by omega
    have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
    let rev : CriticalPath d.radical geometry z (alpha d.radical) := {
      start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry hedge (alpha d.radical) rfl
        (by rwa [geometry.distance_constant (alpha d.radical) rfl]) z path.end_color path.critical }
    obtain ⟨β,hβmark,hβno⟩ := h.replacement_refinement_free_inner_actor d (ρ := ρ₀) (B := C₀)
      (show Nat.card E.Carrier = Nat.card F by rw [E.card_eq,hE,h.field_card]) rev hpos
      s₀ e he (h.replacement_component_image_structure d).2.2.2.2 j hj hjr κ hκQ hconj
    refine ⟨β,?_,hβno⟩
    intro x hx
    rw [hs]
    exact hβmark x hx

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
