module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixResidual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedSix
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.Seed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.Transport

public import Theory.Representation.HexacodeAction.SolvablePoint

/-!
# The original six-cover parabolic and surviving field point

A recognized quotient section controls the actual action on K/O₂,Z(K).
The solvable-overgroup argument first excludes Y=L₁. The native marked
six-group geometry then proves that H∩M=L₁T is maximal. The source seed
is irreducible of binary dimension two and survives every proper invariant
quotient, so maximality identifies its full stabilizer. The residual cubic
scalar makes this seed an actual F₄-point in the recognized hexacode.

Since the original L₁T is solvable, that point cannot be full-weight: its
even stabilizer would have an A₅ quotient. It is therefore a coordinate-pair
point, giving the literal pair geometry required by the terminal V_H/U_H
obstruction. In the reducible source case native recognition supplies the
quotient coordinates, so no selection or parabolic premise remains.

The remaining irreducible selection and terminal critical-action assembly
stay with qt-d-138-fields-source; qt-d-1381-source supplies SourceContext.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), using
13.8.13, F.9.18(6) and the original seed V₃/V₁.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.ModuleRecognition SourceCompletion
open LocalGeometry LocalGeometry.DynkinExclusion LocalGeometry.CoverParabolics
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
attribute [local instance] Selection.starImage_normal

private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

private noncomputable def centralSixEquiv
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) :
    ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) ≃* AlternatingSix.ShadowLocal.A6 :=
  (QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
    Hexacode.even_quotient_center_equiv

variable [IsElementaryAbelian 2 (Source.UH H V₃)] [(K.subgroupOf H).Normal]

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- A faithful recognized actor proves the original maximal parabolic. -/
theorem source_six_cover_parabolic
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (a : Source.Hstar H →* Atlas.Codes.HexAutomorphisms) (ha : Function.Injective a)
    (hK : (Source.starImage H K).map a = Atlas.Codes.hexSign.ker) :
    IsCoatom ((H ⊓ M).subgroupOf H) ∧ H ⊓ M = one L T V₁ ⊔ (T : Subgroup G) ∧
      IsCoatom (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))) := by
  let eZ := centralSixEquiv e
  have hn := sourceAction_natural_of_actor H K (component_le c) c.component.component eZ
    a ha hK
  have hne := source_six_cover_residual_ne_one_of_natural c eZ hn
  have hH := c.component.local_overgroup
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  let := LocalFitting.local_solvable c.localSetup
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let s : MarkedSetup H K (one L T V₁) T G₁ M := {
    mem_Hz := hH
    component_le := component_le c
    component := c.component.component
    component_normal := c.component.normal
    sylow := ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩
    sylow_le_M := by rw [c.localSetup.local_normalizer]; exact c.localSetup.normalizes_L
    generated := (source_six_cover_consequences c e).2.1
    seed_le_component := source_six_cover_containment c e
    seed_solvable := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (show one L T V₁ ≤ one L T V₁ ⊔ (T : Subgroup G) from le_sup_left))
    theta := c.component.theta
    proper_residual := lt_of_le_of_ne (source_residual_located c hc).2 hne
    quasisimple := IsQuasisimple.of_mulEquiv e.symm
    center_card := hc
    solvable_overgroups := SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 }
  let d := (centralPreimageQuotientEquiv (pCore 2 K)).trans eZ
  have hd : (s.sixAction d).range ≤ AlternatingSix.ShadowLocal.natural := by
    rintro _ ⟨h,rfl⟩
    have hh := hn (QuotientGroup.mk' (pCore 2 H) h)
    rwa [sourceAction_eq_centralModelAction] at hh
  obtain ⟨hm,he,hstar,_⟩ := s.six_marked_parabolic d hd
  exact ⟨hm,he,star_base_isCoatom H M (one L T V₁) T hm
    ((c.f9 H hH).QH_le_T.trans s.sylow_le_M) hstar⟩

omit [Finite G] in
private theorem seed_eq_source : Reduction.seedSpace H V₃ V₁ =
    AlternatingAndLinear.FourStructure.ChiefFactors.sourceSeedSpace H V₃ V₁ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨v,le_conjugateSpanBy V₃ H v.property⟩,v.property,rfl⟩
  · rintro v ⟨w,hw,rfl⟩
    exact Submodule.subset_span ⟨⟨w,hw⟩,rfl⟩

open AlternatingAndLinear.FourStructure.OriginalSource
open Components.Swapped.LinearTwo.ModuleAlternatives

/-- Recognition on a literal proper quotient marks the surviving F₄-point. -/
theorem source_six_cover_quotient_marked_point
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hW : W ≠ ⊤)
    (q : HexacodeModel (Source.starImage H K) W.quotientRepresentation) :
    ∃ D : Submodule Hexacode.F Atlas.Codes.hexacode,
      Module.finrank Hexacode.F D = 1 ∧ D.restrictScalars (ZMod 2) =
        ((Reduction.seedSpace H V₃ V₁).map W.toSubmodule.mkQ).map q.coordinates.toLinearMap ∧
      (subspaceStabilizer Hexacode.action (D.restrictScalars (ZMod 2))).comap q.actor =
        Source.starImage H (one L T V₁ ⊔ (T : Subgroup G)) := by
  have hH := c.component.local_overgroup
  let P := one L T V₁ ⊔ (T : Subgroup G)
  have hP : P ≤ normalizer (V₃ : Set G) :=
    sup_le (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup c.localSetup))
      c.localSetup.seed_stable
  have he : seedRepresentation H V₃ V₁ act P hP =
      markedSeed H V₃ V₁ act.representation act.conjugation P hP := by
    apply Subrepresentation.toSubmodule_injective
    exact seed_eq_source
  let : IsIrreducible (seedRepresentation H V₃ V₁ act P hP).toRepresentation := by
    rw [he]
    exact markedSeed_irreducible H V₃ V₁ act.representation act.conjugation P hH.1.2 hP
      (c.f9 H hH).point_lt
      (fun X hx hy hn => seed_irreducible_source c.localSetup (le_sup_left.trans hH.1.2)
        act.representation act.conjugation X hx hy (le_sup_left.trans hn))
  have hd : Module.finrank (ZMod 2) (Reduction.seedSpace H V₃ V₁) = 2 := by
    rw [seed_eq_source]
    exact AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.sourceSeed_finrank_of_index
      H V₃ V₁ (seed_index_source c.localSetup)
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  let B := (Reduction.seedSpace H V₃ V₁).map W.toSubmodule.mkQ
  let S := B.map q.coordinates.toLinearMap
  have hmark : (subspaceStabilizer Hexacode.action S).comap q.actor = Source.starImage H P := by
    have hb : subspaceStabilizer W.quotientRepresentation B = Source.starImage H P :=
      quotient_seed_stabilizer H V₃ V₁ act P hP
        (source_six_cover_parabolic c e q.actor q.faithful q.component_image).2.2 W hW hd q.finrank
    rw [←hb]
    ext g
    have heq (v) : q.coordinates v ∈ S ↔ v ∈ B := by
      constructor
      · rintro ⟨x,hx,hxv⟩
        exact q.coordinates.injective hxv ▸ hx
      · exact fun hv => ⟨v,hv,rfl⟩
    change (∀ v, Hexacode.action (q.actor g) v ∈ S ↔ v ∈ S) ↔ _
    constructor
    · intro h v
      simpa only [←q.intertwines,heq] using h (q.coordinates v)
    · intro h v
      obtain ⟨x,rfl⟩ := q.coordinates.surjective v
      rw [←q.intertwines,heq,heq]
      exact h x
  have hz : Atlas.Codes.hexZ ∈ subspaceStabilizer Hexacode.action S := by
    obtain ⟨z,hz,he⟩ := scalar_mem_of_residual_le H K (component_le c) c.component.component
      q.actor q.faithful q.component_image P ((source_residual_located c hc).2.trans le_sup_left)
    rw [←he]
    exact (show z ∈ (subspaceStabilizer Hexacode.action S).comap q.actor from hmark ▸ hz)
  refine ⟨Hexacode.scalarSubmodule S hz,?_,rfl,hmark⟩
  have hs : Module.finrank (ZMod 2) S = 2 := by
    rw [show S = B.map q.coordinates.toLinearMap from rfl,q.coordinates.finrank_map_eq]
    exact quotient_seed_finrank H V₃ V₁ act P hP W hW hd
  have hh := Hexacode.scalarSubmodule_finrank S hz
  rw [hs] at hh
  omega

/-- The original solvable parabolic selects the fifteen-pair orbit. -/
theorem source_six_cover_quotient_pair
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hW : W ≠ ⊤)
    (q : HexacodeModel (Source.starImage H K) W.quotientRepresentation) :
    ∃ (D : Submodule Hexacode.F Atlas.Codes.hexacode)
      (s : BinaryPermutation.SixPairsQuadratic.Pair),
      Module.finrank Hexacode.F D = 1 ∧
      D.restrictScalars (ZMod 2) =
        ((Reduction.seedSpace H V₃ V₁).map W.toSubmodule.mkQ).map q.coordinates.toLinearMap ∧
      D.restrictScalars (ZMod 2) = Hexacode.zeroPairPlane s ∧
      (subspaceStabilizer Hexacode.action (D.restrictScalars (ZMod 2))).comap q.actor =
        Source.starImage H (one L T V₁ ⊔ (T : Subgroup G)) := by
  obtain ⟨D,hd,hseed,hpoint⟩ := source_six_cover_quotient_marked_point c e act W hW q
  have heven : Atlas.Codes.hexSign.ker ≤ q.actor.range := by
    rw [←q.component_image]
    exact map_le_range _ _
  have hsolv : Group.IsSolvable (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))) := by
    let := LocalFitting.local_solvable c.localSetup
    let : Group.IsSolvable ((one L T V₁ ⊔ (T : Subgroup G)).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe c.component.local_overgroup.1.2).toMonoidHom)
        (subgroupOfEquivOfLe c.component.local_overgroup.1.2).injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  obtain ⟨s,hs⟩ := Hexacode.fieldPoint_pair_of_solvable_stabilizer q.actor heven D hd
    (hpoint.symm ▸ hsolv)
  exact ⟨D,s,hd,hseed,hs,hpoint⟩

/-- Every nonzero proper invariant section of the original six-cover module
supplies the actual pair point, with all recognition and source inputs discharged. -/
theorem source_six_cover_pair_of_proper_section
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hb : W ≠ ⊥) (ht : W ≠ ⊤) :
    ∃ (q : HexacodeModel (Source.starImage H K) W.quotientRepresentation)
      (D : Submodule Hexacode.F Atlas.Codes.hexacode)
      (s : BinaryPermutation.SixPairsQuadratic.Pair),
      Module.finrank Hexacode.F D = 1 ∧
      D.restrictScalars (ZMod 2) =
        ((Reduction.seedSpace H V₃ V₁).map W.toSubmodule.mkQ).map q.coordinates.toLinearMap ∧
      D.restrictScalars (ZMod 2) = Hexacode.zeroPairPlane s ∧
      (subspaceStabilizer Hexacode.action (D.restrictScalars (ZMod 2))).comap q.actor =
        Source.starImage H (one L T V₁ ⊔ (T : Subgroup G)) := by
  obtain ⟨_,⟨q⟩,_⟩ := source_six_cover_proper_sections c e act W hb ht
  exact ⟨q,source_six_cover_quotient_pair c e act W ht q⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
