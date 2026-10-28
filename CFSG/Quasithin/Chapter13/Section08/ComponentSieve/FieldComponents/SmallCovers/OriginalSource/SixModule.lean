module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.Residual
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.NativeSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Actors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SeedTransport
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.Quotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion

/-!
# Cubic action and native section recognition in the original six-cover case

The original containment H=KT and its literal Sylow image identify K* with
F*(H*). This supplies the centralizer bound for the proved native B.4
classification. The earlier residual alternatives give [V₃,Y]=V₃ both when
Y=L₁ and when Y=L₁,+; the original quotient map then gives the primitive
cubic polynomial on U_H/V₁. No proper-residual conclusion is assumed.

The genuine F.9 edge actor gives the small quadratic ratio on every action
with the literal conjugation formula. Cubic faithfulness and the native
classification exclude strong FF-modules on all nonzero invariant sections.
If the source module is reducible, fixed-codimension additivity forces both
sections to be FF-modules, hence actual six-dimensional hexacode modules;
the whole module then has dimension twelve.

The invariant-constituent selection in the remaining irreducible case and
the terminal V_H/U_H contradiction remain with qt-d-138-fields-source.
The preceding SourceContext assumptions are supplied by qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), using
13.8.13, F.9.16, F.9.18(6), B.4.2(8) and B.4.5.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.ModuleRecognition SourceCompletion
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Components.Swapped.LinearTwo.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

private noncomputable def sixStarEquiv
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) :
    Source.starImage H K ≃* Atlas.Codes.HexEvenAutomorphisms :=
  (Components.componentStarEquiv H K (component_le c) c.component.component).symm.trans e

/-- The actual K-star is the generalized Fitting subgroup of H-star. -/
theorem source_six_cover_fitting
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) :
    generalizedFitting (Source.Hstar H) = Source.starImage H K := by
  let := c.component.normal
  let : (Source.starImage H K).Normal := Selection.starImage_normal H K
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple (Source.starImage H K) := IsQuasisimple.of_mulEquiv (sixStarEquiv c e).symm
  have hH := c.component.local_overgroup
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨P,hP⟩ := LinearThree.Geometry.ParabolicMarking.starImage_sylow H T hTH
  have hgen := LocalGeometry.DynkinExclusion.star_sylow_generation H K (T : Subgroup G)
    (source_six_cover_consequences c e).2.1 P hP
  have hquot : IsPGroup 2 (Source.Hstar H ⧸ Source.starImage H K) :=
    isPGroup_quotient_of_sup_eq_top _ (P : Subgroup (Source.Hstar H)) P.isPGroup' hgen
  exact generalizedFitting_eq_of_quasisimple_two_quotient _ hquot (pCore_quotient_pCore_eq_bot 2)

private theorem source_sqtk (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H) := by
  refine ⟨?_,c.component.sqtk.isKGroup.quotient (pCore 2 H)⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
    (c.component.sqtk.stronglyQuasithin p hp ho)

/-- Both irreducible B.4 inputs follow from the original source context. -/
theorem source_six_cover_irreducibleInputs
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) :
    IrreducibleInputs.{u,u} (Source.starImage H K) := by
  let := c.component.normal
  let : (Source.starImage H K).Normal := Selection.starImage_normal H K
  have hc : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K := by
    rw [←source_six_cover_fitting c e]
    exact centralizer_generalizedFitting_le _
  exact NativeSource.irreducibleInputs _ (source_sqtk c) (sixStarEquiv c e) hc

/-- Both earlier residual alternatives move the whole original seed. -/
theorem source_cover_residual_moves_seed
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3) :
    ⁅V₃,coverResidualIn K⁆ = V₃ := by
  rcases source_residual_alternatives c hc with hy | ⟨hL,hy⟩
  · rw [hy]
    exact Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup c.localSetup)
  · rw [hy]
    exact Section07.ModelExclusions.seed_commutator_plus (localNaturalSetup c.localSetup) hL

section Module
variable [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [Finite G] in
private theorem seed_eq_source : Reduction.seedSpace H V₃ V₁ =
    AlternatingAndLinear.FourStructure.ChiefFactors.sourceSeedSpace H V₃ V₁ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨v,le_conjugateSpanBy V₃ H v.property⟩,v.property,rfl⟩
  · rintro v ⟨w,hw,rfl⟩
    exact Submodule.subset_span ⟨⟨w,hw⟩,rfl⟩

/-- The seed movement descends through the literal original quotient map. -/
theorem source_cover_residual_seed_commutator
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (act : QuotientAction H V₃ V₁) :
    subspaceCommutator act.representation (Reduction.seedSpace H V₃ V₁)
      (Source.starImage H (coverResidualIn K)) = Reduction.seedSpace H V₃ V₁ := by
  rw [seed_eq_source]
  exact image_commutator_eq H V₃ V₁ act.representation act.conjugation
    (coverResidualIn K) V₃ ((coverResidualIn_le K).trans (component_le c))
    (le_conjugateSpanBy V₃ H)
    ((source_residual_located c hc).2.trans
      (Section07.ModelExclusions.point_residual_normalizes_seed (localNaturalSetup c.localSetup)))
    act.line_le (by rw [commutator_comm,source_cover_residual_moves_seed c hc]; exact le_sup_left)

/-- The original F.9 geometry bounds any action with the literal conjugation formula. -/
theorem source_quotient_small_ratio
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : QuotientAction H V₃ V₁) : quadraticRatio act.representation ≤ 2 := by
  obtain ⟨a,B,_,hq⟩ := F918.exists_edge_quadratic_actor c.localSetup
    (c.f9 H c.component.local_overgroup)
  have he : act.representation =
      SolvableExclusion.Three.Supercritical.Offenders.linearAction a := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
    exact (act.conjugation h u).trans (a.conjugation h u).symm
  rw [he]
  exact (quadraticRatio_le_two_iff _).mpr ⟨Source.starImage H B,hq⟩

/-- The genuine seed orders give a nonzero literal source quotient. -/
theorem source_quotient_nontrivial
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) :
    Nontrivial (Additive (Source.Utilde H V₃ V₁)) := by
  have hline := c.localSetup.line_le_plane.trans c.localSetup.plane_le_seed
  have hproper : V₁ < V₃ := by
    apply lt_of_le_of_ne hline
    intro he
    have h1 := c.localSetup.line_card
    have h3 := c.localSetup.seed_card
    rw [he] at h1
    omega
  obtain ⟨v,hv,hn⟩ := SetLike.exists_of_lt hproper
  let w : Source.UH H V₃ := ⟨v,le_conjugateSpanBy V₃ H hv⟩
  have hh : QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) w ≠ 1 := by
    intro he
    exact hn ((QuotientGroup.eq_one_iff w).mp he)
  exact ⟨⟨Additive.ofMul (QuotientGroup.mk' _ w),0,hh⟩⟩

/-- The original residual generates the whole literal module in both local cases. -/
theorem source_cover_residual_moves_quotient
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (act : QuotientAction H V₃ V₁) :
    subspaceCommutator act.representation ⊤ (Source.starImage H (coverResidualIn K)) = ⊤ := by
  let := c.component.normal
  exact residual_generates_quotient H V₃ V₁ act K (component_le c)
    (source_cover_residual_seed_commutator c hc act)

/-- A central generator of order three acts by the primitive cubic polynomial. -/
theorem source_six_cover_cubic_polynomial
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁) :
    ∃ z ∈ Source.starImage H K, orderOf z = 3 ∧
      zpowers z = (center (Source.starImage H K)).map (Source.starImage H K).subtype ∧
      CubicPolynomial act.representation z := by
  let := c.component.normal
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans Hexacode.even_center_card
  obtain ⟨z,hz,ho,hgen,hp⟩ := exists_residual_cubic_polynomial H K V₃ V₁ act
    (component_le c) c.component.component e (source_cover_residual_seed_commutator c hc act)
  exact ⟨z,hz,ho,hgen.trans (residual_star_eq_center H K (component_le c) c.component.component hc),hp⟩

/-- Cubic faithfulness and the native FF passage hold on all proper sections. -/
theorem source_six_cover_sections
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁) :
    (∀ W : Subrepresentation act.representation, W ≠ ⊥ →
      Function.Injective W.toRepresentation ∧ ¬ IsStrongFFModule W.toRepresentation) ∧
    (∀ W : Subrepresentation act.representation, W ≠ ⊤ →
      Function.Injective W.quotientRepresentation ∧ ¬ IsStrongFFModule W.quotientRepresentation ∧
        (IsFFModule W.quotientRepresentation →
          Nonempty (HexacodeModel (Source.starImage H K) W.quotientRepresentation))) := by
  let := c.component.normal
  let : (Source.starImage H K).Normal := Selection.starImage_normal H K
  let : IsQuasisimple Atlas.Codes.HexEvenAutomorphisms := Hexacode.even_isQuasisimple
  let : IsQuasisimple (Source.starImage H K) := IsQuasisimple.of_mulEquiv (sixStarEquiv c e).symm
  have hc : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K := by
    rw [←source_six_cover_fitting c e]
    exact centralizer_generalizedFitting_le _
  obtain ⟨z,hz,ho,hzc,hp⟩ := source_six_cover_cubic_polynomial c e act
  have hcz := FFPassage.centralizer_le_zpowers _ z hc hzc
  constructor
  · intro W hW
    let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
      (fun he => hW (Subrepresentation.toSubmodule_injective he))
    exact ⟨faithful_subrepresentation_of_cubicPolynomial act.representation _ z hz ho hcz hp W hW,
      (FFPassage.passage W.toRepresentation _ (sixStarEquiv c e)
        (source_six_cover_irreducibleInputs c e) z ho hzc hc (hp.subrepresentation W)).1⟩
  · intro W hW
    let : Nontrivial (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule) :=
      Submodule.Quotient.nontrivial_iff.mpr
        (fun he => hW (Subrepresentation.toSubmodule_injective he))
    have hh := FFPassage.passage W.quotientRepresentation _ (sixStarEquiv c e)
      (source_six_cover_irreducibleInputs c e) z ho hzc hc (hp.quotient W)
    exact ⟨faithful_quotient_of_cubicPolynomial act.representation _ z hz ho hcz hp W hW,
      hh.1,fun hff => (hh.2 hff).2.1⟩
/-- If the literal source module is reducible, every nonzero proper invariant
section and its quotient are actual hexacode modules. -/
theorem source_six_cover_proper_sections
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (e : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple)
    (act : QuotientAction H V₃ V₁)
    (W : Subrepresentation act.representation) (hb : W ≠ ⊥) (ht : W ≠ ⊤) :
    Nonempty (HexacodeModel (Source.starImage H K) W.toRepresentation) ∧
    Nonempty (HexacodeModel (Source.starImage H K) W.quotientRepresentation) ∧
    Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 12 := by
  let := c.component.normal
  let : (Source.starImage H K).Normal := Selection.starImage_normal H K
  let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun he => hb (Subrepresentation.toSubmodule_injective he))
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.mpr
      (fun he => ht (Subrepresentation.toSubmodule_injective he))
  have hc : centralizer (Source.starImage H K : Set (Source.Hstar H)) ≤ Source.starImage H K := by
    rw [←source_six_cover_fitting c e]
    exact centralizer_generalizedFitting_le _
  obtain ⟨z,_,ho,hzc,hp⟩ := source_six_cover_cubic_polynomial c e act
  have hs := FFPassage.passage W.toRepresentation _ (sixStarEquiv c e)
    (source_six_cover_irreducibleInputs c e) z ho hzc hc (hp.subrepresentation W)
  have hq := FFPassage.passage W.quotientRepresentation _ (sixStarEquiv c e)
    (source_six_cover_irreducibleInputs c e) z ho hzc hc (hp.quotient W)
  obtain ⟨A,hA,_,hbound⟩ := (quadraticRatio_le_two_iff _).mp (source_quotient_small_ratio c act)
  have hsum := fixedCodim_quotient_add_subrepresentation_le act.representation W A
  have hlowS : rank A ≤ fixedCodim W.toRepresentation A := by
    exact Nat.le_of_not_gt (fun hlt => hs.1 ⟨A,hA,hlt⟩)
  have hlowQ : rank A ≤ fixedCodim W.quotientRepresentation A := by
    exact Nat.le_of_not_gt (fun hlt => hq.1 ⟨A,hA,hlt⟩)
  have hfs : IsFFModule W.toRepresentation := ⟨A,hA,by omega⟩
  have hfq : IsFFModule W.quotientRepresentation := ⟨A,hA,by omega⟩
  have ds := hs.2 hfs
  have dq := hq.2 hfq
  refine ⟨ds.2.1,dq.2.1,?_⟩
  have hd := W.toSubmodule.finrank_quotient_add_finrank
  rw [ds.2.2,dq.2.2] at hd
  exact hd.symm

end Module
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
