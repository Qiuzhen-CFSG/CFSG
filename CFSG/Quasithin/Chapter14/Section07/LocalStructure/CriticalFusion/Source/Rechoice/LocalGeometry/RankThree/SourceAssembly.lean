module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.SourceNormalization
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.MarkedControl
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Span
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt

/-!
# The source rank-three geometry before Goldschmidt in 14.7.70

For one prepared critical path, construct the actual core axes by the
restricted F.9.7 pairing and apply full A.1.14 to the original four-group.
If T moves E, the three marked axes generate all six elementary
transvections on the literal commutator. A cubic fixing the original point
then contradicts N_H([U,Uα]) = T, proved on the original marked cover.
Thus T normalizes E and its actual two-residual Y. The proved 14.7.65
fixed-space identities give the literal L₁ orbit span V Zα of rank four.

The output constructs the existing Goldschmidt.Geometry interface; it does
not invoke Goldschmidt classification or the subsequent contradiction.
Neither ThreeAxisAction nor MarkedPlaneControl is an input. The exact
source normalizer bound is used without requiring T to centralize V₂.

Earlier-source inputs retain their producers: Preliminary comes from
qt-14-07-rechoice-preparation; the core-action and commutator equality are
14.5.15(4)/14.5.21(1), owned by qt-14-05; ModuleSeparation is 14.7.2(1),
owned by qt-14-07-solvable; UpperMarking and LocalActors are the compatible
14.3/14.7.65 data, owned by qt-14-03 and qt-14-07. The marked reciprocal
actor is the actual earlier 14.7.39/64/69 input used by pairing_action_source.
Final discharge of those earlier statements stays with qt-14-07.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
proof of 14.7.70, printed p.1074 (PDF p.1091).
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08 Preparation Preparation.MarkedSpans
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- All original rank-three conclusions needed before the Goldschmidt step. -/
structure SourceGeometry (d : Data T L V F W) (c : CriticalPath (L := L) F)
    : Prop extends Goldschmidt.Geometry d c where
  opposite_commutator : ⁅c.Zα, F.H.pCoreIn 2⁆ = F.Vi 1
  point_commutator : ⁅F.Vi 1, c.Qα⁆ = c.Zα
  R₁_normalizes : F.Ri L 1 ≤ normalizer (E c : Set G)
  T_normalizes_residual : (T : Subgroup G) ≤ normalizer (Y c : Set G)
  commutator_normalizer : F.H ⊓ normalizer (Fcomm c : Set G) = (T : Subgroup G)
  normalizer_eq : normalizer (E c : Set G) = YE c ⊔ centralizer (E c : Set G)
  orbit_eq : conjugateSpanBy c.Zα (F.Li L 1) = V ⊔ c.Zα
  orbit_rank : primeRank 2 (conjugateSpanBy c.Zα (F.Li L 1)) = 4
  fixed_opposite : tilde d c.Zα ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d) = fixedT d
  fixed_plane : fixedT d = tilde d (F.Vi 2) ⊔ (d.projection.toLinearMap.ker ⊓ fixedT d)

/-- The source rank-three branch, with the pairing, full moved action,
normalizer calculation and actual orbit span all constructed. -/
theorem source_rank_three_geometry (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (h : Preliminary d c)
    (hcore : ∀ x : F.H, x ∈ pCore 2 F.H → d.action x = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (r : SL2FourNatural.F) (hr : r ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper r)) :
    SourceGeometry d c := by
  let s := d.actionDescentOfCore hcore
  obtain ⟨axes, hfull, hn, hnormalizer, hresidual⟩ :=
    h.pairing_action_source s h21 a ha r hr hmark
  have hN := MarkedControl.normalizer_eq_T d c h s mark
  have hT : (T : Subgroup G) ≤ normalizer (E c : Set G) := by
    intro t ht
    by_contra hm
    exact MovedPlane.cubic_contradiction_of_normalizer_bound h hN.le t
      (ThreeAxes.source_action d c h h21.le axes t ht hm)
  obtain ⟨hfixed, hplane, horbit, hrank, hL⟩ :=
    Span.source_span_geometry d c h hcore mark sep actors hT
  exact {
    rank_three := h.rank_three
    star_central := h.star_central
    Zα_not_le := h.opposite_not_le_seed
    elementary := h.E_elementary
    rank_two := h.E_rank
    T_normalizes := hT
    span := hresidual
    YE_normalizes := h.YE_normalizes h21.le
    full_action := hfull
    YE_normal := hn
    centralizer_two := h.E_centralizer_two
    L₁_not_normalizes := hL
    opposite_commutator := h.opposite_commutator s h21
    point_commutator := h.point_commutator s h21 a ha r hr hmark
    R₁_normalizes := h.R₁_normalizes_E s mark sep actors
    T_normalizes_residual := Preliminary.T_normalizes_residual (h.YE_normalizes h21.le) hn hT
    commutator_normalizer := hN
    normalizer_eq := hnormalizer
    orbit_eq := horbit
    orbit_rank := hrank
    fixed_opposite := hfixed
    fixed_plane := hplane }

/-- Actual application to the existing next-stage interface, before its
independent Goldschmidt classification and rank contradiction. -/
theorem goldschmidt_geometry_of_source (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (h : Preliminary d c)
    (hcore : ∀ x : F.H, x ∈ pCore 2 F.H → d.action x = 1)
    (mark : UpperMarking d) (sep : d.ModuleSeparation) (actors : LocalActors d)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (r : SL2FourNatural.F) (hr : r ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper r)) :
    Goldschmidt.Geometry d c :=
  (source_rank_three_geometry d c h hcore mark sep actors h21 a ha r hr hmark).toGeometry

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
