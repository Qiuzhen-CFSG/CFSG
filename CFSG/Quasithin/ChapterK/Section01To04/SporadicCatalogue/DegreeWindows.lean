module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Source
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.Geometry
public import Theory.Representation.BinaryOffender.CubicNormalizerDegree
public import Theory.Mathieu.M11.Properties.ThreeInvolutions

/-!
# The source sporadic degree windows

Three conjugates of a small-displacement involution bound the original binary
degree by six times the automorphism two-rank. For M11 the required geometry
is already proved. For J1, Ru and J4 the separate model-geometry producers
remain explicit. Thus the remaining windows are 12, 18, 36 and 66, respectively.

The applications below lift bounded representation exclusions to full source
exclusions. They do not mistake the FF lower bounds for contradictions at the
cubic threshold two, and do not assert the outstanding bounded exclusions.
Source: Aschbacher–Smith, K.4, printed p.457, citing GM02, Theorem 6.6.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs
open _root_.Sporadic.Mathieu
universe u v

private theorem m11_threeConjugateAutomorphisms : ThreeConjugateAutomorphisms M11 := by
  intro t ht ht2
  obtain ⟨a, rfl⟩ := m11_automorphism_inner t
  have hinj := MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot
  have ha : a ≠ 1 := fun h => ht (by rw [h, map_one])
  have ha2 : a ^ 2 = 1 := hinj (by rw [map_pow, ht2, map_one])
  obtain ⟨g, h, hgh⟩ := m11_three_involution_conjugates a (orderOf_eq_prime ha2 ha)
  refine ⟨g, h, ?_⟩
  have he := congrArg (fun H : Subgroup M11 => H.map MulAut.conj) hgh
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
    map_mul, map_inv] using he.ge

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)

include ρ h

/-- Actual M11 source modules have degree at most twelve, including all covers
and ambient extensions. This upper bound alone is not an exclusion. -/
theorem m11_degree_le_twelve
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.m11.Carrier) : Module.finrank (ZMod 2) V ≤ 12 := by
  let := h.quasisimple
  exact finrank_le_six_mul_of_cubic_central_quotient ρ (generalizedFitting G)
    h.faithful h.irreducible e m11_threeConjugateAutomorphisms
    m11_automorphism_twoRank_le_two h.cubic_le_two

/-- The existing simple-model geometry contracts imply the source degree bound.
The carrier's finiteness, simplicity and perfectness are inherited from F*(G). -/
theorem degree_le_of_simpleGeometry (name : KnownSimple.SporadicName) (r : ℕ)
    (hg : SimpleGeometry name r)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃* name.Carrier) :
    Module.finrank (ZMod 2) V ≤ 6 * r := by
  let := h.quasisimple
  let : Finite name.Carrier := Finite.of_surjective e e.surjective
  let : IsSimpleGroup (generalizedFitting G ⧸ center (generalizedFitting G)) :=
    IsQuasisimple.simple
  let : IsSimpleGroup name.Carrier := e.symm.isSimpleGroup
  let : Group.IsPerfect name.Carrier :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hgen, hr⟩ := hg
  exact finrank_le_six_mul_of_cubic_central_quotient ρ (generalizedFitting G)
    h.faithful h.irreducible e hgen hr h.cubic_le_two

omit ρ h in
/-- Discharge the degree-window premise using the actual source representation. -/
theorem sourceExclusion_of_bounded (name : KnownSimple.SporadicName) (r : ℕ)
    (hg : SimpleGeometry name r) (hb : BoundedSourceExclusion.{u,v} name (6 * r)) :
    SourceExclusion.{u,v} name := by
  intro G V _ _ _ _ _ ρ h he
  obtain ⟨e⟩ := he
  exact hb ρ h ⟨e⟩ (degree_le_of_simpleGeometry ρ h name r hg e)

omit ρ h in
/-- Only the degree-at-most-twelve M11 calculation remains after proved geometry. -/
theorem sourceExclusion_m11_of_bounded (hb : BoundedSourceExclusion.{u,v} .m11 12) :
    SourceExclusion.{u,v} .m11 := by
  intro G V _ _ _ _ _ ρ h he
  obtain ⟨e⟩ := he
  exact hb ρ h ⟨e⟩ (m11_degree_le_twelve ρ h e)

omit ρ h in
/-- J1's cubic window is eighteen; its old lower bound eighteen does not exclude it. -/
theorem sourceExclusion_j1_of_bounded (hg : SimpleGeometry .j1 3)
    (hb : BoundedSourceExclusion.{u,v} .j1 18) : SourceExclusion.{u,v} .j1 :=
  sourceExclusion_of_bounded .j1 3 hg hb

omit ρ h in
/-- Ru's cubic window is thirty-six, larger than the old degree lower bound. -/
theorem sourceExclusion_ru_of_bounded (hg : SimpleGeometry .ru 6)
    (hb : BoundedSourceExclusion.{u,v} .ru 36) : SourceExclusion.{u,v} .ru :=
  sourceExclusion_of_bounded .ru 6 hg hb

omit ρ h in
/-- J4's cubic window is sixty-six; FF exclusion does not discharge this case. -/
theorem sourceExclusion_j4_of_bounded (hg : SimpleGeometry .j4 11)
    (hb : BoundedSourceExclusion.{u,v} .j4 66) : SourceExclusion.{u,v} .j4 :=
  sourceExclusion_of_bounded .j4 11 hg hb

end CFSG.Quasithin.ChapterK.SporadicCatalogue
