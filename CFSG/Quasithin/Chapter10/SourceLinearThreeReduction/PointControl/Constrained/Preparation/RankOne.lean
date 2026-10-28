module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Orbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Thompson
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Orbits
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.Transport

/-!
# Complete preparation in the original rank-one natural-cover row

A nonzero fixed kernel gives the fixed-layer centralizer argument. If the
kernel vanishes, SL₂ transitivity generates the full moved factor from a
nonidentity point-Sylow fixed vector. The earlier Baumann fixed-orbit theorem
and the actual saturated point give J(C_T(v))=J(T). Thompson movement then
constructs the faithful FF action on the literal reduced orbit.

This proves preparation for every marked rank-one natural cover, including
positive kernels and even field degrees. The ambient model recognition and
torus exclusion remain with qt-d-10-nona5-point-constrained.
Source: Aschbacher--Smith, 10.2.9, printed p.751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- In the zero-kernel rank-one row the seed generates the full moved factor. -/
theorem Context.moved_le_of_rankOneNatural_of_fixed_eq_bot (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) (hz : sourceMovedFixed D = ⊥) :
    ⁅D.fullModule,L⁆ ≤ orbitModule D v I := by
  obtain ⟨n,hn,e,⟨s⟩⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
  have hi : Function.Injective s.coordinates := (MonoidHom.ker_eq_bot_iff _).mp (by
    rw [s.kernel_eq]
    change (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆ = ⊥
    rw [hz,bot_subgroupOf])
  apply c.moved_le_of_transitive
  intro a b ha hb
  have hne (x : (⁅D.fullModule,L⁆ : Subgroup G)) (hx : x ≠ 1) :
      (s.coordinates x).toAdd ≠ 0 := by
    intro he
    exact hx (hi (he.trans (map_one s.coordinates).symm))
  obtain ⟨g,hg⟩ := Matrix.SL2.exists_mulVec_eq (GaloisField 2 n)
    (s.coordinates a).toAdd (s.coordinates b).toAdd (hne a ha) (hne b hb)
  obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) g
  change e (QuotientGroup.mk' (pCore 2 L) l) = g at hl
  refine ⟨l,?_⟩
  have he := s.equivariant l a
  change (s.coordinates _).toAdd = SL2.BinarySmall.natural
    (e (QuotientGroup.mk' (pCore 2 L) l)) (s.coordinates a).toAdd at he
  rw [hl] at he
  exact congrArg Subtype.val (hi (Multiplicative.toAdd.injective (he.trans hg)))

/-- Both fixed-kernel alternatives of the original rank-one cover control C_G(VI). -/
theorem Context.centralizer_le_of_rankOneNatural (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) :
    centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal := by
  by_cases hz : sourceMovedFixed D = ⊥
  · exact c.centralizer_le_of_moved_le
      (c.moved_le_of_rankOneNatural_of_fixed_eq_bot hmodel hz)
  · exact c.centralizer_le_of_moved_fixed_ne_bot hz

/-- Saturation transports the rank-one Baumann fixed orbit to the actual point. -/
theorem Context.thompson_eq_of_rankOneNatural (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) := by
  have hs : Chapter1.IsSylowIn 2 (pointSylow T v)
      (D.maximalLocal ⊓ centralizer ({v} : Set G)) :=
    c.escaping.sylow.restrict
      (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right) inf_le_right
  obtain ⟨m,hm,hfix⟩ := Selection.RankOne.partner_baumann_conjugate_fixed_of_rankOneNatural
    D hmodel c.escaping.t_mem c.escaping.v_mem
  exact source_point_thompson_eq_of_conjugate_fixed D hs
    ⟨m,hm,(map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann _)).trans hfix⟩

/-- Every original rank-one natural cover supplies all three preparation conclusions. -/
theorem Context.prepared_of_rankOneNatural (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) : Prepared D v I :=
  c.prepared_of_centralizer_of_thompson_eq
    (c.centralizer_le_of_rankOneNatural hmodel) (c.thompson_eq_of_rankOneNatural hmodel)

/-- Actual consumer: the rank-one cover gives the full FF conclusion on the specified orbit. -/
theorem Context.actionFacts_of_rankOneNatural (c : Context D t v I)
    (hmodel : Selection.RankOneNatural D) : ActionFacts c :=
  c.actionFacts (c.prepared_of_rankOneNatural hmodel)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
