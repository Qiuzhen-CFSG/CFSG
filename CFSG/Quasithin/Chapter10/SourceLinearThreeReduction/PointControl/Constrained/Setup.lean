module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfSylow
public import CFSG.Quasithin.ChapterB.QuasisimpleOffenderModels

/-!
# The literal constrained point action

The context contains exactly the original inputs to the constrained branch of
point control. Its module is the I-orbit of C_[V,L](C_T(v)), inside I C_T(v).
The centralizer bound and Thompson movement are separate conclusions to be
proved. In particular we do not assume that this orbit contains [V,L]: the
fixed-layer case on p.751 must also be treated.

Source: Aschbacher--Smith, 10.2.9, printed pp.751--753, combined manuscript
of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original Sylow subgroup of the point centralizer. -/
abbrev pointSylow (T : Sylow 2 G) (v : G) : Subgroup G :=
  (T : Subgroup G) ⊓ centralizer ({v} : Set G)

/-- The actual join on which the orbit module is reduced. -/
abbrev pointJoin (T : Sylow 2 G) (v : G) (I : Subgroup G) : Subgroup G :=
  I ⊔ pointSylow T v

/-- The orbit of the literal fixed seed, as a subgroup of G. -/
abbrev orbitModule (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (v : G) (I : Subgroup G) : Subgroup G :=
  conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (pointSylow T v : Set G)) I

/-- The same orbit inside the characteristic-two join. -/
abbrev internalModule (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (v : G) (I : Subgroup G) : Subgroup (pointJoin T v I) :=
  (orbitModule D v I).subgroupOf (pointJoin T v I)

/-- Only hypotheses supplied by the parent constrained-exclusion contract. -/
structure Context (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (t v : G) (I : Subgroup G) : Prop where
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  minimal : D.IsMinimalFullModule
  nonA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  escaping : EscapingComponent D t v I
  not_quasisimple : ¬ IsQuasisimple I
  characteristic_two : generalizedFitting (pointJoin T v I) = pCore 2 (pointJoin T v I)
  reduced : IsPReduced 2 (internalModule D v I)

/-- The source geometry needed before applying the complete FF theorem.
These are obligations, not additional fields of the original context. -/
structure Prepared (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (v : G) (I : Subgroup G) : Prop where
  centralizer_le : centralizer (orbitModule D v I : Set G) ≤ D.maximalLocal
  thompson_eq : elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G)
  thompson_moves : ¬ elementaryAbelianMaxJ (pointSylow T v) ≤
    centralizer (orbitModule D v I : Set G)

variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The source point is a nonidentity involution of the original full module. -/
theorem Context.point_involution (c : Context D t v I) : orderOf v = 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v
    (partner_le_fullModule D c.escaping.t_mem c.escaping.v_mem)) c.escaping.v_ne

theorem Context.orbit_le_component (c : Context D t v I) : orbitModule D v I ≤ I :=
  conjugateSpanBy_le_self (inf_le_left.trans
    ((source_full_moved_le_component D).trans c.escaping.strict.le))

theorem Context.orbit_le_join (c : Context D t v I) :
    orbitModule D v I ≤ pointJoin T v I := c.orbit_le_component.trans le_sup_left

/-- SQTK is inherited from the actual involution centralizer, not from a
family name assigned to the action quotient. -/
theorem Context.join_sqtk (c : Context D t v I) :
    IsSQTK KnownSimple.IsKnownSimple (pointJoin T v I) :=
  (IsSQTK.equiv (subgroupOfEquivOfLe
    (sup_le c.escaping.le_centralizer inf_le_right))).mp
    ((D.simpleQTKE.involution_centralizer_sqtk c.point_involution).subgroup _)

/-- Restriction of the supplied full point Sylow to its literal join with I. -/
theorem Context.join_sylow (c : Context D t v I) :
    Chapter1.IsSylowIn 2 (pointSylow T v) (pointJoin T v I) :=
  c.escaping.sylow.restrict le_sup_right (sup_le c.escaping.le_centralizer inf_le_right)

end CFSG.Quasithin.Chapter10.PointControl.Constrained
