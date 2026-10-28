module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.MovedAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Source
public import Theory.Representation.BinaryConjugationSection.Relabel

/-!
# Applying moved-quotient recognition to the original Hall context

Either separated-seed orientation gives an irreducible faithful action on
the literal W/C_W(L). An equivariant natural-module recognition transports
through the original quotient map to the precise NaturalSection consumed
by the completed Hall calculation. Thus that recognition alternative is
excluded without identifying W with its central quotient.

This discharges the action and coordinate premises at the natural-row
consumer. Seed separation and the exhaustive B.4 model recognition still
belong to qt-d-10-nona5-central-hall-orders; this is not their source proof.
Source: Aschbacher--Smith 3.2.6, 10.1.1(1) and 10.2.3, pp.581,741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance recognitionMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The original separated seed supplies faithful irreducible quotient data
and crossed geometry in either orientation. The two source classification
steps are not assumed as conclusions of this transport. -/
theorem geometry_and_irreducible_of_separatedSeed
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (h : SeparatedSeed D t) :
    ModuleGeometry D ∧ MovedMinimal D ∧
      (movedQuotientAction D (fun hn => htn (hn ht))).IsIrreducible := by
  obtain ⟨geometry,hmin⟩ := geometry_and_minimality_of_separatedSeed D ht htn h
  exact ⟨geometry,hmin,movedQuotientAction_irreducible D _ hmin⟩

local instance naturalBinaryAlgebra (r : ℕ) : Algebra (ZMod 2) (GaloisField 2 r) :=
  ZMod.algebra _ 2

/-- Natural recognition of the faithful quotient gives the literal natural
row; its central factor is retained in the section denominator. -/
def natural_section_of_movedQuotient
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (r : ℕ)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
    (E : (movedQuotientAction D hn).Equiv
      (SL2.BinarySmall.natural.comp e.toMonoidHom)) : NaturalSection D r e :=
  (movedQuotientSection D hn).relabel (QuotientGroup.mk' (pCore 2 L)) E

/-- The exact natural alternative of moved-quotient recognition is impossible
in the original central Hall context, without discarding C_W(L). -/
theorem not_natural_movedQuotient
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (geometry : ModuleGeometry D) (r : ℕ) (hr : 1 < r)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r)) :
    ¬ Nonempty ((movedQuotientAction D c.nonnormal).Equiv
      (SL2.BinarySmall.natural.comp e.toMonoidHom)) := by
  rintro ⟨E⟩
  exact (HallGeometry.source_hallGeometryAt T L D H B c geometry).natural_excluded r hr e
    (natural_section_of_movedQuotient D c.nonnormal r e E)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
