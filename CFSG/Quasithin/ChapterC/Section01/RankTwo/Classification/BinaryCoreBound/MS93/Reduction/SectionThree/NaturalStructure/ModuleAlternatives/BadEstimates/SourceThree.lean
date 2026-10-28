module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Basic
public import Theory.GroupAction.SubgroupQuotientCommutatorBound

/-!
# The literal centralizer action for MS93 (3.3)

Write R₀ = [Z_a,Z_a'] and A = X_a ∩ Q_a'. The subgroup
Q_t ∩ C(R₀) acts by conjugation on X_a'/R₀: adjacency normalizes X_a',
the centralizer fixes R₀, and the elementary endpoint layer supplies relative
normality. At a critical pair, R₀ is contained in X_a', so the relative
quotient uses the entire source commutator.

This module constructs that action and lifts an explicit quotient displacement
calculation to [Z_a',Y] ≤ [X_a,X_a'] ⊔ [A,Y]. The calculation itself remains
a premise of bound_of_quotient_displacement; no theorem here constructs it
from BadCase or asserts Source33Bound.

The actor is the literal centralizer, not the whole edge kernel. In particular
the construction does not require invariance of [X_a,X_a'] under Q_t.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation (3.0), printed p.859, and (3.3), printed p.866.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceThree
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The literal actor group from printed (3.3). -/
def centralizingActors (R : Subgroup M) (a a' t : Vertex R) :
    Subgroup (FreeAmalgam R) :=
  Q R t ⊓ centralizer ((⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) :
    Set (FreeAmalgam R))

/-- These actors normalize the endpoint layer using adjacency alone. -/
theorem centralizingActors_normalize_X (a a' t : Vertex R)
    (hat : Adjacent R a' t) :
    centralizingActors R a a' t ≤ normalizer (X R a' : Set (FreeAmalgam R)) := by
  intro g hg
  exact X_normalized R a' (hg.1.2 a' (adjacent_symm R hat))

/-- Relative normality in the elementary endpoint layer. -/
theorem critical_Z_quotient_normal (a a' : Vertex R) :
    ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')).Normal := by
  let := X_elementary R a'
  infer_instance

/-- The source centralizer acts by literal conjugation on the endpoint
quotient by the source commutator. Its invariance is proved, not assumed. -/
theorem exists_centralizingActors_action (a a' t : Vertex R)
    (hat : Adjacent R a' t) :
    letI := critical_Z_quotient_normal a a'
    ∃ action : centralizingActors R a a' t →*
        MulAut (X R a' ⧸ (⁅Z R a, Z R a'⁆).subgroupOf (X R a')),
      ∀ actor : centralizingActors R a a' t, ∀ point : X R a',
        action actor
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) =
        QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))
          ⟨(actor : FreeAmalgam R) * (point : FreeAmalgam R) *
              (actor : FreeAmalgam R)⁻¹,
            (mem_normalizer_iff.mp
              (centralizingActors_normalize_X a a' t hat actor.property) point).mp
                point.property⟩ := by
  apply exists_quotient_conjugation_action
    (centralizingActors R a a' t) (X R a') (⁅Z R a, Z R a'⁆)
    (centralizingActors_normalize_X a a' t hat)
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
    (critical_Z_quotient_normal a a')

variable [Finite M]

/-- The source R lies in the auxiliary commutator used by (2.3). -/
theorem critical_Z_commutator_le_auxiliary (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅Z R a, Z R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  exact commutator_mono
    (geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; exact hb))
    (critical_endpoint_choice source geometry hb a ha a' hc).1

/-- At a critical pair the quotient kernel above is the entire source R,
not just its intersection with the endpoint layer. -/
theorem critical_Z_commutator_le_endpoint_X (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅Z R a, Z R a'⁆ ≤ X R a' :=
  (critical_Z_commutator_le_auxiliary source geometry hb a ha a' hc).trans
    ((critical_commutator_le_intersection source geometry hb a ha a' hc).trans inf_le_right)

/-- A displacement calculation in the literal source quotient suffices for
the local estimate. The model calculation remains an explicit premise. -/
theorem bound_of_quotient_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ centralizingActors R a a' t) :
    letI := critical_Z_quotient_normal a a'
    ∀ action : centralizingActors R a a' t →*
        MulAut (X R a' ⧸ (⁅Z R a, Z R a'⁆).subgroupOf (X R a')),
      (∀ actor : centralizingActors R a a' t, ∀ point : X R a',
        action actor
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) =
        QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a'))
          ⟨(actor : FreeAmalgam R) * (point : FreeAmalgam R) *
              (actor : FreeAmalgam R)⁻¹,
            (mem_normalizer_iff.mp
              (centralizingActors_normalize_X a a' t hat actor.property) point).mp
                point.property⟩) →
      (∀ actor : centralizingActors R a a' t, (actor : FreeAmalgam R) ∈ Y →
        ∀ point : X R a', (point : FreeAmalgam R) ∈ Z R a' →
        (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point)⁻¹ *
          action actor
            (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')) point) ∈
        (⁅X R a ⊓ Q R a', Y⁆.subgroupOf (X R a')).map
          (QuotientGroup.mk' ((⁅Z R a, Z R a'⁆).subgroupOf (X R a')))) →
      ⁅Z R a', Y⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆ := by
  let := critical_Z_quotient_normal a a'
  intro action hformula hdisplacement
  have h := quotient_conjugation_commutator_le_sup
    (centralizingActors R a a' t) (X R a') (⁅Z R a, Z R a'⁆) (Z R a') Y
    (⁅X R a ⊓ Q R a', Y⁆) (centralizingActors_normalize_X a a' t hat) hY
    (critical_endpoint_choice source geometry hb a ha a' hc).1
    action hformula hdisplacement
  rw [commutator_comm, sup_comm] at h
  exact h.trans (sup_le_sup
    (critical_Z_commutator_le_auxiliary source geometry hb a ha a' hc) le_rfl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceThree
