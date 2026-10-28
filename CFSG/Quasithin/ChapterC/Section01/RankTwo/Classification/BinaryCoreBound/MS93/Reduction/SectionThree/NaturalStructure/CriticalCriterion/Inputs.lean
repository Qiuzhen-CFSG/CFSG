module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Extensions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer
public import Theory.ElementaryAbelian.Join
public import Theory.Frattini.PGroup

/-!
# The literal hypotheses of the critical-distance-four criterion

These are the hypotheses (b)--(d) of MS93 (2.3), p.857. Conjugate generation
is relative to the vertex stabilizer. The subgroup in (c) belongs to the
**far** endpoint X, and the Frattini condition is on the actual join. The
predecessor is specified by adjacency and distance along the geodesic.

`EdgeWitness` describes one subgroup on one oriented edge, not a covariant
family. Its normality is relative to the indicated local group, and the
containment in X is retained separately. Transport of such a witness is a
proof obligation, not an additional hypothesis of the criterion.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.3), printed pp.857--859.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
open NormalizerTransfer
variable {M : Type*} [Group M] (R : Subgroup M)

/-- Source (b), on the translates of an oriented edge. -/
def Generation : Prop :=
  ∀ a t, color R a = false → Adjacent R a t →
    ∀ x ∈ Q R t, x ∉ Q R a →
      conjugatesIn (zpowers x) (stabilizer R a) ⊔ Q R t = stabilizer R a

/-- The predecessor of the far endpoint on the specified shortest path. -/
def Predecessor (a a' t : Vertex R) : Prop :=
  Adjacent R a' t ∧
    (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a'

/-- A particular witness to source (c), with the printed Frattini premise. -/
structure CommutatorWitness (a a' : Vertex R) (W : Subgroup (FreeAmalgam R)) : Prop where
  le_X : W ≤ X R a'
  not_le_Q : ¬ W ≤ Q R a
  bound : ∀ t, Predecessor R a a' t →
    ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Q R t →
      frattini ↥(Y ⊔ X R a) = ⊥ →
      ⁅Y, W⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅Y, X R a' ⊓ Q R a⁆

/-- Source (c) for every actual critical pair. -/
def CommutatorControl (geometry : Geometry R) : Prop :=
  ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
      ∃ W, CommutatorWitness R a a' W

/-- Source (d), for one subgroup attached to one oriented edge. -/
structure EdgeWitness (geometry : Geometry R) (a t : Vertex R)
    (A : Subgroup (FreeAmalgam R)) : Prop where
  le_X : A ≤ X R a
  normal_edge : (A.subgroupOf (Q R t)).Normal
  not_normal_vertex : ¬ (A.subgroupOf (stabilizer R a)).Normal
  critical_bound : ∀ (ha : color R a = false) d,
    CriticalPair R a d (geometry.exists_critical a ha) →
    (cosetGraph R).dist t d + 1 = geometry.b R → A ≤ ⁅X R a, X R d⁆

variable [Finite M]

/-- All subgroups under discussion remain inside finite local stabilizers. -/
theorem finite_of_le_stabilizer {A : Subgroup (FreeAmalgam R)} {a : Vertex R}
    (hA : A ≤ stabilizer R a) : Finite A := by
  let := finite_stabilizer R a
  exact Finite.of_injective (inclusion hA) (inclusion_injective hA)

/-- A holomorph kernel on an edge is contained in its M-stabilizer. -/
theorem edge_le_stabilizer {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : Q R t ≤ stabilizer R a := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  rw [Q_h_eq_edge R ht hat]
  exact inf_le_left

/-- The X-layer of an M-vertex is contained in any adjacent holomorph kernel. -/
theorem X_le_edge {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) : X R a ≤ Q R t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  exact (omegaCenter_le _).trans (Q_le_adjacent_h R ht hat)

/-- The explicit X-containment in (d) gives the needed edge containment. -/
theorem EdgeWitness.le_edge {geometry : Geometry R} {a t : Vertex R}
    {A : Subgroup (FreeAmalgam R)} (hA : EdgeWitness R geometry a t A)
    (ha : color R a = false) (hat : Adjacent R a t) : A ≤ Q R t :=
  hA.le_X.trans (X_le_edge R ha hat)

/-- Trivial Frattini and elementary abelianness agree under the actual finite
two-group containment. The source premise itself is not replaced by this lemma. -/
theorem frattini_join_eq_bot_iff {L : Subgroup M} (source : LocalSource L R)
    {a : Vertex R} (ha : color R a = false)
    {Y : Subgroup (FreeAmalgam R)} (hY : Y ≤ Q R a) :
    frattini ↥(Y ⊔ X R a) = ⊥ ↔ IsElementaryAbelian 2 ↥(Y ⊔ X R a) := by
  have hjoin : Y ⊔ X R a ≤ Q R a := sup_le hY (omegaCenter_le _)
  let := finite_of_le_stabilizer R (hjoin.trans (fun _ hx => hx.1))
  let : Fact (IsPGroup 2 ↥(Y ⊔ X R a)) := ⟨
    (Q_isPGroup R source.two_group source.core_le a ha).of_injective
      (inclusion hjoin) (inclusion_injective hjoin)⟩
  exact frattini_eq_bot_iff_isElementaryAbelian (p := 2)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
