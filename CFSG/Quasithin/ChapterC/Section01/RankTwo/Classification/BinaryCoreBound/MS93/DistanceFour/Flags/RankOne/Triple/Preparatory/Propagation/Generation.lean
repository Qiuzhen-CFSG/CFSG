module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Escape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Detection

/-!
# Generation from a transported crossing commutator

The edge index two turns a commutator outside Z_alpha into the displayed
identity for Z_t. The same noncontainment, combined with the seed bound,
forces the transported Z-layer to escape Q_alpha. This proves the terminal
group-theoretic step without assuming the displayed identity or Z_t ≤ V₀.

The non-single-section hypothesis supplies an escaping conjugate through
the complete marked natural-section recognition. The geometric actor
index bound then lets commutator detection produce the required crossing.
`transportedGenerator` assembles these proofs into one actual ordered-pair
transport and the displayed identity, with no extra representation premise.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

namespace Generation

private theorem supplement_of_index_le_two {G : Type*} [Group G]
    (A K P : Subgroup G) (hA : A ≤ P) (hK : K ≤ P)
    (hindex : A.relIndex P ≤ 2) (hnzero : A.relIndex P ≠ 0)
    (hcross : ¬ K ≤ A) : K ⊔ A = P := by
  have hle : K ⊔ A ≤ P := sup_le hK hA
  have hmul := relIndex_mul_relIndex A (K ⊔ A) P le_sup_right hle
  have hne : A.relIndex (K ⊔ A) ≠ 1 := by
    intro h
    exact hcross (le_sup_left.trans (relIndex_eq_one.mp h))
  have ha : 2 ≤ A.relIndex (K ⊔ A) := by
    have hz : A.relIndex (K ⊔ A) ≠ 0 := by intro h; rw [h, zero_mul] at hmul; exact hnzero hmul.symm
    omega
  have hb : 1 ≤ (K ⊔ A).relIndex P := by
    have hz : (K ⊔ A).relIndex P ≠ 0 := by intro h; rw [h, mul_zero] at hmul; exact hnzero hmul.symm
    omega
  have he : (K ⊔ A).relIndex P = 1 := by nlinarith
  exact le_antisymm hle (relIndex_eq_one.mp he)

/-- An actual transported midpoint with nonzero displacement modulo Z_alpha
has exactly the displayed source generation identity. -/
theorem generation_of_crossing [Finite M] (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i) (t lam : Vertex R)
    (ht : nu R geometry (alpha R) t)
    (hd : (cosetGraph R).dist lam t = 2)
    (hcross : ¬ ⁅Z R lam, midpointSpan p ⊓ Q R t⁆ ≤ Z R (alpha R)) :
    Z R t = ⁅Z R lam, midpointSpan p ⊓ Q R t⁆ ⊔ (Z R t ⊓ Z R (alpha R)) := by
  have htc := color_of_distance_two (alpha R) t rfl ht.1
  have hK : ⁅Z R lam, midpointSpan p ⊓ Q R t⁆ ≤ Z R t :=
    (commutator_mono (show Z R lam ≤ V R t from
      le_iSup_of_le lam (le_iSup_of_le hd.le le_rfl)) inf_le_right).trans
      (early.commutator_le_Z t htc)
  let := finite_stabilizer R t
  let : Finite (Z R t) := Finite.of_injective (inclusion (Z_le_stabilizer R t))
    (inclusion_injective _)
  apply Eq.symm
  apply supplement_of_index_le_two _ _ _ inf_le_left hK
  · rw [inf_relIndex_left]
    exact intersection_index_le_two early (alpha R) t rfl ht.1
  · exact ((Z R t ⊓ Z R (alpha R)).subgroupOf (Z R t)).index_ne_zero_of_finite
  · exact fun h => hcross (h.trans inf_le_right)

/-- Nonzero displacement modulo Z_alpha forces the literal escape from Q_alpha. -/
theorem escapes_of_crossing (common : CommonFacts R source geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (t lam : Vertex R)
    (hcross : ¬ ⁅Z R lam, midpointSpan p ⊓ Q R t⁆ ≤ Z R (alpha R)) :
    ¬ Z R lam ≤ Q R (alpha R) := by
  intro h
  apply hcross
  rw [commutator_comm]
  exact (commutator_mono inf_le_left h).trans
    ((span_commutator_le_U common p hseed).trans (U_le_Z (alpha R)))

end Generation

/-- The full witness follows from one actual ordered-pair transport whose
commutator crosses Z_alpha. No displayed generation identity is an input. -/
theorem transportedGenerator_of_crossing [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (g : FreeAmalgam R) (hg : act R g (alpha R) = t)
    (hcross : ¬ ⁅Z R (act R g p.middle), midpointSpan p ⊓ Q R t⁆ ≤ Z R (alpha R)) :
    Nonempty (TransportedGenerator p t) :=
  ⟨{
    lam := act R g p.middle
    conjugator := g
    base_image := hg
    middle_image := rfl
    escapes := Generation.escapes_of_crossing common p hseed t _ hcross
    generation := Generation.generation_of_crossing early p t _ ht
      (Generation.transported_distance p g t hg) hcross }⟩

/-- Conditional assembly of the transported-vertex branch. The two explicit
representation premises still have to be proved from the non-single-section
condition; this is not the unconditional source result. -/
theorem transportedGenerator_of_escape_and_detection [Finite M]
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (hbad : ¬ ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hescape : ∃ g : FreeAmalgam R, act R g (alpha R) = t ∧
      ¬ Z R (act R g p.middle) ≤ Q R (alpha R))
    (hdetect : ∀ g : FreeAmalgam R, act R g (alpha R) = t →
      ¬ Z R (act R g p.middle) ≤ Q R (alpha R) →
      (Q R t).relIndex (midpointSpan p) ≤ 2 →
      ¬ ⁅Z R (act R g p.middle), midpointSpan p ⊓ Q R t⁆ ≤ Z R (alpha R)) :
    Nonempty (TransportedGenerator p t) := by
  obtain ⟨g, hg, he⟩ := hescape
  exact transportedGenerator_of_crossing common early p hseed t ht g hg
    (hdetect g hg he (Generation.span_actor_index_le_two common early p hseed t ht hbad))

/-- The transported-vertex branch of (4.6.8)(2): failure of the full split
natural-section condition yields one actual transport and the displayed
commutator generation. The flag kernel and naturality inputs are retained
from the source interface; this branch already follows from the common and
early facts and the critical configuration. -/
theorem transportedGenerator [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry)
    (_hkernel : flagKernel source i = Q R (beta R))
    (_natural : FlagNaturalSection source i)
    (p : FlagCriticalData source geometry i)
    (hseed : ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R))
    (hs : ¬ SingleSection p) (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (hbad : ¬ ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R)) :
    Nonempty (TransportedGenerator p t) := by
  exact transportedGenerator_of_escape_and_detection common early p hseed t ht hbad
    (Generation.escapingTransport common early p hs t ht)
    (Generation.transported_commutator_crosses common hb early p hs t ht)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation
