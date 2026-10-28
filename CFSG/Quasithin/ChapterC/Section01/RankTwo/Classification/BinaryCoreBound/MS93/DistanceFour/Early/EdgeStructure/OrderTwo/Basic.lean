module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Basic
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The source hypotheses in the order-two edge branch

Edge transitivity propagates the order-two assumption to every edge. A
nontrivial critical commutator contained in such an edge commutator must
equal it. This proves the universal critical-pair containment in MS93
(2.3)(d), and also proves (c), with the literal witness Z at the far endpoint,
even without its elementary-join restriction on Y.

The edge commutator is normal in the edge kernel. It is not normal in the
M-vertex stabilizer: a normal group of order two would be central there,
contradicting the absence of fixed points in the actual natural subgroup U.
These are hypotheses for the application of (2.3), not its conclusion or
the completed exclusion. All finiteness used below is local.

Source: Meierfrankenfeld--Stellmacher (1993), (2.3), pp.857--859,
and the order-two branch of (4.6.5), p.903.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conjugacy of actual edges makes their displacement orders equal. -/
theorem edge_card_eq (a b c d : Vertex R)
    (ha : color R a = false) (hc : color R c = false)
    (hab : Adjacent R a b) (hcd : Adjacent R c d) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) =
      Nat.card (⁅Z R c, Q R d⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨g, hg | hg⟩ := edge_transitive R hab hcd
  · rw [← hg.1, ← hg.2, Z_act, Q_act, ← map_commutator]
    exact (card_map_of_injective (MulAut.conj g⁻¹).injective).symm
  · have hcol : color R d = false := by
      rw [← hg.1, action_preserves_color]
      exact ha
    exact (adjacent_color_ne R hcd (hc.trans hcol.symm)).elim

variable [Finite M] (common : CommonFacts R source geometry)

omit [Finite M] in
/-- This is relative normality in T_beta, as required by (2.3)(d). -/
theorem edge_normal_in_kernel (a b : Vertex R) (hab : Adjacent R a b) :
    ((⁅Z R a, Q R b⁆).subgroupOf (Q R b)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized R a (hg.2 a (adjacent_symm R hab))),
    mem_normalizer_iff_map_conj_eq.mp ((Q R b).le_normalizer hg)]

include common

/-- An order-two displacement group cannot be normal in G_alpha. -/
theorem edge_not_normal_in_stabilizer (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ¬ ((⁅Z R a, Q R b⁆).subgroupOf (stabilizer R a)).Normal := by
  intro hn
  let A := ⁅Z R a, Q R b⁆
  have hAU : A ≤ U R a := edge_commutator_le_natural common a b ha hab
  have hAG : A ≤ stabilizer R a :=
    hAU.trans ((DistanceEight.U_le_Z R a).trans (Z_le_stabilizer R a))
  let : (A.subgroupOf (stabilizer R a)).Normal := hn
  have hcard' : Nat.card (A.subgroupOf (stabilizer R a)) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAG).toEquiv]
    exact hcard
  have hc := central_of_normal_card_two (A.subgroupOf (stabilizer R a)) hcard'
  have hAC : A ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    intro x hx l hl
    exact congrArg Subtype.val ((mem_center_iff.mp
      (hc (show (⟨x, hAG hx⟩ : stabilizer R a) ∈ A.subgroupOf (stabilizer R a) from hx)))
        ⟨l, (map_subtype_le (pResidual 2 (stabilizer R a))) hl⟩)
  apply edge_commutator_ne_bot common a b ha hab
  exact le_bot_iff.mp ((le_inf hAU hAC).trans (Flags.U_fixed_eq_bot common a ha).le)

/-- Every critical pair through this edge has exactly its order-two displacement.
In particular the containment in (2.3)(d) holds for every such pair. -/
theorem critical_commutator_eq_edge (a b a' : Vertex R) (ha : color R a = false)
    (_hab : Adjacent R a b)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha))
    (hpath : (cosetGraph R).dist b a' + 1 = (cosetGraph R).dist a a')
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅Z R a, Z R a'⁆ = ⁅Z R a, Q R b⁆ := by
  have ha' := critical_endpoint_color R a ha _ hcrit
  have hZ : Z R a' ≤ Q R b := by
    apply Z_le_Q_of_dist_lt R a' (geometry.exists_critical a' ha')
    rw [geometry.distance_constant a' ha', ← geometry.distance_constant a ha,
      SimpleGraph.dist_comm]
    have hd := hcrit.1
    omega
  have hle := commutator_mono (le_refl (Z R a)) hZ
  let A := ⁅Z R a, Q R b⁆
  let : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Finite (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective hle)
  have hnontriv : 1 < Nat.card (⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) :=
    (one_lt_card_iff_ne_bot _).mpr (common.critical_noncommutation a ha a' hcrit)
  exact eq_of_le_of_card_ge hle (by omega)

/-- The witness Z(a,a') = Z_a' satisfies (2.3)(c). In the order-two
branch the whole predecessor kernel has this stronger commutator bound. -/
theorem critical_predecessor_commutator_le (a₀ b₀ : Vertex R)
    (ha₀ : color R a₀ = false)
    (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (a a' : Vertex R) (ha : color R a = false)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (hpath : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a')
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t) :
    ⁅Y, Z R a'⁆ ≤ ⁅Z R a, Z R a'⁆ := by
  have ha' := critical_endpoint_color R a ha _ hcrit
  have hrev := common.critical_reverse a ha a' ha' hcrit
  have hc : Nat.card (⁅Z R a', Q R t⁆ : Subgroup (FreeAmalgam R)) = 2 :=
    (edge_card_eq a₀ b₀ a' t ha₀ ha' he₀ hat).symm.trans hcard
  have he := critical_commutator_eq_edge common a' t a ha' hat hrev
    (by simpa only [SimpleGraph.dist_comm] using hpath) hc
  rw [commutator_comm Y, commutator_comm (Z R a), he]
  exact commutator_mono le_rfl hY

/-- Clause (2.3)(c), including its actual far-endpoint witness and escape. -/
theorem critical_witness_bound (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false)
    (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (a a' : Vertex R) (ha : color R a = false)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Z R a' ≤ X R a' ∧ ¬ Z R a' ≤ Q R a ∧
      ∀ t, Adjacent R a' t →
        (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a' →
        ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Q R t →
          ⁅Y, Z R a'⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅Y, X R a' ⊓ Q R a⁆ := by
  have ha' := critical_endpoint_color R a ha _ hcrit
  refine ⟨(common.X_eq_Z a' ha').ge,
    (common.critical_reverse a ha a' ha' hcrit).2, ?_⟩
  intro t hat hpath Y hY
  rw [common.X_eq_Z a ha, common.X_eq_Z a' ha']
  exact (critical_predecessor_commutator_le common a₀ b₀ ha₀ he₀ hcard
    a a' ha hcrit t hat hpath Y hY).trans le_sup_left

/-- All four parts of (2.3)(d) for the literal edge commutator. -/
theorem edge_source_d (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅Z R a, Q R b⁆ ≤ X R a ∧
      ((⁅Z R a, Q R b⁆).subgroupOf (Q R b)).Normal ∧
      ¬ ((⁅Z R a, Q R b⁆).subgroupOf (stabilizer R a)).Normal ∧
      ∀ a', CriticalPair R a a' (geometry.exists_critical a ha) →
        (cosetGraph R).dist b a' + 1 = (cosetGraph R).dist a a' →
          ⁅Z R a, Q R b⁆ ≤ ⁅X R a, X R a'⁆ := by
  refine ⟨?_, edge_normal_in_kernel a b hab,
    edge_not_normal_in_stabilizer common a b ha hab hcard, ?_⟩
  · rw [common.X_eq_Z a ha]
    exact (edge_commutator_le_natural common a b ha hab).trans (DistanceEight.U_le_Z R a)
  · intro a' hcrit hpath
    rw [common.X_eq_Z a ha,
      common.X_eq_Z a' (critical_endpoint_color R a ha _ hcrit),
      critical_commutator_eq_edge common a b a' ha hab hcrit hpath hcard]


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo
