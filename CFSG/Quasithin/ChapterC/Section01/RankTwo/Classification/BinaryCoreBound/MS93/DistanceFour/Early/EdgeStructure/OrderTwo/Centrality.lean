module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Basic

/-!
# From the critical-path normality to the fixed derived subgroup

An order-two edge commutator normal in the midpoint stabilizer is central
there. A critical commutator through that edge equals it. Among any two
M-vertex layers generating the radius group, either the layers commute,
or their vertices form a critical pair with the original vertex as midpoint.
Thus centrality of the critical commutators extends to the whole derived
subgroup by subgroup generation. This proves its containment in the actual
fixed core D_alpha, as used on p.903.

The normality furnished by MS93 (2.3) remains explicit here; this module
does not assert that application without its source hypotheses.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.5), p.903.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common

/-- Relative normality from (2.3) gives literal midpoint centrality. -/
theorem critical_midpoint_central (hb : geometry.b R = 4)
    (a b a' c : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hcb : Adjacent R c b)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha))
    (hac : (cosetGraph R).dist a c = 2) (hca' : (cosetGraph R).dist c a' = 2)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2)
    (hn : ((⁅Z R a, Q R b⁆).subgroupOf (stabilizer R c)).Normal) :
    ⁅Z R a, Z R a'⁆ ≤ centralizer (stabilizer R c : Set (FreeAmalgam R)) := by
  have hdist : (cosetGraph R).dist a a' = 4 := by
    rw [hcrit.1, geometry.distance_constant a ha]
    exact hb
  have hpath : (cosetGraph R).dist b a' + 1 = (cosetGraph R).dist a a' := by
    have hbc : (cosetGraph R).dist b c = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hcb))
    have habd : (cosetGraph R).dist a b = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hab)
    have htri := (cosetGraph_connected R).dist_triangle (u := b) (v := c) (w := a')
    have htri' := (cosetGraph_connected R).dist_triangle (u := a) (v := b) (w := a')
    omega
  rw [critical_commutator_eq_edge common a b a' ha hab hcrit hpath hcard]
  let A := ⁅Z R a, Q R b⁆
  have hZa : Z R a ≤ Q R c := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha]
    change (cosetGraph R).dist a c < geometry.b R
    omega
  have hAG : A ≤ stabilizer R c :=
    ((edge_commutator_le_natural common a b ha hab).trans
      (DistanceEight.U_le_Z R a)).trans (hZa.trans (fun _ hx => hx.1))
  let : (A.subgroupOf (stabilizer R c)).Normal := hn
  have hc := central_of_normal_card_two (A.subgroupOf (stabilizer R c))
    ((Nat.card_congr (subgroupOfEquivOfLe hAG).toEquiv).trans hcard)
  intro x hx g hg
  exact congrArg Subtype.val ((mem_center_iff.mp
    (hc (show (⟨x, hAG hx⟩ : stabilizer R c) ∈ A.subgroupOf (stabilizer R c) from hx)))
      ⟨g, hg⟩)

omit [Finite M] common in
private theorem radius_le_of_m_layers (a : Vertex R) (ha : color R a = false)
    (D : Subgroup (FreeAmalgam R))
    (hD : ∀ c, color R c = false → (cosetGraph R).dist c a ≤ 2 → Z R c ≤ D) :
    V R a ≤ D := by
  apply iSup_le
  intro c
  apply iSup_le
  intro hc
  by_cases hcol : color R c = false
  · exact hD c hcol hc
  · have hcol' : color R c = true := by cases hh : color R c <;> simp_all
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist c a
    have hnEven : ¬ Even p.length := by
      rw [walk_even_iff_color_eq, hcol', ha]
      decide
    have hlen : p.length = 1 := by
      have hle : p.length ≤ 2 := hp.trans_le hc
      rw [Nat.even_iff] at hnEven
      omega
    have hadj : Adjacent R a c :=
      adjacent_symm R ((cosetGraph_adj R _ _).mp (p.adj_of_length_eq_one hlen))
    exact (edge_Z_le a c ha hadj).trans (hD a ha (by simp))

omit [Finite M] common in
private theorem commutator_join_le {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Y D : Subgroup G)
    (hn : (⨆ i, A i) ≤ normalizer (D : Set G)) (hc : ∀ i, ⁅A i, Y⁆ ≤ D) :
    ⁅⨆ i, A i, Y⁆ ≤ D := by
  apply commutator_le.mpr
  intro x hx y hy
  revert y
  induction hx using iSup_induction' with
  | hp i x hx =>
      intro y hy
      exact hc i (commutator_mem_commutator hx hy)
  | h1 =>
      intro y hy
      simpa only [commutatorElement_one_left] using D.one_mem
  | hmul x z hx _ ihx ihz =>
      intro y hy
      rw [commutatorElement_mul_left_eq_conj_mul]
      exact D.mul_mem ((mem_normalizer_iff.mp (hn hx) _).mp (ihz y hy)) (ihx y hy)

omit [Finite M] in
/-- The generation argument immediately following (2.3) on p.903. Only
centrality for critical pairs having a as midpoint is needed. -/
theorem derived_le_fixedCore_of_critical_midpoints (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hcentral : ∀ c d (hc : color R c = false),
      CriticalPair R c d (geometry.exists_critical c hc) →
      (cosetGraph R).dist c a = 2 → (cosetGraph R).dist a d = 2 →
        ⁅Z R c, Z R d⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    ⁅V R a, V R a⁆ ≤ fixedCore R a := by
  let I := {c : Vertex R // color R c = false ∧ (cosetGraph R).dist c a ≤ 2}
  let A : I → Subgroup (FreeAmalgam R) := fun c => Z R c.val
  have hV : V R a = ⨆ c, A c := by
    apply le_antisymm
    · apply radius_le_of_m_layers a ha
      intro c hc hca
      exact le_iSup A ⟨c, hc, hca⟩
    · apply iSup_le
      intro c
      exact le_iSup_of_le c.val (le_iSup_of_le c.property.2 le_rfl)
  have hn : (⨆ c, A c) ≤
      normalizer (centralizer (stabilizer R a : Set (FreeAmalgam R))) := by
    rw [← hV]
    exact ((radius_le_Q common a ha).trans (fun _ hx => hx.1)).trans
      ((le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _))
  have hpair (c d : I) : ⁅A c, A d⁆ ≤
      centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    change ⁅Z R c.val, Z R d.val⁆ ≤ _
    by_cases hle : Z R c.val ≤ Q R d.val
    · have hz := commutator_mono hle (le_refl (Z R d.val))
      rw [commutator_comm (Q R d.val), geometry.centralizes d.val d.property.1] at hz
      exact hz.trans bot_le
    · have hd' : (cosetGraph R).dist a d.val ≤ 2 := by
        simpa only [SimpleGraph.dist_comm] using d.property.2
      have hupper := (cosetGraph_connected R).dist_triangle (u := c.val) (v := a) (w := d.val)
      have hlower := criticalDistance_le R c.val (geometry.exists_critical c.val c.property.1) hle
      rw [geometry.distance_constant c.val c.property.1] at hlower
      change geometry.b R ≤ _ at hlower
      have hdist : (cosetGraph R).dist c.val d.val = 4 := by have := c.property.2; omega
      have hcrit : CriticalPair R c.val d.val (geometry.exists_critical c.val c.property.1) := by
        refine ⟨?_, hle⟩
        rw [geometry.distance_constant c.val c.property.1]
        exact hdist.trans hb.symm
      exact hcentral c.val d.val c.property.1 hcrit
        (by have := c.property.2; omega) (by have := c.property.2; omega)
  have hderived : ⁅V R a, V R a⁆ ≤
      centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    rw [hV]
    apply commutator_join_le _ _ _ hn
    intro c
    rw [commutator_comm]
    exact commutator_join_le _ _ _ hn (fun d => hpair d c)
  exact le_inf ((commutator_le_self (V R a)).trans (radius_le_Q common a ha))
    (hderived.trans (centralizer_le (map_subtype_le (pResidual 2 (stabilizer R a)))))

/-- Applying the critical-path normality conclusion uniformly supplies the
fixed-derived premise needed by the final offender argument. -/
theorem derived_le_fixedCore_of_critical_edge_normality (hb : geometry.b R = 4)
    (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false) (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (hnormal : ∀ c d (hc : color R c = false),
      CriticalPair R c d (geometry.exists_critical c hc) →
      ∀ b a, Adjacent R c b → Adjacent R a b →
        (cosetGraph R).dist c a = 2 → (cosetGraph R).dist a d = 2 →
          ((⁅Z R c, Q R b⁆).subgroupOf (stabilizer R a)).Normal)
    (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, V R a⁆ ≤ fixedCore R a := by
  apply derived_le_fixedCore_of_critical_midpoints common hb a ha
  intro c d hc hcrit hca had
  obtain ⟨b, hcb, hab⟩ := exists_common_neighbor_of_dist_two R c a hca
  have hcard' : Nat.card (⁅Z R c, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2 :=
    (edge_card_eq a₀ b₀ c b ha₀ hc he₀ hcb).symm.trans hcard
  exact critical_midpoint_central common hb c b d a hc hcb hab hcrit hca had hcard'
    (hnormal c d hc hcrit b a hcb hab hca had)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo
