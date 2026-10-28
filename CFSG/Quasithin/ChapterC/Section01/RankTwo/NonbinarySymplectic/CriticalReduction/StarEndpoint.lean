module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedAction

/-!
# The escaping seed's vertex layer cannot fix the critical endpoint

The endpoint intersection normalizes the actual full-Sylow seed through
its common edge. If the seed's whole vertex layer fixed the endpoint, it
would normalize that intersection and make its action quadratic. The full
intersection then has centralizer index both at least q and at most n,
contrary to n < 2ⁿ. This excludes the noncritical penultimate branch in the
first symplectic star comparison without any field-four restriction.

Source: MS93 (3.4), printed p.868. The critical penultimate branch remains
the separate local commutator comparison.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full Z-layer of an escaping source-star seed does not stabilize the
critical endpoint. Its fixed seed itself still lies in that stabilizer. -/
theorem Input.replacement_star_seed_not_endpoint_stabilizer
    (geometry : Geometry d.radical) (hfour : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P₀ : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P₀)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {u t : Vertex d.radical} (hu : color d.radical u = false)
    (hat : Adjacent d.radical (alpha d.radical) t) (hut : Adjacent d.radical u t)
    (P : Sylow 2 (Ltilde d.radical u))
    (hnP : Q d.radical t ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)))
    (hs : componentSylowSeed d.radical u P ≤ sourceStarAlpha d.radical Y)
    (he : ¬ Z d.radical z ≤ normalizer
      ((componentSylowSeed d.radical u P ⊔ Z d.radical (alpha d.radical) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ¬ Z d.radical u ≤ stabilizer d.radical z := by
  intro hUZ
  have hb : 0 < geometry.b d.radical := by omega
  let E := Z d.radical z ⊓ Q d.radical (alpha d.radical)
  have hdist : (cosetGraph d.radical).dist u (alpha d.radical) ≤ 2 := by
    have hu1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hut)
    have ha1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hat)
    have hta1 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 := by
      rwa [SimpleGraph.dist_comm]
    have htri := (cosetGraph_connected d.radical).dist_triangle
      (u := u) (v := t) (w := alpha d.radical)
    omega
  have hUQ : Z d.radical u ≤ Q d.radical (alpha d.radical) :=
    Z_le_Q_of_dist_lt d.radical u (geometry.exists_critical u hu) (by
      rw [geometry.distance_constant u hu]
      change (cosetGraph d.radical).dist u (alpha d.radical) < geometry.b d.radical
      omega)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases hh' : color d.radical t <;> simp_all
  have hEQ : E ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hEU : E ≤ stabilizer d.radical u := hEQ.trans (fun _ hx => hx.2 u (adjacent_symm _ hut))
  have hEN : E ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)) :=
    hEQ.trans hnP
  have hUN : Z d.radical u ≤ normalizer (E : Set (FreeAmalgam d.radical)) :=
    (le_inf (hUZ.trans (Z_normalized d.radical z))
      (hUQ.trans (Q d.radical (alpha d.radical)).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hcomm : ⁅E,U d.radical u⁆ ≤ E := by
    apply le_normalizer_iff_commutator_le_left.mp
    exact (U_le_Z u).trans hUN
  let : IsElementaryAbelian 2 (Z d.radical z) := geometry.Z_elementary hb z path.end_color
  have hEE : E ≤ centralizer (E : Set (FreeAmalgam d.radical)) :=
    inf_le_left.trans ((Z d.radical z).le_centralizer.trans (centralizer_le inf_le_left))
  have hquad : ⁅⁅E,U d.radical u⁆,E⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hcomm.trans hEE)
  have hYS := hs.trans (h.replacement_sourceStarAlpha_le_critical_endpoint_stabilizer
    d geometry hb path Y P₀ hY hn)
  have hYQ := hs.trans (h.replacement_sourceStarAlpha_le_own_core d geometry hb Y P₀ hY hn)
  have hmove : ¬ E ≤ centralizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)) := by
    intro hfix
    have hlo := h.replacement_seed_actor_centralizer_index_ge_field d path hb
      (componentSylowSeed d.radical u P) hYS hYQ he
      (componentSylowSeed d.radical u P) le_rfl hYS
    have hi := relIndex_eq_one.mpr hfix
    change (centralizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z ⊓ Q d.radical (alpha d.radical)) = 1 at hi
    rw [hi,h.field_card] at hlo
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) h.nonbinary
    omega
  have hup := h.replacement_moving_seed_actor_index_le_degree d hu P E hEU hEN hmove hquad
  have hlo := h.replacement_sourceStar_seed_index_ge_field d geometry hb path Y P₀ hY hn u P hs hUZ he
  rw [h.field_card] at hlo
  change (centralizer (Z d.radical u : Set (FreeAmalgam d.radical))).relIndex
    (Z d.radical z ⊓ Q d.radical (alpha d.radical)) ≤ n at hup
  have hlt := n.lt_two_pow_self
  omega


/-- The noncritical penultimate branch is excluded for the actual selected
seed. The remaining pair is critical at the literal vertex on the path. -/
theorem Input.replacement_star_seed_critical_at_penultimate
    (geometry : Geometry d.radical) (hfour : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P₀ : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P₀)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {u t : Vertex d.radical} (hu : color d.radical u = false)
    (hat : Adjacent d.radical (alpha d.radical) t) (hut : Adjacent d.radical u t)
    (P : Sylow 2 (Ltilde d.radical u))
    (hnP : Q d.radical t ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)))
    (hs : componentSylowSeed d.radical u P ≤ sourceStarAlpha d.radical Y)
    (he : ¬ Z d.radical z ≤ normalizer
      ((componentSylowSeed d.radical u P ⊔ Z d.radical (alpha d.radical) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    CriticalPair d.radical u (path.walk.getVert (path.walk.length - 2))
      (geometry.exists_critical u hu) := by
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hfour
  let c := path.walk.getVert (path.walk.length - 2)
  let v := path.walk.getVert (path.walk.length - 1)
  have hcv : Adjacent d.radical c v := by
    have hh := path.walk.adj_getVert_succ (i := path.walk.length - 2) (by omega)
    have hi : path.walk.length - 2 + 1 = path.walk.length - 1 := by omega
    rw [hi] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hvz : Adjacent d.radical v z := by
    have hh := path.walk.adj_getVert_succ (i := path.walk.length - 1) (by omega)
    have hi : path.walk.length - 1 + 1 = path.walk.length := by omega
    rw [hi,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hv : color d.radical v = true := by
    have hh := adjacent_color_ne d.radical hvz
    rw [path.end_color] at hh
    cases hcolor : color d.radical v <;> simp_all
  have hnQ : ¬ Z d.radical u ≤ Q d.radical c := by
    intro hc
    apply h.replacement_star_seed_not_endpoint_stabilizer d geometry hfour path Y P₀ hY hn
      hu hat hut P hnP hs he
    exact (hc.trans (Q_le_adjacent_h d.radical hv hcv)).trans (fun _ hx => hx.2 z hvz)
  have hdist : (cosetGraph d.radical).dist u (alpha d.radical) ≤ 2 := by
    have hu1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hut)
    have ha1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hat)
    have hta1 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 := by
      rwa [SimpleGraph.dist_comm]
    have htri := (cosetGraph_connected d.radical).dist_triangle
      (u := u) (v := t) (w := alpha d.radical)
    omega
  have hac : (cosetGraph d.radical).dist (alpha d.radical) c = path.walk.length - 2 :=
    path.dist_start (Nat.sub_le _ _)
  have htri := (cosetGraph_connected d.radical).dist_triangle
    (u := u) (v := alpha d.radical) (w := c)
  refine ⟨le_antisymm ?_ (criticalDistance_le d.radical u _ hnQ),hnQ⟩
  rw [geometry.distance_constant u hu]
  have hlength := path.length_eq_b
  change (cosetGraph d.radical).dist u c ≤ geometry.b d.radical
  omega


/-- An actual failure of the first star bound yields a second critical pair,
with the same transported full-Sylow seed and its movement retained. -/
theorem Input.replacement_bad_star_penultimate_seed
    (geometry : Geometry d.radical) (hfour : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P₀ : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P₀)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    (hbad : ¬ ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical)) :
    ∃ u t : Vertex d.radical, ∃ P : Sylow 2 (Ltilde d.radical u),
      ∃ hu : color d.radical u = false,
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical u t ∧
      Q d.radical t ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)) ∧
      componentSylowSeed d.radical u P ≤ sourceStarAlpha d.radical Y ∧
      ¬ Z d.radical z ≤ normalizer
        ((componentSylowSeed d.radical u P ⊔ Z d.radical (alpha d.radical) :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ¬ componentSylowSeed d.radical u P ≤ centralizer
        ((Z d.radical z ⊓ Q d.radical (alpha d.radical) :
          Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      CriticalPair d.radical u (path.walk.getVert (path.walk.length - 2))
        (geometry.exists_critical u hu) := by
  obtain ⟨u,t,P,hu,hat,hut,hnP,hs,he,hm⟩ :=
    h.replacement_bad_star_moving_seed d geometry (by omega) path Y P₀ hY hn hbad
  exact ⟨u,t,P,hu,hat,hut,hnP,hs,he,hm,
    h.replacement_star_seed_critical_at_penultimate d geometry hfour path Y P₀ hY hn
      hu hat hut P hnP hs he⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
