module
public import CFSG.Quasithin.ChapterF.Section08.Track

/-!
# The chosen critical geodesic in F.8

Starting with the actual critical vertex from F.7.9, local transitivity moves
the first edge of a shortest path to the standard edge. This preserves both
criticality and distance. Odd parity then orients the last edge and supplies
the source conjugator g_b, represented by inverse left translation.
The record below contains these choices only; its existence is proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.8.4 and the choice following F.8.5, printed pp.316–317.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Subgroup.CosetGeometry.RankTwo
open Subgroup.CosetGeometry (stabilizer_base translationGraphIso incident_base)
namespace CFSG.Quasithin.ChapterF.Section08.Setup
open Section07
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
namespace Hypothesis
variable (h : D.Hypothesis)

/-- The choices in F.8.4 and the oriented edge choice following F.8.5.
The element `g⁻¹` is the source right-action conjugator g_b. -/
structure CriticalPath where
  endpoint : Vertex (family (D := D))
  distance : (graph (family (D := D))).dist (base (family (D := D)) false) endpoint = h.b
  critical : ¬ h.f7Setup.seed ≤ ballKernel (family (D := D)) endpoint 1
  path : (graph (family (D := D))).Walk (base (family (D := D)) false) endpoint
  shortest : path.length = (graph (family (D := D))).dist (base (family (D := D)) false) endpoint
  first : path.getVert 1 = base (family (D := D)) true
  g : (D.LT ⊔ D.H : Subgroup G)
  penultimate_eq : g • base (family (D := D)) false = path.getVert (path.length - 1)
  endpoint_eq : g • base (family (D := D)) true = endpoint

omit [Group G] [Finite G] in
private theorem getVert_copy {X : Type*} {Γ : SimpleGraph X} {a b c d : X}
    (p : Γ.Walk a b) (ha : a = c) (hb : b = d) (n : ℕ) :
    (p.copy ha hb).getVert n = p.getVert n := by subst c; subst d; rfl

/-- The normalized critical geodesic and its oriented edge representative exist. -/
theorem exists_criticalPath : Nonempty h.CriticalPath := by
  let F := family (D := D)
  let S := h.f7Setup
  obtain ⟨v, hd, hc⟩ := (S.critical_witness h.f7V_ne_bot).1
  obtain ⟨p, hp⟩ := (connected F S.generates).exists_walk_length_eq_dist (base F false) v
  have hlen : p.length = h.b := hp.trans hd
  have hpos : 0 < p.length := by have := h.one_lt_b; omega
  have hadj : (graph F).Adj (base F false) (p.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using p.adj_getVert_succ (i := 0) hpos
  have hedge : (graph F).Adj (base F false) (base F true) :=
    ⟨Bool.false_ne_true, incident_base F false true⟩
  obtain ⟨a, ha, hfirst⟩ := locally_transitive F hadj hedge
  have hfix : a • base F false = base F false := ha
  have haF : a ∈ F false := by
    rwa [show stabilizer F (base F false) = F false from stabilizer_base F false] at ha
  have hseed : S.seed.map (MulAut.conj a).toMonoidHom = S.seed :=
    mem_normalizer_iff_map_conj_eq.mp (S.seed_normalized haF)
  let φ : (graph F) →g (graph F) :=
    { toFun := fun x => a • x
      map_rel' := fun hab => (translationGraphIso F a).map_rel_iff.mpr hab }
  let q : (graph F).Walk (base F false) (a • v) :=
    (p.map φ).copy (show φ (base F false) = base F false from hfix) rfl
  have hq : q.length = (graph F).dist (base F false) (a • v) := by
    dsimp only [q]
    rw [SimpleGraph.Walk.length_copy]
    rw [SimpleGraph.Walk.length_map, hp]
    have hh := dist_smul F a (base F false) v
    exact (by simpa only [hfix] using hh.symm)
  have hqd : (graph F).dist (base F false) (a • v) = h.b := by
    have hh := dist_smul F a (base F false) v
    rw [hfix] at hh
    exact hh.trans hd
  have hqfirst : q.getVert 1 = base F true := by
    dsimp only [q]
    rw [getVert_copy, SimpleGraph.Walk.getVert_map]
    exact hfirst
  have hcrit : ¬ S.seed ≤ ballKernel F (a • v) 1 := by
    intro hh
    have hm := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hh
    rw [← ballKernel_translate, inv_smul_smul] at hm
    have hi : S.seed.map (MulAut.conj a⁻¹).toMonoidHom = S.seed :=
      mem_normalizer_iff_map_conj_eq.mp (S.seed_normalized ((F false).inv_mem haF))
    exact hc (hi ▸ hm)
  have hv : (a • v).type = true :=
    CriticalPairs.odd_endpoint_type F S h.f7V_ne_bot hqd h.odd_b
  obtain ⟨hpen, _, _, _⟩ := CriticalPairs.geodesic_internal_segments F S
    h.f7V_ne_bot hqd h.lemma_F_8_5.1 q hq hqfirst
  have hpt : (q.getVert (q.length - 1)).type = false := by
    have hh := hpen.1
    rw [hv] at hh
    cases ht : (q.getVert (q.length - 1)).type <;> simp_all
  obtain ⟨g, hg₀, hg₁⟩ := incident_common_translate F hpen.2
  rw [hpt] at hg₀
  rw [hv] at hg₁
  exact ⟨{
    endpoint := a • v
    distance := hqd
    critical := hcrit
    path := q
    shortest := hq
    first := hqfirst
    g := g
    penultimate_eq := hg₀
    endpoint_eq := hg₁ }⟩

end Hypothesis

end CFSG.Quasithin.ChapterF.Section08.Setup
