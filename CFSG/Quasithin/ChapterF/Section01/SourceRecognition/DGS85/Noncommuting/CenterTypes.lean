module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.LocalGeneration

/-!
# The two source center types

Conjugation transports equality of Z_delta with Omega_1(Z(L_delta)) along
an actual vertex orbit. Noncommutation and the literal local placement exclude
that equality at both critical endpoints. Thus the epsilon-one choice gives
the noncentral alternative at every vertex, discharging the use of (6.2)(c).
For epsilon two the critical endpoints lie in the same orbit, so b is even.

The local actors retain their actual conjugation maps and odd relative indices.
No natural-module or distance classification is assumed. The source application
is in `RadiusOneSource`.
Source: DGS, *Groups and Graphs* (1985), (7.0), (7.3), (7.4)(a), pp.126--128.
-/

public section
open Subgroup
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The central-center alternative has the same truth value throughout an
actual graph orbit, with the local actor transported by conjugation. -/
theorem graph_center_equality_of_type (h : LocallyRankOneTriple P B)
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    {v w : Vertex (family P)} (ht : v.type = w.type) :
    Z (family P) v = Stellmacher.omegaOneCenterAmbient (L v) ↔
      Z (family P) w = Stellmacher.omegaOneCenterAmbient (L w) := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  rw [Z_translate,hcov,Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective]
  exact (map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).eq_iff.symm

/-- A noncommuting center cannot be the omega-center of the local actor
containing the opposite center. -/
theorem center_ne_omega_of_noncommuting (L Z A : Subgroup G)
    (hAL : A ≤ L) (hne : ⁅Z,A⁆ ≠ ⊥) : Z ≠ Stellmacher.omegaOneCenterAmbient L := by
  intro he
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hz a ha
  rw [he] at hz
  exact (Stellmacher.mem_omegaOneCenterAmbient_iff L z).mp hz |>.2.2 a (hAL ha)

/-- In epsilon one, both orbit representatives are noncentral; hence the
actual (6.2)(c) Sylow-centralizer conclusion holds at every vertex. -/
theorem graph_sylow_centralizers_of_epsilonOne (h : LocallyRankOneTriple P B)
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v w u : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hu : Z (family P) u ≠ Stellmacher.omegaOneCenterAmbient (L u))
    (hother : Z (family P) w ≤ L v) (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥) :
    ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) := by
  have hv := center_ne_omega_of_noncommuting (L v) _ _ hother hne
  intro x
  apply (hdich x).resolve_right
  by_cases ht : v.type = x.type
  · exact fun hx => hv ((graph_center_equality_of_type h L hcov ht).mpr hx)
  · have huxt : u.type = x.type := by
      have hne := hvu.1
      cases hv : v.type <;> cases hu : u.type <;> cases hx : x.type <;> simp_all
    exact fun hx => hu ((graph_center_equality_of_type h L hcov huxt).mpr hx)

/-- DGS (7.4)(a): epsilon two forces conjugate critical endpoints and even b. -/
theorem graph_even_of_epsilonTwo (h : LocallyRankOneTriple P B)
    (L : Vertex (family P) → Subgroup G)
    (hcov : ∀ g x, L (g • x) = (L x).map (MulAut.conj g).toMonoidHom)
    {v w u : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hvu : (graph (family P)).Adj v u)
    (hu : Z (family P) u = Stellmacher.omegaOneCenterAmbient (L u))
    (hother : Z (family P) v ≤ L w) (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥) :
    (∃ g : G, g • v = w) ∧ Even (b (family P)) := by
  have hw := center_ne_omega_of_noncommuting (L w) _ _ hother
    (by rwa [commutator_comm])
  have htype : v.type = w.type := by
    by_contra ht
    have huw : u.type = w.type := by
      have hne := hvu.1
      cases hv : v.type <;> cases hu : u.type <;> cases hw : w.type <;> simp_all
    exact hw ((graph_center_equality_of_type h L hcov huw).mp hu)
  refine ⟨(same_orbit_iff (family P) v w).mpr htype,?_⟩
  rw [← hc.1]
  exact (even_dist_iff (family P) h.generate v w).mpr htype

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
