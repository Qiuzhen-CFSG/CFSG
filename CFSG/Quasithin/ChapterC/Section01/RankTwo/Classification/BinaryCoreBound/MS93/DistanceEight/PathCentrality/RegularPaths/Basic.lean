module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalAction

/-!
# The intermediate orbit-escape statements for regular critical paths

The first statement is the disjunction opening the proof of (4.4.2). The
second is the noncontainment of the P-orbit span used to prove (4.4.4), where
P is the normalizer of the forward edge commutator inside the local stabilizer.
Neither statement is asserted from the source inputs in this module.

The proved extraction lemma obtains the same element for the prescribed
edge-commutator conjugation and the endpoint noncontainment. It selects an
element of P before multiplying by the prescribed edge conjugator.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2) and (4.4.4), printed pp.892--894.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Turn conjugators at even vertices through the indicated initial segment. -/
def InitialTurns {a a' : Vertex R} (p : CriticalPath R geometry a a') (n : ℕ) : Prop :=
  ∀ i : ℕ, Even i → 2 ≤ i → i ≤ n → i + 2 ≤ p.walk.length →
    ∃ g ∈ stabilizer R (p.walk.getVert i),
      Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert (i + 2)) =
        p.walk.getVert (i - 2)

/-- The escape disjunction at the start of the proof of (4.4.2), p.892.
This is an intermediate target, not an assumed source theorem. -/
def OrbitEscapeAlternative {a a' : Vertex R} (p : CriticalPath R geometry a a') : Prop :=
  (¬ localZSpan R (p.walk.getVert 2) a ≤ Q R (p.walk.getVert (p.walk.length - 2))) ∨
    ∃ g ∈ stabilizer R a,
      ¬ localZSpan R a (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2)) ≤
        Q R (p.walk.getVert (p.walk.length - 4))

/-- Failure of containment for the generated span selects an actual orbit element. -/
theorem exists_conjugate_not_le {a c : Vertex R} {K : Subgroup (FreeAmalgam R)}
    (h : ¬ localZSpan R a c ≤ K) :
    ∃ g ∈ stabilizer R c, ¬ Z R (Stellmacher.PushingUp.AmalgamGraph.act R g a) ≤ K := by
  classical
  simpa only [localZSpan, iSup_le_iff, not_forall, Subtype.exists, exists_prop] using h

/-- Covariance uses the original right action and inverse conjugation. -/
theorem edgeCommutator_act (g : FreeAmalgam R) (a t : Vertex R) :
    edgeCommutator R (Stellmacher.PushingUp.AmalgamGraph.act R g a)
      (Stellmacher.PushingUp.AmalgamGraph.act R g t) =
      (edgeCommutator R a t).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [edgeCommutator, Z_act, Q_act, ← map_commutator]
  rfl

/-- Neighbor transitivity prescribes the image of the actual edge commutator. -/
theorem exists_edge_conjugator [Finite M] {a s t : Vertex R}
    (hs : Adjacent R a s) (ht : Adjacent R a t) :
    ∃ g ∈ stabilizer R a,
      (edgeCommutator R a s).map (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t := by
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R a hs ht
  refine ⟨g, hg, ?_⟩
  have hga : Stellmacher.PushingUp.AmalgamGraph.act R g a = a := hg
  rw [← edgeCommutator_act, hga, hgt]

/-- The actual P-orbit span used in the proof of (4.4.4), with P relative to G_a. -/
noncomputable def prescribedSpan {a a' : Vertex R} (p : CriticalPath R geometry a a') :
    Subgroup (FreeAmalgam R) :=
  ⨆ g : ↥(stabilizer R a ⊓ normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R))),
    Z R (Stellmacher.PushingUp.AmalgamGraph.act R g (p.walk.getVert 2))

/-- The subgroup noncontainment proved before choosing the final element in
(4.4.4). It is weaker than requiring each prescribed conjugator to work. -/
def PrescribedSpanEscape {a a' : Vertex R} (p : CriticalPath R geometry a a') : Prop :=
  ∀ t, Adjacent R a t →
    ¬ Z R a' ≤ stabilizer R a ⊓ normalizer (edgeCommutator R a t : Set (FreeAmalgam R)) →
    ∀ g ∈ stabilizer R a,
      (edgeCommutator R a (p.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom =
        edgeCommutator R a t →
      ¬ (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
        Q R (p.walk.getVert (p.walk.length - 2))

/-- Select an element of the relative normalizer orbit before the prescribed
conjugation. Their product gives both conclusions with the same conjugator. -/
theorem prescribedReplacement_of_spanEscape [Finite M] {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (hb : 0 < geometry.b R)
    (hspan : PrescribedSpanEscape p) : PrescribedReplacement R p := by
  intro t ht hn
  have hpnon : ¬ p.walk.Nil := by
    intro h
    have hz := h.length_eq_zero
    have hl := p.length_eq_b
    omega
  have hs := (cosetGraph_adj R _ _).mp (p.walk.adj_snd hpnon)
  obtain ⟨g, hg, hge⟩ := exists_edge_conjugator hs ht
  have he := hspan t ht hn g hg hge
  rw [prescribedSpan, Subgroup.map_iSup, iSup_le_iff] at he
  obtain ⟨u, hu⟩ := not_forall.mp he
  refine ⟨(u : FreeAmalgam R) * g, (stabilizer R a).mul_mem u.property.1 hg, ?_, ?_⟩
  · have huE := mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (edgeCommutator R a (p.walk.getVert 1) : Set (FreeAmalgam R))).inv_mem
        u.property.2)
    have huE' : (edgeCommutator R a (p.walk.getVert 1)).map
        (MulAut.conj (u : FreeAmalgam R)⁻¹).toMonoidHom =
          edgeCommutator R a (p.walk.getVert 1) := by
      simpa only [MulEquiv.toMonoidHom_eq_coe] using huE
    have hmaps : (MulAut.conj ((u : FreeAmalgam R) * g)⁻¹).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj (u : FreeAmalgam R)⁻¹).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc]
    rw [hmaps, ← Subgroup.map_map, huE', hge]
  · rw [← Z_act, act_mul, Z_act]
    exact hu


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths
