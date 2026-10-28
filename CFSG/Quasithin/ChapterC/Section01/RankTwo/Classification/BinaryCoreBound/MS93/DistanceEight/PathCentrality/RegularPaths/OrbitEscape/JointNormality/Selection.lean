module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Selection.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.OrbitGrowth.LocalAction

/-!
# The two separating edge conjugates in MS93 (4.4.2)

The critical endpoint acts nontrivially on the actual natural eight-group at
the start. Its compatible matrix image therefore moves a vector. The binary
geometry construction chooses two translates of the edge commutator which
are moved by this actor and whose common intersection with its fixed space
is trivial. Both possible edge orders, two and four, are included.

Lift the two matrices through the same local quotient and invert the lifts
to obtain the source's right conjugators. Covariance identifies each moved
edge with an actual adjacent vertex. Maximality of its relative normalizer
then gives both generation equations. Equivariance of the natural marking
identifies the fixed space with the literal centralizer in U_a and reflects
the threefold intersection back to the amalgam.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), first paragraph on printed p.893. This discharges exactly
SeparatingConjugates from JointNormality/Reduction.lean. The parent retains
the applications of (4.4.1) and final joint-normality assembly.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
open NormalizerTransfer
open Escape.Propagation.Backward.Products.Selection.Choices
open Escape.Propagation.Backward.Products.Selection.Choices.FiniteGeometry
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The two source right conjugates, with both generation equations and the
literal centralizer intersection. CommonFacts already suffices for selection. -/
theorem separatingConjugates [Finite M] {source : LocalSource L R}
    (common : CommonFacts R source geometry) {a a' : Vertex R}
    (p : CriticalPath R geometry a a') : SeparatingConjugates p := by
  classical
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) a p.start_color
  have hl := p.length_eq_b
  have hb := common.large_distance
  have hadj : Adjacent R a (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero, Nat.zero_add] using
      (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  let E := edgeCommutator R a (p.walk.getVert 1)
  let A := Z R a'
  have hA : A ≤ stabilizer R a :=
    (source.critical_Z_le_stabilizer geometry a p.start_color a' p.critical).2
  have hE : E ≤ U R a := Escape.EdgeTransfer.edge_commutator_le_natural
    hb (moduleFacts common) a _ p.start_color hadj
  have hsmall := Escape.EdgeTransfer.edge_displacement_card_le_four hb
    (moduleFacts common) a _ p.start_color hadj
  have hne := Escape.EdgeTransfer.edge_commutator_ne_bot
    (moduleFacts common) a _ p.start_color hadj
  have hcard : Nat.card E = 2 ∨ Nat.card E = 4 := by
    have hdiv := card_dvd_of_le hE
    rw [common.natural.card_at a p.start_color] at hdiv
    have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
    rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hh
    have hone : Nat.card E ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    change Nat.card E ≤ 4 at hsmall
    change Nat.card E = 1 ∨ Nat.card E = 2 ∨ Nat.card E = 4 ∨ Nat.card E = 8 at hh
    omega
  have hmoved : ∃ s ∈ model.actorImage A, ∃ v : Space, modelAction s v ≠ v := by
    by_contra! hn
    have hc : U R a ≤ centralizer (A : Set (FreeAmalgam R)) := by
      intro u hu z hz
      apply (model.action_fixed_iff ⟨z, hA hz⟩ ⟨u, hu⟩).mp
      exact hn _ (mem_map_of_mem model.projection hz) _
    apply common.critical_noncommutation a p.start_color a' p.critical
    rw [(naturalStructure common).critical_commutator_eq geometry a p.start_color a' p.critical]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hc.trans (centralizer_le (U_le_Z R a')))
  obtain ⟨s, t, hs, ht, hsep⟩ := Selection.BinaryGeometry.exists_separating_translates
    (model.coordinates E) (by rwa [model.coordinates_card E hE]) (model.actorImage A) hmoved
  obtain ⟨g, rfl⟩ := model.surjective s
  obtain ⟨h, rfl⟩ := model.surjective t
  have hconjU (x : stabilizer R a) :
      E.map (MulAut.conj (x : FreeAmalgam R)).toMonoidHom ≤ U R a :=
    (map_mono hE).trans (mem_normalizer_iff_map_conj_eq.mp (U_normalized a x.property)).le
  have hnot (x : stabilizer R a)
      (hn : ¬ model.actorImage A ≤ planeStabilizer (move (model.projection x) (model.coordinates E))) :
      ¬ A ≤ stabilizer R a ⊓ normalizer (E.map (MulAut.conj (x : FreeAmalgam R)).toMonoidHom) := by
    intro hnA
    apply hn
    rintro _ ⟨z, hz, rfl⟩
    change move (model.projection z) (move (model.projection x) (model.coordinates E)) = _
    simp only [move]
    rw [← model.coordinates_conjugate x E hE,
      ← model.coordinates_conjugate z _ (hconjU x)]
    exact congrArg model.coordinates (mem_normalizer_iff_map_conj_eq.mp (hnA hz).2)
  have hP (x : stabilizer R a) :
      rightConjugate (relativeP p) (x : FreeAmalgam R)⁻¹ =
        stabilizer R a ⊓ normalizer (E.map (MulAut.conj (x : FreeAmalgam R)).toMonoidHom) := by
    rw [rightConjugate, inv_inv, relativeP,
      Subgroup.map_inf _ _ _ (MulAut.conj (x : FreeAmalgam R)).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj (x : FreeAmalgam R)).bijective]
    have he : (stabilizer R a).map (MulAut.conj (x : FreeAmalgam R)).toMonoidHom =
        stabilizer R a := mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer R a).le_normalizer x.property)
    rw [he]
  have hgen (x : stabilizer R a)
      (hn : ¬ model.actorImage A ≤ planeStabilizer (move (model.projection x) (model.coordinates E))) :
      rightConjugate (relativeP p) (x : FreeAmalgam R)⁻¹ ⊔ A = stabilizer R a := by
    have hfix : act R (x : FreeAmalgam R)⁻¹ a = a := (stabilizer R a).inv_mem x.property
    have he : E.map (MulAut.conj (x : FreeAmalgam R)).toMonoidHom =
        edgeCommutator R a (act R (x : FreeAmalgam R)⁻¹ (p.walk.getVert 1)) := by
      have hh := edgeCommutator_act (x : FreeAmalgam R)⁻¹ a (p.walk.getVert 1)
      simpa only [hfix, inv_inv] using hh.symm
    rw [hP x, he]
    apply CommutatorPropagation.Seed.OrbitGrowth.edge_normalizer_sup_eq common p.start_color
      (by simpa only [hfix] using
        (adjacent_act_iff R (x : FreeAmalgam R)⁻¹ a (p.walk.getVert 1)).mpr hadj) hA
    simpa only [he] using hnot x hn
  refine ⟨(g : FreeAmalgam R)⁻¹, (stabilizer R a).inv_mem g.property,
    (h : FreeAmalgam R)⁻¹, (stabilizer R a).inv_mem h.property, hgen g hs, hgen h ht, ?_⟩
  change (E.map (MulAut.conj (g : FreeAmalgam R)⁻¹⁻¹).toMonoidHom ⊓
    E.map (MulAut.conj (h : FreeAmalgam R)⁻¹⁻¹).toMonoidHom) ⊓
    (U R a ⊓ centralizer (A : Set (FreeAmalgam R))) = ⊥
  simp only [inv_inv]
  apply model.coordinates_injective (inf_le_left.trans (inf_le_left.trans (hconjU g))) bot_le
  rw [model.coordinates_inf, model.coordinates_inf,
    model.coordinates_conjugate g E hE, model.coordinates_conjugate h E hE,
    ← model.fixedSpace_actorImage A hA]
  simpa only [LocalModel.coordinates, bot_subgroupOf, Subgroup.map_bot] using hsep

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.JointNormality
