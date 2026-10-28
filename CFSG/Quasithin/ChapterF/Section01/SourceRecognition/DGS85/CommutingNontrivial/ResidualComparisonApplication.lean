module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PairedIndexGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.EscapeApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ResidualSource

/-!
# Literal residual actors for the paired Chapter 8 comparison

The two original residual quotients have nonzero vectors and zero residual
fixed space. Their opposite neighborhood actors are quadratic and have
orders exactly a₁ and a₂: the kernel on each actor is its intersection with
the original vertex core. Reciprocal escape supplies the opposite critical
orientation; the original 6.5(a) obstruction supplies both core escapes.

For a large unitary moving quotient the two original secondary indices
are bounded by its actual field order, and the printed products retain
their literal subgroup denominators. The remaining 8.3(2) proof must still
establish the residual-action square estimates and exclude the natural
alternative. Neither descent of the entire residual action nor those
estimates is asserted here.

Source: DGS, Groups and Graphs (1985), 8.3(2), pp.135--136.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.NormalElementaryQuotient BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CommutingTrivial
universe u
variable {G : Type u} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The whole residual section at the ending vertex, with its exact actor
kernel and order. The coordinate map, residual vanishing and quadraticity
are constructed on this section, without passing to a constituent. -/
theorem reduced_ending_residual_actor
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a') :
    let F := Reduction.reducedFamily J S₀
    let L := graphLocalGroup F a'
    let U := (V F a' 1).subgroupOf L
    let A := (V F beta 1).subgroupOf L
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F a' L (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 L
      let ρ := fixedQuotientAction U (pResidual 2 L)
      Nontrivial (FixedQuotient U (pResidual 2 L)) ∧
      Nonempty (BinaryConjugationSection L (V F a' 1)
        (V F a' 1 ⊓ centralizer ((pResidual 2 L).map L.subtype : Set (Reduction.G₀ J S₀))) ρ) ∧
      fixedSpace ρ (pResidual 2 L) = ⊥ ∧ IsQuadratic ρ A ∧
      A ⊓ ρ.ker = (V F beta 1 ⊓ Q F a').subgroupOf L ∧
      Nat.card (A.map ρ.asGroupHom) = (Q F a').relIndex (V F beta 1) := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  have hb3 : 3 ≤ b F := (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.1
  have hb2 : 2 < b F := by omega
  dsimp only
  refine ⟨hb2,?_⟩
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) a' hb2 L
  obtain ⟨⟨c⟩,hr,hquad⟩ := neighborhood_residual_section ht (Reduction.reduced_kernel_sylow h)
    a' hb2 L (core_le_graphLocalGroup ht a') (sylowGenerated_le _)
  let : Nontrivial (FixedQuotient U (pResidual 2 L)) := local_residual_section_nontrivial ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) w.property
      (fixedQuotientAction U (pResidual 2 L)) c
  have he := source_critical_residual_actor_kernel (W := FixedQuotient U (pResidual 2 L))
    ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w
    (core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm))
    (fixedQuotientAction U (pResidual 2 L)) c hr
  exact ⟨inferInstance,⟨c⟩,hr,hquad beta hd.le,he⟩

/-- Both printed actors are realized on the original full residual quotients.
The reverse critical pair is constructed using 8.2, so no reverse-escape
or reverse-commutation premise is added to the source contract. -/
theorem reduced_paired_residual_actor_orders
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥) :
    let F := Reduction.reducedFamily J S₀
    let L₁ := graphLocalGroup F a'
    let L₂ := graphLocalGroup F beta
    let U₁ := (V F a' 1).subgroupOf L₁
    let U₂ := (V F beta 1).subgroupOf L₂
    letI : ∀ i, Finite (F i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal F a' L₁ (sylowGenerated_le _)
    letI := neighborhoodIn_normal F beta L₂ (sylowGenerated_le _)
    ∃ hb2 : 2 < b F,
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) a' hb2 L₁
      letI := neighborhoodIn_elementary F (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 L₂
      Nat.card (((V F beta 1).subgroupOf L₁).map
        (fixedQuotientAction U₁ (pResidual 2 L₁)).asGroupHom) =
          (Q F a').relIndex (V F beta 1) ∧
      Nat.card (((V F a' 1).subgroupOf L₂).map
        (fixedQuotientAction U₂ (pResidual 2 L₂)).asGroupHom) =
          (Q F beta).relIndex (V F a' 1) := by
  obtain ⟨_,z,hz,hcz,hzd,hzc,_⟩ := reduced_reciprocal_critical_configuration h hob models
    hc hab hd hb hcomm hne
  obtain ⟨hb2,_,_,_,_,_,h₁⟩ := reduced_ending_residual_actor h hob models hc hab hd hb hcomm ⟨z,hz.symm⟩
  obtain ⟨_,_,_,_,_,_,h₂⟩ := reduced_ending_residual_actor h hob models hcz hz hzd hb hzc ⟨a,hab.symm⟩
  exact ⟨hb2,h₁,h₂⟩

private theorem unitary_quotient_rank_le {L : Type*} [Group L] [Finite L]
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2^n) ∨ IsSU (L ⧸ pCore 2 L) 3 (2^n)) :
    primeRank 2 (L ⧸ pCore 2 L) ≤ n := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le

/-- The actual unitary field supplies both secondary-index bounds in the
original reduced graph, including the full special-unitary scalar kernel. -/
theorem reduced_unitary_paired_core_indices
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^n)) :
    let F := Reduction.reducedFamily J S₀
    (Q F a').relIndex (V F beta 1) * (Q F w.val).relIndex (V F beta 1 ⊓ Q F a') =
      (Q F w.val).relIndex (V F beta 1) ∧
    (Q F beta).relIndex (V F a' 1) * (Q F a).relIndex (V F a' 1 ⊓ Q F beta) =
      (Q F a).relIndex (V F a' 1) ∧
    (Q F w.val).relIndex (V F beta 1 ⊓ Q F a') ≤ 2^n ∧
    (Q F a).relIndex (V F a' 1 ⊓ Q F beta) ≤ 2^n := by
  let : ∀ i, Finite (Reduction.reducedFamily J S₀ i) := finite_endpoints (Reduction.reduced_triple h)
  let : Finite (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact source_paired_core_indices (Reduction.reduced_triple h) (Reduction.reduced_borel_core_sylow h)
    (Reduction.reducedEarlierLocalTheorems h hob) hc hab hd hb hcomm models w hm n
    (unitary_quotient_rank_le (L := graphLocalGroup (Reduction.reducedFamily J S₀) w.val) hn hu)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
