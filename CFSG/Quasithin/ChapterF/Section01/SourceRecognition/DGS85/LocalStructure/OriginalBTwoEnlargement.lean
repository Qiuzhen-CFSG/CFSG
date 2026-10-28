module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSmallUnitaryExclusionSource

/-!
# The original beta enlargement on the distance-two source branch

The constructed natural action and proved central middle vertex supply
all earlier premises of the original beta-selection theorem. Both small
unitary alternatives, including the strict projective enlargement, are
therefore excluded on this exact source branch. The original beta quotient
is linear, and conjugation transports the two actual endpoint markings
to every intrinsic actor in the reduced graph.

The same construction applies the existing saturation theorem to the
literal original alpha core and D subgroup, retaining the full Borel and
all inclusion maps. The assumption b=2 is essential here; this does not
prove unrestricted 6.1 or the remaining long same-orbit distance bound.
Source: DGS, Groups and Graphs (1985), 6.1, pp.118--119,
7.4, p.128, and 10.6--10.9, pp.158--163.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true

private theorem bTwo_base_adj : (graph F).Adj α β :=
  ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩

private theorem bTwo_other_neighbor (h : HypothesisF11 L S)
    {u : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥) :
    ∃ t : Vertex F, (graph F).Adj α t ∧ t ≠ β := by
  obtain ⟨d,_⟩ := reduced_critical_actor_localData h hc hne bTwo_base_adj
  dsimp only [reducedFamily] at d
  obtain ⟨g,hg,hng⟩ := SetLike.exists_of_lt (source_borel_lt d)
  have hfix : g • α = α := hg
  refine ⟨g • β,?_,?_⟩
  · have he : (graph F).Adj (g • α) (g • β) :=
      (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr bTwo_base_adj
    simpa only [hfix] using he
  · intro he
    exact hng ⟨hg,he⟩

/-- The original beta quotient is linear on the actual distance-two branch.
No enlarged-model, centrality, radius-commutator or obstruction premise remains. -/
theorem original_bTwo_beta_linear (h : HypothesisF11 L S)
    {u : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) := by
  obtain ⟨k,f,n,ch,a,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb bTwo_base_adj hβu
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  obtain ⟨t,ht,htne⟩ := bTwo_other_neighbor h hc hne
  exact NoncommutingProfile.Reduction.original_bTwo_beta_linear h hb c hactor
    (reduced_bTwo_middle_central h hc hne hb bTwo_base_adj hβu) ht htne
    (reduced_bTwo_center_identities h hc hne hb bTwo_base_adj hβu).2.2.2
    (reduced_graph_core_obstruction h α β bTwo_base_adj) (LinearEquiv.refl _ _)

/-- The literal original beta enlargement is unchanged on this source
branch, so the strict PSU₃(2) alternative has been discharged here. -/
theorem original_bTwo_beta_enlargement_eq_starred (h : HypothesisF11 L S)
    {u : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    enlargedEndpoint L S 1 = starredParabolic L S 1 := by
  obtain ⟨n,hn,K,hK,hfin,hcard,⟨e⟩⟩ := original_bTwo_beta_linear h hc hne hb hβu
  let := hK
  let := hfin
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact reduced_enlargedEndpoint_eq_starred_of_linear h 1 e

/-- The critical alpha marking and the original beta quotient give all
graph actor models on this source branch. -/
theorem original_bTwo_actor_models (h : HypothesisF11 L S)
    {u : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) (x : Vertex F) :
    IsRankOneModel (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) := by
  have hα : IsRankOneModel (graphLocalGroup F α ⧸ pCore 2 (graphLocalGroup F α)) := by
    obtain ⟨n,hn,hm⟩ := (reduced_critical_actor_quotients_linear h hc hne).1
    exact .linear n hn hm
  have hβ : IsRankOneModel (graphLocalGroup F β ⧸ pCore 2 (graphLocalGroup F β)) := by
    obtain ⟨n,hn,K,hK,hfin,hcard,⟨e⟩⟩ := original_bTwo_beta_linear h hc hne hb hβu
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact .linear n hn ⟨K,hK,hfin,hcard,⟨reduced_graphLinearQuotient h true e⟩⟩
  have hbase (i : Bool) : IsRankOneModel
      (graphLocalGroup F (base F i) ⧸ pCore 2 (graphLocalGroup F (base F i))) := by
    cases i
    · exact hα
    · exact hβ
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F x
  let A := graphLocalGroup F (base F x.type)
  have he : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F x :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F x.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let e : A ≃* graphLocalGroup F x :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr he)
  exact (hbase x.type).of_equiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

/-- Apply the original core-field consumer with all its earlier geometric
premises discharged, retaining the supplied opposite neighbor and full Borel. -/
theorem original_bTwo_central_core_field (h : HypothesisF11 L S)
    {u t : Vertex F} (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F α β u k (Fin 2 → k),
      c.actor = graphLocalGroup F α ∧
      enlargedEndpoint L S 1 = starredParabolic L S 1 ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype
      ∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n) ∧
        (∃ r : ℕ, 0 < r ∧ 2^n = Nat.card k ^ r) ∧
        (centralSeed F α β t).map (G₀ L S).subtype = Q₀ ∧
        P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
        ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
          IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
          Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^n)^2 := by
  obtain ⟨k,f,n,ch,a,c,hactor⟩ := Noncommuting.Reduction.reduced_bTwo_center_action_exists h
    (original_bTwo_actor_models h hc hne hb hβu) hc hne hb bTwo_base_adj hβu
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  refine ⟨k,f,n,ch,inferInstance,c,hactor,
    original_bTwo_beta_enlargement_eq_starred h hc hne hb hβu,?_⟩
  exact NoncommutingProfile.Reduction.original_bTwo_central_core_field h hb c hactor
    (reduced_bTwo_middle_central h hc hne hb bTwo_base_adj hβu) ht htne
    (reduced_bTwo_center_identities h hc hne hb bTwo_base_adj hβu).2.2.2
    (reduced_graph_core_obstruction h α β bTwo_base_adj) (LinearEquiv.refl _ _)

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
