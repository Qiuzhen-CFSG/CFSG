module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SpecialUnitaryEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.ActorData

/-!
# Original unitary quotient markings on the reduced DGS graph

Both projective and full special-unitary markings, in every fixed-field
degree at least two, identify the actual graph actor with the original
starred parabolic. Quotient equivalences retain the original local-to-starred
map on every representative. In the special form the full scalar center
remains in the target. The ambient completion may be infinite.

Original conjugation supplies these models at every graph vertex. The
literal Chapter 7 consumer discharges its enlarged-model premise from
these markings. Its general 6.5 obstruction remains explicit, and neither
degree-one unitary case is asserted here.

Source: DGS, Groups and Graphs (1985), reduction p.95, 6.1 pp.118--119,
and 7.1--7.5 pp.126--131; Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem borel_core_sylow (h : HypothesisF11 L S) :
    ∃ T : Sylow 2 (commonBorel L (SuzukiContainment.reducedSylow L S)),
      (T : Subgroup (commonBorel L (SuzukiContainment.reducedSylow L S))) =
        pCore 2 (commonBorel L (SuzukiContainment.reducedSylow L S)) := by
  apply f11_borel_core_sylow (SuzukiContainment.reduced_hypothesis h)
  exact (normal_subgroupOf_iff_le_normalizer
    (show SuzukiContainment.reducedSylow L S ≤ commonBorel L (SuzukiContainment.reducedSylow L S)
      from le_sup_right)).mp (SuzukiContainment.reduced_sylow_normal h)

/-- The actual source enlargement equals the original starred endpoint in
all projective-unitary degrees at least two. -/
theorem reduced_enlargedEndpoint_eq_starred_of_projective_unitary
    (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L i ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have he := localEnlargement_eq_star_of_projective_unitary (hh.starredLocalRankOneData i)
    (borel_core_sylow h) J hn hcard hconj ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i] at he
  exact he.trans (SuzukiContainment.reduced_starredParabolic h i)

/-- The intrinsic graph actor embeds onto the original starred subgroup. -/
def reduced_projectiveUnitaryActorEquiv (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      family (starredParabolic L S) i := by
  have he : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
      (G₀ L S).subtype = family (starredParabolic L S) i := by
    rw [reduced_graphLocalGroup_image h]
    cases i
    · exact reduced_enlargedEndpoint_eq_starred_of_projective_unitary h 0 J hn hcard hconj e
    · exact reduced_enlargedEndpoint_eq_starred_of_projective_unitary h 1 J hn hcard hconj e
  exact ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr he)

/-- The actor map is the original completion inclusion on every element. -/
theorem reduced_projectiveUnitaryActorEquiv_coe (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    (reduced_projectiveUnitaryActorEquiv h i J hn hcard hconj e x : G) = (x : G₀ L S) := by rfl

/-- The actual core quotient retains the original unitary marking. -/
def reduced_graphProjectiveUnitaryQuotient (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
        ProjectiveSpecialUnitaryMatrixGroup J :=
  (QuotientGroup.congr _ _ (reduced_projectiveUnitaryActorEquiv h i J hn hcard hconj e)
    (pCore_map_iso 2 _)).trans ((originalStarredQuotientEquiv h i).symm.trans e)

/-- The quotient formula keeps the original starred inclusion on representatives. -/
theorem reduced_graphProjectiveUnitaryQuotient_mk (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    reduced_graphProjectiveUnitaryQuotient h i J hn hcard hconj e (QuotientGroup.mk x) =
      e ((originalStarredQuotientEquiv h i).symm
        (QuotientGroup.mk (reduced_projectiveUnitaryActorEquiv h i J hn hcard hconj e x))) := by rfl

/-- The original projective-unitary marking supplies the Chapter 6 actor model. -/
theorem reduced_graph_projectiveUnitary_rankOne (h : HypothesisF11 L S) (i : Bool)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  exact .projective_unitary n (by omega) ⟨F,hF,hfin,J,hcard,hconj,
    ⟨reduced_graphProjectiveUnitaryQuotient h i J hn hcard hconj e⟩⟩

/-- Every graph vertex receives its actual unitary quotient model by original conjugation. -/
theorem reduced_projectiveUnitary_actor_models (h : HypothesisF11 L S)
    (hm : ∀ i : Bool, ∃ n, 2 ≤ n ∧
      ClassicalGroup.IsPSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n))
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let A := graphLocalGroup F (base F v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v := by
    exact (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  obtain ⟨n,hn,he⟩ := hm v.type
  exact (reduced_graph_projectiveUnitary_rankOne h v.type hn he).of_equiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

/-- Actual application to the Chapter 7 distance theorem: the unitary
markings discharge its enlarged-model premise. General 6.5 remains explicit. -/
theorem reduced_projectiveUnitary_noncommuting_distance_bound (h : HypothesisF11 L S)
    (hm : ∀ i : Bool, ∃ n, 2 ≤ n ∧
      ClassicalGroup.IsPSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n))
    (hob : ∀ x y, (graph (reducedFamily L S)).Adj x y →
      ¬ stabilizer (reducedFamily L S) y ≤ normalizer
        ((Q (reducedFamily L S) x ⊓ Q (reducedFamily L S) y : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v) (Z (reducedFamily L S) v)
      (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w) (Z (reducedFamily L S) w)
      (Q (reducedFamily L S) w) :=
  Noncommuting.Reduction.reduced_distance_bound_of_actor_models h
    (reduced_projectiveUnitary_actor_models h hm) hob hc hne

/-- The actual source enlargement equals the original starred endpoint in
all special-unitary degrees at least two. -/
theorem reduced_enlargedEndpoint_eq_starred_of_special_unitary
    (h : HypothesisF11 L S) (i : Fin 2)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (L i ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    enlargedEndpoint L S i = starredParabolic L S i := by
  let hh := SuzukiContainment.reduced_hypothesis h
  have he := localEnlargement_eq_star_of_special_unitary (hh.starredLocalRankOneData i)
    (borel_core_sylow h) J hn hcard hconj ((hh.starredQuotientEquiv i).symm.trans e)
  rw [reduced_localEnlargement_eq h i] at he
  exact he.trans (SuzukiContainment.reduced_starredParabolic h i)

/-- The intrinsic graph actor embeds onto the original starred subgroup. -/
def reduced_specialUnitaryActorEquiv (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* J.specialSubgroup) :
    graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      family (starredParabolic L S) i := by
  have he : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).map
      (G₀ L S).subtype = family (starredParabolic L S) i := by
    rw [reduced_graphLocalGroup_image h]
    cases i
    · exact reduced_enlargedEndpoint_eq_starred_of_special_unitary h 0 J hn hcard hconj e
    · exact reduced_enlargedEndpoint_eq_starred_of_special_unitary h 1 J hn hcard hconj e
  exact ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective).trans (MulEquiv.subgroupCongr he)

/-- The actor map is the original completion inclusion on every element. -/
theorem reduced_specialUnitaryActorEquiv_coe (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* J.specialSubgroup)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    (reduced_specialUnitaryActorEquiv h i J hn hcard hconj e x : G) = (x : G₀ L S) := by rfl

/-- The actual core quotient retains the original unitary marking. -/
def reduced_graphSpecialUnitaryQuotient (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* J.specialSubgroup) :
    (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃*
        J.specialSubgroup :=
  (QuotientGroup.congr _ _ (reduced_specialUnitaryActorEquiv h i J hn hcard hconj e)
    (pCore_map_iso 2 _)).trans ((originalStarredQuotientEquiv h i).symm.trans e)

/-- The quotient formula keeps the original starred inclusion on representatives. -/
theorem reduced_graphSpecialUnitaryQuotient_mk (h : HypothesisF11 L S) (i : Bool)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* J.specialSubgroup)
    (x : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i)) :
    reduced_graphSpecialUnitaryQuotient h i J hn hcard hconj e (QuotientGroup.mk x) =
      e ((originalStarredQuotientEquiv h i).symm
        (QuotientGroup.mk (reduced_specialUnitaryActorEquiv h i J hn hcard hconj e x))) := by rfl

/-- The original special-unitary marking supplies the Chapter 6 actor model. -/
theorem reduced_graph_specialUnitary_rankOne (h : HypothesisF11 L S) (i : Bool)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : IsSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  exact .special_unitary n (by omega) ⟨F,hF,hfin,J,hcard,hconj,
    ⟨reduced_graphSpecialUnitaryQuotient h i J hn hcard hconj e⟩⟩


/-- Every graph vertex receives its actual special or projective unitary quotient model by original conjugation. -/
theorem reduced_unitary_actor_models (h : HypothesisF11 L S)
    (hm : ∀ i : Bool, ∃ n, 2 ≤ n ∧
      (ClassicalGroup.IsPSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n) ∨
        IsSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n)))
    (v : Vertex (reducedFamily L S)) :
    IsRankOneModel (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) := by
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let A := graphLocalGroup F (base F v.type)
  have heq : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v := by
    exact (graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let a : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr heq)
  obtain ⟨n,hn,he⟩ := hm v.type
  have hm0 : IsRankOneModel (A ⧸ pCore 2 A) := by
    rcases he with hp | hs
    · exact reduced_graph_projectiveUnitary_rankOne h v.type hn hp
    · exact reduced_graph_specialUnitary_rankOne h v.type hn hs
  exact hm0.of_equiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm

/-- Actual application to the Chapter 7 distance theorem: the unitary
markings discharge its enlarged-model premise. General 6.5 remains explicit. -/
theorem reduced_unitary_noncommuting_distance_bound (h : HypothesisF11 L S)
    (hm : ∀ i : Bool, ∃ n, 2 ≤ n ∧
      (ClassicalGroup.IsPSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n) ∨
        IsSU (family L i ⧸ pCore 2 (family L i)) 3 (2^n)))
    (hob : ∀ x y, (graph (reducedFamily L S)).Adj x y →
      ¬ stabilizer (reducedFamily L S) y ≤ normalizer
        ((Q (reducedFamily L S) x ⊓ Q (reducedFamily L S) y : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {v w : Vertex (reducedFamily L S)} (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥) :
    (b (reducedFamily L S) = 1 ∨ b (reducedFamily L S) = 2) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) v) (Z (reducedFamily L S) v)
      (Q (reducedFamily L S) v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup (reducedFamily L S) w) (Z (reducedFamily L S) w)
      (Q (reducedFamily L S) w) :=
  Noncommuting.Reduction.reduced_distance_bound_of_actor_models h
    (reduced_unitary_actor_models h hm) hob hc hne


end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
