module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.DihedralApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySourceApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReorientedConfiguration

/-!
# Original binary quotients from the intrinsic graph markings

The original local quotient embeds in the actual full-Borel-core
enlargement quotient because their embedded two-cores have the original
intersection. A rank-one group embedded in SL₂(2) must fill it: every
proper subgroup has prime order or is trivial, contradicting the proved
proper Sylow normalizer. Thus a binary intrinsic graph marking gives the
original quotient marking, with its original inclusion formula retained.

Conjugation carries the two adjacent markings to both vertex orbits.
Applying the existing binary full-parabolic theorem then gives the original
full endpoints, unchanged completion and all graph stabilizers. The two
source fields remain independent; only their orders are compared.
The numerical field-two conclusion itself is supplied by source 9.10.

Source: DGS, *Groups and Graphs* (1985), 6.1, 9.10 and 13.1,
pp.118--119,147--150,191; Aschbacher--Smith F.1.9, pp.261--262.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Reduction Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem rankOne_binary_embedding_surjective {X : Type*} [Group X]
    (hm : IsRankOneModel X) (f : X →* SL(2,ZMod 2)) (hf : Function.Injective f) :
    Function.Surjective f := by
  let : Finite X := hm.finite
  have h6 : Nat.card SL(2,ZMod 2) = 6 := by
    rw [Nat.card_congr SLTwoPermThree.sl2Two_equiv_perm_three.some.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hd : Nat.card X ∈ (6 : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨h6 ▸ card_dvd_of_injective f hf,by decide⟩
  have hc : Nat.card X = 1 ∨ Nat.card X = 2 ∨ Nat.card X = 3 ∨ Nat.card X = 6 := by
    have hdiv : (6 : ℕ).divisors = {1,2,3,6} := by decide
    rw [hdiv] at hd
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hd
  have hnc (hc : IsMulCommutative X) : False := by
    let := hc
    let T : Sylow 2 X := Sylow.nonempty.some
    exact (hm.rankOneSylowFacts T).proper.ne (Subgroup.normalizer_eq_top _)
  have hx6 : Nat.card X = 6 := by
    rcases hc with hc | hc | hc | hc
    · have : Nat.card X ∣ 2 := by rw [hc]; exact one_dvd _
      exact (hnc (isCyclic_of_card_dvd_prime (p := 2) this).isMulCommutative).elim
    · exact (hnc (isCyclic_of_prime_card (p := 2) hc).isMulCommutative).elim
    · exact (hnc (isCyclic_of_prime_card (p := 3) hc).isMulCommutative).elim
    · exact hc
  exact (hf.bijective_of_nat_card_le (by omega)).surjective

private def localToEnlargement (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) :
    L i →* (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) :=
  (QuotientGroup.mk' _).comp
    (inclusion ((local_le_starredParabolic i).trans (show starredParabolic L S i ≤ enlargedEndpoint L S i from le_sup_left)))

private theorem localToEnlargement_ker (h : HypothesisF11 L S) (i : Fin 2) :
    (localToEnlargement L S i).ker = pCore 2 (L i) := by
  have hc : ((enlargedEndpoint L S i).pCoreIn 2).subgroupOf (L i) = pCore 2 (L i) := by
    apply map_injective (L i).subtype_injective
    rw [subgroupOf_map_subtype,enlargedEndpoint_core h i,inf_comm]
    exact h.local_inf_parabolic_core i
  rw [←hc]
  ext x
  change QuotientGroup.mk (inclusion ((local_le_starredParabolic i).trans
      (show starredParabolic L S i ≤ enlargedEndpoint L S i from le_sup_left)) x) =
      (1 : enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) ↔
    (x : G) ∈ (enlargedEndpoint L S i).pCoreIn 2
  rw [QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem (f := (enlargedEndpoint L S i).subtype)
    (enlargedEndpoint L S i).subtype_injective).symm

private def localQuotientEnlargementEmbedding (h : HypothesisF11 L S) (i : Fin 2) :
    (L i ⧸ pCore 2 (L i)) →*
      (enlargedEndpoint L S i ⧸ pCore 2 (enlargedEndpoint L S i)) :=
  (localToEnlargement L S i).range.subtype.comp
    (((QuotientGroup.quotientMulEquivOfEq (localToEnlargement_ker h i).symm).trans
      (QuotientGroup.quotientKerEquivRange (localToEnlargement L S i))).toMonoidHom)

private theorem localQuotientEnlargementEmbedding_injective (h : HypothesisF11 L S) (i : Fin 2) :
    Function.Injective (localQuotientEnlargementEmbedding h i) :=
  (localToEnlargement L S i).range.subtype_injective.comp
    (((QuotientGroup.quotientMulEquivOfEq (localToEnlargement_ker h i).symm).trans
      (QuotientGroup.quotientKerEquivRange (localToEnlargement L S i))).injective)

private def graphBaseBinaryOriginalMap (h : HypothesisF11 L S) (i : Bool)
    (e : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃* SL(2,ZMod 2)) :
    (family L i ⧸ pCore 2 (family L i)) →* SL(2,ZMod 2) := by
  cases i
  · exact e.toMonoidHom.comp ((reduced_graphEnlargementQuotient h false).symm.toMonoidHom.comp
      (localQuotientEnlargementEmbedding h 0))
  · exact e.toMonoidHom.comp ((reduced_graphEnlargementQuotient h true).symm.toMonoidHom.comp
      (localQuotientEnlargementEmbedding h 1))

private theorem graphBaseBinaryOriginalMap_injective (h : HypothesisF11 L S) (i : Bool)
    (e : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃* SL(2,ZMod 2)) :
    Function.Injective (graphBaseBinaryOriginalMap h i e) := by
  cases i
  · exact e.injective.comp ((reduced_graphEnlargementQuotient h false).symm.injective.comp
      (localQuotientEnlargementEmbedding_injective h 0))
  · exact e.injective.comp ((reduced_graphEnlargementQuotient h true).symm.injective.comp
      (localQuotientEnlargementEmbedding_injective h 1))

private theorem graphEnlargementQuotient_symm_mk (h : HypothesisF11 L S) (i : Bool)
    (y : family (enlargedEndpoint L S) i) :
    (reduced_graphEnlargementQuotient h i).symm (QuotientGroup.mk y) =
      QuotientGroup.mk ((reduced_enlargementActorEquiv h i).symm y) := by
  apply (reduced_graphEnlargementQuotient h i).injective
  rw [MulEquiv.apply_symm_apply,reduced_graphEnlargementQuotient_mk,MulEquiv.apply_symm_apply]

/-- The actual graph binary marking pulls back along the original local inclusion.
Its surjectivity uses the original rank-one Sylow facts. -/
theorem graph_base_binary_original_quotient (h : HypothesisF11 L S) (i : Bool)
    (e : (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i))) ≃* SL(2,ZMod 2)) :
    ∃ f : (family L i ⧸ pCore 2 (family L i)) ≃* SL(2,ZMod 2),
      ∀ x : family L i, f (QuotientGroup.mk x) =
        e (QuotientGroup.mk ((reduced_enlargementActorEquiv h i).symm
          (inclusion (show family L i ≤ family (enlargedEndpoint L S) i from by
            cases i <;> exact (local_le_starredParabolic _).trans le_sup_left) x))) := by
  have hm : IsRankOneModel (family L i ⧸ pCore 2 (family L i)) := by
    cases i
    · exact h.quotient 0
    · exact h.quotient 1
  refine ⟨MulEquiv.ofBijective (graphBaseBinaryOriginalMap h i e)
    ⟨graphBaseBinaryOriginalMap_injective h i e,
      rankOne_binary_embedding_surjective hm _ (graphBaseBinaryOriginalMap_injective h i e)⟩,?_⟩
  intro x
  cases i
  · exact congrArg e (graphEnlargementQuotient_symm_mk h false _)
  · exact congrArg e (graphEnlargementQuotient_symm_mk h true _)

/-- A binary intrinsic graph quotient supplies the original local quotient
on the same orbit, through conjugation and the actual enlargement inclusion. -/
theorem graph_binary_original_quotient (h : HypothesisF11 L S)
    (v : Vertex (reducedFamily L S))
    (e : (graphLocalGroup (reducedFamily L S) v ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) v)) ≃* SL(2,ZMod 2)) :
    Nonempty ((family L v.type ⧸ pCore 2 (family L v.type)) ≃* SL(2,ZMod 2)) := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (reducedFamily L S) v
  obtain ⟨_,f,_,_,_⟩ := local_quotient_parameter_transport (reduced_triple h) g hg
  obtain ⟨e₀,_⟩ := graph_base_binary_original_quotient h v.type (f.trans e)
  exact ⟨e₀⟩

/-- The two adjacent intrinsic binary quotients mark both original starred
quotients. No classification of the original model rows is assumed. -/
theorem adjacent_binary_starred_quotients (h : HypothesisF11 L S)
    {a beta : Vertex (reducedFamily L S)} (hab : (graph (reducedFamily L S)).Adj a beta)
    (ea : (graphLocalGroup (reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) a)) ≃* SL(2,ZMod 2))
    (eb : (graphLocalGroup (reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) beta)) ≃* SL(2,ZMod 2)) :
    ∀ i : Bool, Nonempty ((CommutingThreeProfile.ReducedLayer.star L S i ⧸
      pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2)) := by
  have ha := graph_binary_original_quotient h a ea
  have hb := graph_binary_original_quotient h beta eb
  intro i
  have hi : i = a.type ∨ i = beta.type := by
    have hne := hab.1
    cases ht : a.type <;> cases hu : beta.type <;> cases i <;> simp_all
  have he : Nonempty ((family L i ⧸ pCore 2 (family L i)) ≃* SL(2,ZMod 2)) := by
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  obtain ⟨e⟩ := he
  have ei : Nonempty ((L (if i then 1 else 0) ⧸
      pCore 2 (L (if i then 1 else 0))) ≃* SL(2,ZMod 2)) := by
    cases i <;> exact ⟨e⟩
  obtain ⟨ei⟩ := ei
  exact ⟨(CommutingThreeProfile.ReducedLayer.originalQuotient h i).symm.trans ei⟩

/-- The actual two original fields need only have the same order. The
field-two conclusion of 9.10 gives both Chapter 13 starred binary markings. -/
theorem adjacent_field_two_starred_quotients (h : HypothesisF11 L S)
    {a beta : Vertex (reducedFamily L S)} (hab : (graph (reducedFamily L S)).Adj a beta)
    {K F : Type*} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    (ea : (graphLocalGroup (reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) beta)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F) (hF : Nat.card F = 2) :
    ∀ i : Bool, Nonempty ((CommutingThreeProfile.ReducedLayer.star L S i ⧸
      pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2)) := by
  obtain ⟨eK⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two (hKF.trans hF)
  obtain ⟨eF⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hF
  let e₂ := SLTwoPermThree.sl2Two_equiv_perm_three.some
  exact adjacent_binary_starred_quotients h hab
    (ea.trans ((Theory.PSL2.sl2QuotientEquiv K).trans (eK.trans e₂.symm)))
    (eb.trans ((Theory.PSL2.sl2QuotientEquiv F).trans (eF.trans e₂.symm)))

/-- DGS 13.1(b) on the original F.1.11 pair, once source 9.10 supplies
its numerical field-two result. The original local inclusions are retained
in both full-parabolic quotient markings. -/
theorem adjacent_field_two_full_parabolics (h : HypothesisF11 L S)
    {a beta : Vertex (reducedFamily L S)} (hab : (graph (reducedFamily L S)).Adj a beta)
    {K F : Type*} [Field K] [Finite K] [CharP K 2] [Field F] [Finite F] [CharP F 2]
    (ea : (graphLocalGroup (reducedFamily L S) a ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) a)) ≃* SL(2,K))
    (eb : (graphLocalGroup (reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (reducedFamily L S) beta)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F) (hF : Nat.card F = 2) :
    ∃ e : ∀ i : Bool, (CommutingThreeProfile.ReducedLayer.star L S i ⧸
        pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2),
      commonBorel L S = S ∧ G₀ L S = generated L S ∧
      (∀ i : Bool, ∃ f : (parabolic L S (if i then 1 else 0) ⧸
          pCore 2 (parabolic L S (if i then 1 else 0))) ≃* SL(2,ZMod 2),
        (∀ x : L (if i then 1 else 0),
          f (QuotientGroup.mk (inclusion (show L (if i then 1 else 0) ≤
            parabolic L S (if i then 1 else 0) from le_sup_left.trans le_sup_left) x)) =
            e i (QuotientGroup.mk (CommutingThreeProfile.ReducedLayer.originalActor
              (L := L) (S := S) i x))) ∧
        starredParabolic L S (if i then 1 else 0) = parabolic L S (if i then 1 else 0) ∧
        Group.IsSolvable (parabolic L S (if i then 1 else 0))) ∧
      ∀ v : Vertex (reducedFamily L S),
        graphLocalGroup (reducedFamily L S) v = stabilizer (reducedFamily L S) v ∧
        Nonempty ((stabilizer (reducedFamily L S) v ⧸
          pCore 2 (stabilizer (reducedFamily L S) v)) ≃* SL(2,ZMod 2)) := by
  let e i := Classical.choice (adjacent_field_two_starred_quotients h hab ea eb hKF hF i)
  exact ⟨e,CommutingThreeProfile.source_binary_full_parabolics h e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
