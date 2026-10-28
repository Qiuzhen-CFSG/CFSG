module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinaryExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLayers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement
public import Theory.GroupTheory.PCoreProduct
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Full parabolics in the both-binary branch

Earlier Chapter 9 supplies the two local SL₂(2) quotient markings. Their
Sylow normalizers give B = S. Hence the full-Borel-core enlargement is the
full original parabolic, and the proved linear enlargement theorem identifies
it with the original starred parabolic. The reduction therefore preserves
both original endpoints and the entire original completion.

The resulting full parabolic quotient equivalences retain the literal local
inclusions. Conjugation transports them to every vertex of the reduced graph;
the intrinsic Sylow-generated local group equals the full vertex stabilizer.
The full original parabolics are solvable. BinarySourceApplication consumes
these conclusions with the actual reduced starred markings.

This proves the full-group upgrade in DGS (13.1)(b) from the earlier binary
markings. It does not derive those Chapter 9 markings, b = 3, the remaining
clauses of (13.1), or the Chapter 12 alternatives.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (6.1), (13.1)(a--b), printed pp.118--119,191; Aschbacher--Smith F.1.9.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Reduction Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Both binary markings identify each starred parabolic with the full original endpoint. -/
theorem both_binary_star_eq_parabolic (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) (i : Fin 2) :
    starredParabolic L S i = parabolic L S i := by
  have he := reduced_enlargedEndpoint_eq_starred_of_linear h i
    ((e i).trans (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))
  rw [enlargedEndpoint, both_binary_commonBorel h e,
    pCoreIn_eq_self_of_isPGroup 2 S h.S_isP] at he
  calc
    starredParabolic L S i = starredParabolic L S i ⊔ S := he.symm
    _ = starredParabolic L S i ⊔ commonBorel L S :=
      congrArg (fun B => starredParabolic L S i ⊔ B) (both_binary_commonBorel h e).symm
    _ = parabolic L S i := h.starredParabolic_supplement i

/-- The full-Borel reduction changes neither endpoint nor the original completion. -/
theorem both_binary_reduction_eq_original (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) :
    B₀ L S = S ∧ (∀ i, P₀ L S i = parabolic L S i) ∧ G₀ L S = generated L S := by
  have hc : (commonBorel L S).pCoreIn 2 = S := by
    rw [both_binary_commonBorel h e, pCoreIn_eq_self_of_isPGroup 2 S h.S_isP]
  have hB : B₀ L S = S := le_antisymm
    ((B₀_le h).trans_eq (both_binary_commonBorel h e))
    (hc.ge.trans (show (commonBorel L S).pCoreIn 2 ≤ B₀ L S from le_sup_right))
  have hP (i : Fin 2) : P₀ L S i = parabolic L S i := by
    change starredParabolic L S i ⊔ B₀ L S = _
    rw [hB]
    exact (congrArg (fun B => starredParabolic L S i ⊔ B)
      (both_binary_commonBorel h e).symm).trans (h.starredParabolic_supplement i)
  refine ⟨hB, hP, ?_⟩
  rw [G₀, hP 0, hP 1, parabolics_generate]

/-- The full original parabolic quotient, marked through the actual local inclusion. -/
def binaryFullParabolicEquiv (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) (i : Fin 2) :
    (parabolic L S i ⧸ pCore 2 (parabolic L S i)) ≃* SL(2, ZMod 2) :=
  (QuotientGroup.congr _ _
    (MulEquiv.subgroupCongr (both_binary_star_eq_parabolic h e i).symm)
    (pCore_map_iso 2 _)).trans ((h.starredQuotientEquiv i).symm.trans (e i))

/-- On local representatives the full quotient marking is the original one. -/
theorem binaryFullParabolicEquiv_mk (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) (i : Fin 2) (x : L i) :
    binaryFullParabolicEquiv h e i (QuotientGroup.mk
      (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) x)) =
      e i (QuotientGroup.mk x) := by
  change e i ((h.starredQuotientEquiv i).symm
    (QuotientGroup.mk (inclusion (local_le_starredParabolic i) x))) = _
  rw [← h.starredQuotientEquiv_mk, MulEquiv.symm_apply_apply]

/-- The full original endpoints, including their intrinsic two-cores, are solvable. -/
theorem both_binary_full_parabolics_solvable (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) (i : Fin 2) :
    Group.IsSolvable (parabolic L S i) := by
  let := h.finite_parabolic i
  exact SymmetricThreeTwoCore.solvable
    ((binaryFullParabolicEquiv h e i).trans SLTwoPermThree.sl2Two_equiv_perm_three.some)

/-- DGS (13.1)(b): the intrinsic local group is the entire stabilizer at every vertex. -/
theorem both_binary_graphLocalGroup_eq_stabilizer (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2))
    (v : Vertex (reducedFamily L S)) :
    graphLocalGroup (reducedFamily L S) v = stabilizer (reducedFamily L S) v := by
  let F := reducedFamily L S
  have hb (i : Bool) : graphLocalGroup F (base F i) = stabilizer F (base F i) := by
    apply map_injective (G₀ L S).subtype_injective
    rw [reduced_graphLocalGroup_image h, stabilizer, Subgroup.CosetGeometry.stabilizer_base]
    have he := reduced_enlargedEndpoint_eq_starred_of_linear h (if i then 1 else 0)
      ((e (if i then 1 else 0)).trans (Theory.PSL2.sl2QuotientEquiv (ZMod 2)))
    have hP := (both_binary_reduction_eq_original h e).2.1 (if i then 1 else 0)
    have hstar := both_binary_star_eq_parabolic h e (if i then 1 else 0)
    cases i
    · change enlargedEndpoint L S 0 = ((P₀ L S 0).subgroupOf (G₀ L S)).map (G₀ L S).subtype
      rw [map_subgroupOf_eq_of_le (ReducedLayer.endpoint_le_completion 0)]
      exact he.trans (hstar.trans hP.symm)
    · change enlargedEndpoint L S 1 = ((P₀ L S 1).subgroupOf (G₀ L S)).map (G₀ L S).subtype
      rw [map_subgroupOf_eq_of_le (ReducedLayer.endpoint_le_completion 1)]
      exact he.trans (hstar.trans hP.symm)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  change graphLocalGroup F v = stabilizer F v
  rw [← hg]
  calc
    graphLocalGroup F (g • base F v.type) =
        (graphLocalGroup F (base F v.type)).map (MulAut.conj g).toMonoidHom :=
      graphLocalGroup_conjugate (reduced_triple h) g (base F v.type)
    _ = (stabilizer F (base F v.type)).map (MulAut.conj g).toMonoidHom := by rw [hb]
    _ = stabilizer F (g • base F v.type) := (stabilizer_translate F g _).symm

/-- Identify a base-vertex stabilizer with its actual original parabolic. -/
def binaryBaseStabilizerEquiv (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) (i : Bool) :
    stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ≃*
      parabolic L S (if i then 1 else 0) :=
  (MulEquiv.subgroupCongr (show stabilizer (reducedFamily L S)
      (base (reducedFamily L S) i) =
      (P₀ L S (if i then 1 else 0)).subgroupOf (G₀ L S) from by
        rw [stabilizer, Subgroup.CosetGeometry.stabilizer_base]
        cases i <;> rfl)).trans
    ((subgroupOfEquivOfLe (ReducedLayer.endpoint_le_completion (if i then 1 else 0))).trans
      (MulEquiv.subgroupCongr ((both_binary_reduction_eq_original h e).2.1 _)))

/-- The stabilizer identification is the literal reduced-completion inclusion. -/
theorem binaryBaseStabilizerEquiv_coe (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2)) (i : Bool)
    (x : stabilizer (reducedFamily L S) (base (reducedFamily L S) i)) :
    (binaryBaseStabilizerEquiv h e i x : G) = (x : G₀ L S) := rfl

/-- The full stabilizer at every vertex has its actual two-core quotient isomorphic to SL₂(2). -/
theorem both_binary_vertex_quotient (h : HypothesisF11 L S)
    (e : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* SL(2, ZMod 2))
    (v : Vertex (reducedFamily L S)) :
    Nonempty ((stabilizer (reducedFamily L S) v ⧸
      pCore 2 (stabilizer (reducedFamily L S) v)) ≃* SL(2, ZMod 2)) := by
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  have hv : stabilizer F v = (stabilizer F (base F v.type)).map
      (MulAut.conj g).toMonoidHom := by rw [← hg, stabilizer_translate]; rfl
  let c := ((stabilizer F (base F v.type)).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hv.symm)
  let d := c.symm.trans (binaryBaseStabilizerEquiv h e v.type)
  exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
    (binaryFullParabolicEquiv h e (if v.type then 1 else 0))⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
