module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinarySourceParabolics
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Normalized
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.InteriorResiduals
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.RankOnePerfectResidual
public import Theory.GroupTheory.NormalSymmetricThreeExtension
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.FirstPair

/-!
# Original placement of the degree-five interior nodes and graph endpoint

Every interior minimal parabolic has incident root elements whose product
has a nonidentity sixth power in its two-residual. This excludes a central
product of A₃ blocks. The literal preimage in L has characteristic two and
S₃ two-core quotient; adjoining its normalizing Sylow subgroup retains that
quotient. Thus in the inner-action branch both interior nodes belong to the
source parabolic family. The proved original same-pair placement puts each
in M ∩ L or M_L, and their join is the original interior parabolic.

In the graph branch the previously proved endpoint family membership and
the same placement theorem identify the endpoint with one of the two
original intersections: the node alternatives and generation exclude the
Sylow and interior positions. Both original primes retain the same quotient
marking, component and seed. The exchanged-source application retains the
same node membership on both plane sizes.

The inner-action endpoint nodes and the graph-action interior still need
their source arguments. Small-block recognition and general Borel placement
also remain before constrained-catalogue exhaustion. Original 15.1.14 stays
explicit in the marker application for its existing producer and final owner.

Source: Aschbacher--Smith 15.1.22(*), (3), printed pp.1098--1100.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal preimage of one minimal parabolic in the common flag marking. -/
noncomputable def BinaryNodeGeometry.node
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    Subgroup G := EquivariantLift.lift d.L (coreFlagMap d.L e) (minimalParabolic b.basis i)

private theorem node_eq
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    b.node i = ((minimalParabolic b.basis i).comap (coreFlagMap d.L e)).map d.L.subtype := by
  let q := coreFlagMap d.L e
  let P := (minimalParabolic b.basis i).comap q
  let D := P.map d.L.subtype
  have hD : D.subgroupOf d.L = P := comap_map_eq_self_of_injective d.L.subtype_injective _
  have him : (D.subgroupOf d.L).map q = minimalParabolic b.basis i := by
    rw [hD]
    exact map_comap_eq_self (by rw [q.range_eq_top_of_surjective (coreFlagMap_surjective d.L e)]; exact le_top)
  have he := EquivariantLift.lift_map_subgroupOf d.L q D (map_subtype_le _)
    (by rw [hD]; exact ker_le_comap _ _)
  rw [him] at he
  exact he

/-- Each marked node remains inside the original component. -/
theorem BinaryNodeGeometry.node_le
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    b.node i ≤ d.L := EquivariantLift.lift_le _ _ _

/-- Characteristic two descends to the actual node preimage. -/
theorem BinaryNodeGeometry.node_fitting
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    generalizedFitting (b.node i) = pCore 2 (b.node i) := by
  let P := (minimalParabolic b.basis i).comap (coreFlagMap d.L e)
  let t : P ≃* b.node i := (P.equivMapOfInjective d.L.subtype d.L.subtype_injective).trans
    (MulEquiv.subgroupCongr (node_eq b i).symm)
  have hcore : pCore 2 d.L ≤ P := by
    rw [←coreFlagMap_ker d.L e]
    exact ker_le_comap _ _
  have hP := generalizedFitting_eq_pCore_of_normalized_by_pCore P hf
    (hcore.trans P.le_normalizer)
  rw [←map_generalizedFitting_equiv t,←pCore_map_iso 2 t,hP]

/-- Inner Sylow action fixes every node under the original quotient marking. -/
theorem BinaryNodeGeometry.node_normalizes_of_inner
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _) :
    d.S ≤ normalizer (b.node i : Set G) := by
  rcases b.action with h | ⟨⟨x,hx⟩,_⟩
  · exact h.2 {i}ᶜ
  · exact (hx (hi x)).elim

private noncomputable def nodeMap
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    b.node i →* minimalParabolic b.basis i := by
  let P := (minimalParabolic b.basis i).comap (coreFlagMap d.L e)
  let t : P ≃* b.node i := (P.equivMapOfInjective d.L.subtype d.L.subtype_injective).trans
    (MulEquiv.subgroupCongr (node_eq b i).symm)
  exact ((coreFlagMap d.L e).comp P.subtype).codRestrict _ (fun x => x.property) |>.comp t.symm.toMonoidHom

private theorem nodeMap_surjective
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    Function.Surjective (nodeMap b i) := by
  let P := (minimalParabolic b.basis i).comap (coreFlagMap d.L e)
  let t : P ≃* b.node i := (P.equivMapOfInjective d.L.subtype d.L.subtype_injective).trans
    (MulEquiv.subgroupCongr (node_eq b i).symm)
  intro y
  obtain ⟨x,hx⟩ := coreFlagMap_surjective d.L e y
  refine ⟨t ⟨x,show coreFlagMap d.L e x ∈ minimalParabolic b.basis i from hx.symm ▸ y.property⟩,?_⟩
  apply Subtype.ext
  change coreFlagMap d.L e (t.symm (t _) : d.L) = y
  rw [t.symm_apply_apply]
  exact hx

private theorem nodeMap_kernel_two
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    IsPGroup 2 (nodeMap b i).ker := by
  let P := (minimalParabolic b.basis i).comap (coreFlagMap d.L e)
  let t : P ≃* b.node i := (P.equivMapOfInjective d.L.subtype d.L.subtype_injective).trans
    (MulEquiv.subgroupCongr (node_eq b i).symm)
  have he : (nodeMap b i).ker = ((coreFlagMap d.L e).ker.subgroupOf P).comap t.symm.toMonoidHom := by
    ext x
    change (⟨coreFlagMap d.L e (t.symm x : d.L),_⟩ : minimalParabolic b.basis i) = 1 ↔
      coreFlagMap d.L e (t.symm x : d.L) = 1
    exact Subtype.ext_iff
  rw [he,coreFlagMap_ker]
  exact pCore_isPGroup.comap_subtype.comap_of_injective _ t.symm.injective

/-- The model residual witness excludes A₃ products in the original node. -/
theorem BinaryNodeGeometry.interior_node_not_aThree_product
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m)
    (hi : 0 < i.val) (hi' : i.val + 1 < m) : ¬ IsAThreeProduct (b.node i) := by
  rintro ⟨F,hF,hc,hgen⟩
  obtain ⟨y,hy,hy6⟩ := interior_node_residual_not_exponent_six b.basis i hi hi'
  rw [←map_pResidual_of_surjective 2 (nodeMap b i) (nodeMap_surjective b i)] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  apply hy6
  rw [←map_pow,ChapterC.alternatingThree_product_pow_six F
    (fun A hA => (hF A hA).2) hc (hgen.symm ▸ hx),map_one]

/-- Every degree-five node has its literal S₃ two-core quotient. -/
theorem BinaryNodeGeometry.five_node_quotient
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin 4) :
    Nonempty (((b.node i) ⧸ pCore 2 (b.node i)) ≃* Equiv.Perm (Fin 3)) := by
  let : Finite (LinearGroup 5) := Finite.of_injective
    (fun g : LinearGroup 5 => (g : Space 5 → Space 5)) DFunLike.coe_injective
  exact ⟨((nodeMap b i).pCoreQuotientEquiv (nodeMap_surjective b i) (nodeMap_kernel_two b i)).trans
    (BinaryLinear.FiveFlagGeometry.rankOneQuotientEquiv b.basis i)⟩

/-- All source-family clauses hold for both interior nodes in the inner branch. -/
theorem BinaryNodeGeometry.five_interior_source_parabolic
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _)
    (i : Fin 4) (hi0 : 0 < i.val) (hi3 : i.val < 3) :
    d.IsSourceParabolic (b.node i) := by
  have hn := b.node_normalizes_of_inner i hi
  obtain ⟨t⟩ := b.five_node_quotient i
  refine ⟨b.node_le i,inf_le_left.trans hn,b.node_fitting i hf,Or.inl ?_,
    b.interior_node_not_aThree_product i hi0 (by omega)⟩
  exact NormalSymmetricThreeExtension.normalized_join (b.node i) d.sylowNormalizer
    (inf_le_left.trans hn) t (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))


private theorem endpoint_eq_of_node_position
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    (a : d.BinaryGeneratingParabolics e) {P : Subgroup G}
    (hP : d.BinaryNodePosition a P) (hEP : a.endpoint ≤ P) : a.endpoint = P := by
  have hnot : ¬ a.endpoint ≤ a.interior := by
    intro he
    exact (not_le_of_gt a.interior_proper) (a.generated ▸ sup_le le_rfl he)
  rcases hP with rfl | rfl | rfl
  · exact (hnot (hEP.trans a.sylow_interior)).elim
  · exact (hnot hEP).elim
  · rfl

/-- The degree-five graph endpoint is one of the two original intersections. -/
theorem PreExclusionSource.five_graph_endpoint_eq
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (ho : ∃ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∉ MulAut.innerSubgroup _) :
    d.IsSourceParabolic a.endpoint ∧ (a.endpoint = M ⊓ d.L ∨ a.endpoint = d.ML) := by
  have hp : d.IsSourceParabolic a.endpoint := by
    rcases b.five_endpoint_source_parabolic ⟨d.L_component.1,s.local_component⟩ with hi | hp
    · obtain ⟨x,hx⟩ := ho
      exact (hx (hi x)).elim
    · exact hp
  refine ⟨hp,?_⟩
  rcases b.action with hi | ⟨_,_,hML,hM'⟩
  · obtain ⟨x,hx⟩ := ho
    exact (hx (hi.1 x)).elim
  · rcases s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h b.normalizes _ hp with hm | hm
    · exact Or.inl (endpoint_eq_of_node_position a hM' hm)
    · exact Or.inr (endpoint_eq_of_node_position a hML hm)

/-- Original source placement for both interior nodes when the action is inner. -/
theorem PreExclusionSource.five_interior_node_placement
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _)
    (i : Fin 4) (hi0 : 0 < i.val) (hi3 : i.val < 3) :
    d.IsSourceParabolic (b.node i) ∧ (b.node i ≤ M ⊓ d.L ∨ b.node i ≤ d.ML) := by
  have hp := b.five_interior_source_parabolic hf hi i hi0 hi3
  exact ⟨hp,s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h b.normalizes _ hp⟩


/-- The actual degree-five interior is the join of its two interior nodes. -/
theorem BinaryNodeGeometry.five_interior_eq_nodes
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) :
    a.interior = b.node 1 ⊔ b.node 2 := by
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hQS : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
    exact hQ
  let U := Q.mapSurjective (coreFlagMap_surjective d.L e)
  have hb : (U : Subgroup (LinearGroup 5)) = cutStabilizer b.basis Set.univ := by
    change (Q : Subgroup d.L).map (coreFlagMap d.L e) = _
    rw [hQS,b.sylow_image]
  have hp := BinaryLinear.SylowFlagOvergroups.pair_eq_cutStabilizer U b.basis hb 1 2
  have hc : ({1,2} : Set (Fin 4))ᶜ = {i : Fin 4 | i.val=0 ∨ i.val=3} := by
    ext i
    fin_cases i <;> decide
  rw [hc] at hp
  rw [b.interior_marking, BinaryNodeGeometry.node, BinaryNodeGeometry.node,
    ←EquivariantLift.lift_sup d.L (coreFlagMap d.L e) (coreFlagMap_surjective d.L e),hp]

/-- Both placed interior nodes put the whole original interior in the join
of the original intersections, with no generation premise added. -/
theorem PreExclusionSource.five_interior_le_original_join
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _) :
    a.interior ≤ (M ⊓ d.L) ⊔ d.ML := by
  have hp (i : Fin 4) (h0 : 0 < i.val) (h3 : i.val < 3) :
      b.node i ≤ (M ⊓ d.L) ⊔ d.ML := by
    rcases (s.five_interior_node_placement (h := h) hG hM hJ hu hf b hi i h0 h3).2 with h | h
    · exact h.trans le_sup_left
    · exact h.trans le_sup_right
  rw [b.five_interior_eq_nodes ⟨d.L_component.1,s.local_component⟩]
  exact sup_le (hp 1 (by decide) (by decide)) (hp 2 (by decide) (by decide))

/-- Both original primes retain the marked quotient and the actual placements:
interior nodes in the inner case, the endpoint intersection in the graph case. -/
theorem PreExclusionSource.constrained_binary_five_node_placement
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* SL(5,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(5,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t,
        d.BinaryEndpointExtension a.endpoint ∧ ∃ b : d.BinaryNodeGeometry a,
          ((∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∧
            a.interior ≤ (M ⊓ d.L) ⊔ d.ML ∧
            ∀ i : Fin 4, 0 < i.val → i.val < 3 →
              d.IsSourceParabolic (b.node i) ∧ (b.node i ≤ M ⊓ d.L ∨ b.node i ≤ d.ML)) ∨
          ((∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _) ∧
            d.IsSourceParabolic a.endpoint ∧ (a.endpoint = M ⊓ d.L ∨ a.endpoint = d.ML)) := by
  obtain ⟨t,ht,hML,hM',a,ha,b,_⟩ :=
    s.constrained_binary_wreath (h := h) hG hempty hM hJ hu hf (Or.inr rfl) e
  refine ⟨t,ht,hML,hM',a,ha,b,?_⟩
  rcases b.action with hi | ⟨ho,_⟩
  · exact Or.inl ⟨hi.1,s.five_interior_le_original_join (h := h) hG hM hJ hu hf b hi.1,
      fun i h0 h3 => s.five_interior_node_placement (h := h) hG hM hJ hu hf b hi.1 i h0 h3⟩
  · exact Or.inr ⟨ho,s.five_graph_endpoint_eq (h := h) hG hM hJ hu b ho⟩

/-- The exchanged source uses the same literal interior nodes and endpoint,
with both plane sizes retained. -/
theorem ExchangedSource.constrained_binary_five_node_membership
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* SL(5,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(5,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t,
        d.BinaryEndpointExtension a.endpoint ∧ ∃ b : d.BinaryNodeGeometry a,
          ((∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∧
            ∀ i : Fin 4, 0 < i.val → i.val < 3 → d.IsSourceParabolic (b.node i)) ∨
          ((∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _) ∧
            d.IsSourceParabolic a.endpoint) := by
  obtain ⟨t,ht,hML,hM',a,ha,b,_⟩ :=
    s.constrained_binary_wreath hG hempty hM hJ hu h hf (Or.inr rfl) e
  refine ⟨t,ht,hML,hM',a,ha,b,?_⟩
  rcases b.action with hi | ⟨ho,_⟩
  · exact Or.inl ⟨hi.1,fun i h0 h3 => b.five_interior_source_parabolic hf hi.1 i h0 h3⟩
  · refine Or.inr ⟨ho,?_⟩
    rcases b.five_endpoint_source_parabolic ⟨d.L_component.1,s.local_component⟩ with hi | hp
    · obtain ⟨x,hx⟩ := ho
      exact (hx (hi x)).elim
    · exact hp

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open BinaryLinear.InvariantNodeActions
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The original marker consumes the proved node family and original placements;
its row, seed and prime, including prime five, are unchanged. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_five_node_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (marker : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = marker.Z1 ∧ d.row = marker.row ∧
      d.PreExclusionSource h.normalized marker.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* SL(5,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(5,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          ∃ a : d.BinaryGeneratingParabolics t,
            d.BinaryEndpointExtension a.endpoint ∧ ∃ b : d.BinaryNodeGeometry a,
              ((∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∧
                a.interior ≤ (M ⊓ d.L) ⊔ d.ML ∧
                ∀ i : Fin 4, 0 < i.val → i.val < 3 →
                  d.IsSourceParabolic (b.node i) ∧ (b.node i ≤ M ⊓ d.L ∨ b.node i ≤ d.ML)) ∨
              ((∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _) ∧
                d.IsSourceParabolic a.endpoint ∧ (a.endpoint = M ⊓ d.L ∨ a.endpoint = d.ML))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binary_five_node_placement (h := h) hG hempty hM hJ hu hf e⟩
end CFSG.Quasithin.Chapter15.Section01
