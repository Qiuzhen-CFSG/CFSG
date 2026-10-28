module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryNodePlacement
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Inner
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.EndpointNodes

/-!
# Source placement and generation for inner binary-linear actions

The endpoint node preimages have S₃ two-core quotients and residuals of
order at least sixteen. Their orders have only one factor of three, so
the proved A₃-product bound of twelve excludes that residual form. The
interior nodes use the checked nontrivial sixth-power witness instead.
Thus every node is a source parabolic when the original Sylow action is
inner. Original same-pair placement puts each node in M ∩ L or M_L.
Their full preimages generate L, including its two-core, proving the
required generation of the two original intersections in both dimensions.

The original FF-row and marker applications supply a complete linear
ConstrainedAlternatives branch or retain an actual graph actor under the
same quotient marking. Both original primes are retained. The later
exchanged selection consumes the full inner-node family on both plane
sizes. Graph-action generation, small-block recognition and general Borel
placement remain with this catalogue owner. Original 15.1.14 remains
explicit for its existing producer and final assembly owner.

Source: Aschbacher--Smith 15.1.22(*), (3), printed pp.1098--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open BinaryLinear.OrderedResidualConjugators
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem node_model_cover
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (i : Fin m) :
    ∃ f : b.node i →* minimalParabolic b.basis i,
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let q := coreFlagMap d.L e
  let P := (b.node i).subgroupOf d.L
  have him : P.map q = minimalParabolic b.basis i :=
    coreFlagMap_lift_image d.L e (minimalParabolic b.basis i)
  let t : P ≃* b.node i := subgroupOfEquivOfLe (b.node_le i)
  let f : b.node i →* minimalParabolic b.basis i :=
    ((MulEquiv.subgroupCongr him).toMonoidHom.comp (q.subgroupMap P)).comp t.symm.toMonoidHom
  refine ⟨f,(MulEquiv.subgroupCongr him).surjective.comp
    ((q.subgroupMap_surjective P).comp t.symm.surjective),?_⟩
  have he : f.ker = ((q.ker.subgroupOf P).comap t.symm.toMonoidHom) := by
    ext x
    change (⟨q (t.symm x : d.L),_⟩ : minimalParabolic b.basis i) = 1 ↔
      q (t.symm x : d.L) = 1
    exact Subtype.ext_iff
  rw [he,show q.ker = pCore 2 d.L from coreFlagMap_ker d.L e]
  exact pCore_isPGroup.comap_subtype.comap_of_injective _ t.symm.injective

/-- Both original endpoint preimages retain their S₃ quotients and the
residual-size obstruction to a product of A₃ blocks. -/
theorem BinaryNodeGeometry.endpoint_node_data
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) (hm : 3 ≤ m)
    (i : Fin m) (hi : i.val = 0 ∨ i.val = m-1) :
    Nonempty (((b.node i) ⧸ pCore 2 (b.node i)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ 9 ∣ Nat.card (b.node i) ∧ 16 ≤ Nat.card (pResidual 2 (b.node i)) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hQS : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
    exact hQ
  let U := Q.mapSurjective (coreFlagMap_surjective d.L e)
  have hb : (U : Subgroup (LinearGroup (m+1))) = cutStabilizer b.basis Set.univ := by
    change (Q : Subgroup d.L).map (coreFlagMap d.L e) = _
    rw [hQS,b.sylow_image]
  obtain ⟨⟨eqP⟩,hPcard⟩ := BinaryLinear.InvariantNodeActions.endpoint_node_data hm U b.basis hb i hi
  obtain ⟨f,hf,hker⟩ := node_model_cover b i
  refine ⟨⟨(f.pCoreQuotientEquiv hf hker).trans eqP⟩,?_,?_⟩
  · have hcard : Nat.card (b.node i) = Nat.card f.ker * Nat.card (minimalParabolic b.basis i) := by
      rw [←f.ker.card_mul_index,index_ker,f.range_eq_top_of_surjective hf,card_top]
    obtain ⟨r,hr⟩ := hker.exists_card_eq
    rw [hcard,hr]
    intro hd
    exact node_card_not_nine b.basis i
      (((by decide : Nat.Coprime 9 2).pow_right r).dvd_of_dvd_mul_left hd)
  · have hmapped := map_pResidual_of_surjective 2 f hf
    have hle : Nat.card (pResidual 2 (minimalParabolic b.basis i)) ≤
        Nat.card (pResidual 2 (b.node i)) := by
      rw [←hmapped]
      exact Nat.card_le_card_of_surjective _ (f.subgroupMap_surjective _)
    exact hPcard.trans hle

/-- The endpoint nodes satisfy every source-parabolic clause under inner action. -/
theorem BinaryNodeGeometry.endpoint_node_source_parabolic
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) (hm : 3 ≤ m)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _)
    (i : Fin m) (he : i.val = 0 ∨ i.val = m-1) : d.IsSourceParabolic (b.node i) := by
  obtain ⟨⟨t⟩,h9,h16⟩ := b.endpoint_node_data hK hm i he
  have hn := b.node_normalizes_of_inner i hi
  refine ⟨b.node_le i,inf_le_left.trans hn,b.node_fitting i hf,Or.inl ?_,?_⟩
  · exact NormalSymmetricThreeExtension.normalized_join (b.node i) d.sylowNormalizer
      (inf_le_left.trans hn) t (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))
  · intro hA
    have h12 := aThreeProduct_residual_card_le (b.node i) h9 hA
    omega

/-- The original placement theorem applies to both endpoint nodes, for either
source prime, with the same component and quotient marking. -/
theorem PreExclusionSource.endpoint_node_placement
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {m : ℕ} (hm : 3 ≤ m) {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _)
    (i : Fin m) (he : i.val = 0 ∨ i.val = m-1) :
    d.IsSourceParabolic (b.node i) ∧ (b.node i ≤ M ⊓ d.L ∨ b.node i ≤ d.ML) := by
  have hp := b.endpoint_node_source_parabolic ⟨d.L_component.1,s.local_component⟩ hm hf hi i he
  exact ⟨hp,s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h b.normalizes _ hp⟩

/-- The literal two-core quotient of every original node is S₃. -/
theorem BinaryNodeGeometry.node_quotient
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) (i : Fin m) :
    Nonempty (((b.node i) ⧸ pCore 2 (b.node i)) ≃* Equiv.Perm (Fin 3)) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hQS : (Q : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.SL ≤ d.L from inf_le_right)]
    exact hQ
  let U := Q.mapSurjective (coreFlagMap_surjective d.L e)
  have hb : (U : Subgroup (LinearGroup (m+1))) = cutStabilizer b.basis Set.univ := by
    change (Q : Subgroup d.L).map (coreFlagMap d.L e) = _
    rw [hQS,b.sylow_image]
  obtain ⟨t⟩ := BinaryLinear.InvariantNodeActions.node_quotient U b.basis hb i
  obtain ⟨f,hf,hker⟩ := node_model_cover b i
  exact ⟨(f.pCoreQuotientEquiv hf hker).trans t⟩

/-- Under inner action every original node is a source parabolic. Endpoint
residual size and the interior sixth-power witness supply the two exclusions. -/
theorem BinaryNodeGeometry.inner_nodes_source_parabolic
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) (hm : 3 ≤ m)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _)
    (i : Fin m) : d.IsSourceParabolic (b.node i) := by
  by_cases he : i.val = 0 ∨ i.val = m-1
  · exact b.endpoint_node_source_parabolic hK hm hf hi i he
  · obtain ⟨t⟩ := b.node_quotient hK i
    have hn := b.node_normalizes_of_inner i hi
    refine ⟨b.node_le i,inf_le_left.trans hn,b.node_fitting i hf,Or.inl ?_,
      b.interior_node_not_aThree_product i (by omega) (by omega)⟩
    exact NormalSymmetricThreeExtension.normalized_join (b.node i) d.sylowNormalizer
      (inf_le_left.trans hn) t (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))

/-- The original node preimages generate the original component, including
its full two-core. -/
theorem BinaryNodeGeometry.nodes_generate
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) (hm : 0 < m) :
    (⨆ i : Fin m, b.node i) = d.L := by
  let D := ⨆ i : Fin m, b.node i
  let q := coreFlagMap d.L e
  have hDL : D ≤ d.L := iSup_le b.node_le
  have him : (D.subgroupOf d.L).map q = ⊤ := by
    apply top_unique
    rw [←iSup_minimalParabolic_eq_top hm b.basis]
    apply iSup_le
    intro i
    rw [←coreFlagMap_lift_image d.L e (minimalParabolic b.basis i)]
    exact map_mono (subgroupOf_mono d.L (le_iSup b.node i))
  have hk : q.ker ≤ D.subgroupOf d.L := by
    let i : Fin m := ⟨0,hm⟩
    have hzero : ((q.ker.map d.L.subtype).subgroupOf d.L).map q = ⊥ := by
      rw [show (q.ker.map d.L.subtype).subgroupOf d.L = q.ker from
        comap_map_eq_self_of_injective d.L.subtype_injective _]
      exact (map_eq_bot_iff q.ker).mpr le_rfl
    have hkn : q.ker.map d.L.subtype ≤ b.node i :=
      EquivariantLift.le_lift d.L q (map_subtype_le _)
        (by rw [hzero]; exact bot_le)
    intro x hx
    exact (le_iSup b.node i) (hkn (mem_map_of_mem d.L.subtype hx))
  have he := EquivariantLift.lift_map_subgroupOf d.L q D hDL hk
  rw [him,EquivariantLift.lift_top] at he
  exact he.symm

/-- Both inner-action binary dimensions have the actual original generating
intersections, discharging the generation clause of 15.1.22(3). -/
theorem PreExclusionSource.binary_inner_generated
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {m : ℕ} (hm : 3 ≤ m) {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hi : ∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _) :
    (M ⊓ d.L) ⊔ d.ML = d.L := by
  have hn (i : Fin m) : b.node i ≤ (M ⊓ d.L) ⊔ d.ML := by
    have hp := b.inner_nodes_source_parabolic ⟨d.L_component.1,s.local_component⟩ hm hf hi i
    rcases s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h b.normalizes _ hp with hP | hP
    · exact hP.trans le_sup_left
    · exact hP.trans le_sup_right
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  calc
    d.L = ⨆ i : Fin m, b.node i := (b.nodes_generate (by omega)).symm
    _ ≤ (M ⊓ d.L) ⊔ d.ML := iSup_le hn
/-- Each original binary FF row either supplies a completed constrained
alternative or has an actual graph actor. The inner branch includes the
literal generation of the original intersections. -/
theorem PreExclusionSource.constrained_binary_inner_or_graph
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : d.normalizerImage d.L ≃* SL(m+1,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t,
        d.BinaryEndpointExtension a.endpoint ∧ ∃ b : d.BinaryNodeGeometry a,
          (d.ConstrainedAlternatives ∧ (M ⊓ d.L) ⊔ d.ML = d.L) ∨
            (∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _) := by
  obtain ⟨t,ht,hML,hM',a,ha,⟨b⟩⟩ :=
    s.constrained_binary_nodes (h := h) hG hempty hM hJ hu hf hm e
  refine ⟨t,ht,hML,hM',a,ha,b,?_⟩
  rcases b.action with hi | ⟨ho,_⟩
  · have hg := s.binary_inner_generated (h := h) hG hM hJ hu hf (by omega) b hi.1
    exact Or.inl ⟨ConstrainedAlternatives.linear (m+1) (by omega) t hML hM' hg,hg⟩
  · exact Or.inr ho

/-- The later exchanged selection retains source-family membership for every
node in the inner branch, in both binary dimensions and both plane sizes. -/
theorem ExchangedSource.constrained_binary_inner_node_membership
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    {m : ℕ} (hm : m=3 ∨ m=4) (e : d.normalizerImage d.L ≃* SL(m+1,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t,
        d.BinaryEndpointExtension a.endpoint ∧ ∃ b : d.BinaryNodeGeometry a,
          ((∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∧
            ∀ i : Fin m, d.IsSourceParabolic (b.node i)) ∨
          (∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _) := by
  obtain ⟨t,ht,hML,hM',a,ha,⟨b⟩⟩ :=
    s.constrained_binary_nodes hG hempty hM hJ hu h hf hm e
  refine ⟨t,ht,hML,hM',a,ha,b,?_⟩
  rcases b.action with hi | ⟨ho,_⟩
  · exact Or.inl ⟨hi.1,b.inner_nodes_source_parabolic
      ⟨d.L_component.1,s.local_component⟩ (by omega) hf hi.1⟩
  · exact Or.inr ho

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open BinaryLinear.InvariantNodeActions
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The original marker consumes the completed inner-action branch without
changing its prime, row or seed. Original 15.1.14 remains an explicit earlier
input for its existing producer and final assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_inner_or_graph
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
        ∀ m : ℕ, m=3 ∨ m=4 →
        ∀ e : d.normalizerImage d.L ≃* SL(m+1,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          ∃ a : d.BinaryGeneratingParabolics t,
            d.BinaryEndpointExtension a.endpoint ∧ ∃ b : d.BinaryNodeGeometry a,
              (d.ConstrainedAlternatives ∧ (M ⊓ d.L) ⊔ d.ML = d.L) ∨
                (∃ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∉ MulAut.innerSubgroup _)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf _ hm e =>
    s.constrained_binary_inner_or_graph (h := h) hG hempty hM hJ hu hf hm e⟩
end CFSG.Quasithin.Chapter15.Section01
