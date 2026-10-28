module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryGraphFive
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.Cardinality
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FourEndpointResidual

/-!
# Completion of the constrained binary linear branches

The degree-four interior is the middle node, whose two-residual has a
nonidentity sixth power. The graph endpoint has a wreath Sylow-extension
quotient. Its model residual has at least 144 elements. Characteristic two
in the full original component makes its residual strictly larger than
its quotient image: otherwise that residual would centralize the original
two-core and hence lie in it. But a product of A₃ blocks here has at most
144 elements. Thus both original parabolics belong to the source family.

Original same-pair placement and their generation of L prove the linear
ConstrainedAlternatives branch. The final binary-row theorem combines this
with the checked inner-action and degree-five branches, retaining both
original primes, the quotient marking, and later exchanged selection.
Small-block recognition and general local-family Borel placement remain
obligations of the catalogue. Original 15.1.14 remains explicit for its
existing producer and final source assembly owner.

Source: Aschbacher--Smith 15.1.22(*), (3), printed pp.1098--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem residual_card_lt_of_characteristic_core
    {D : Type*} [Group D] [Finite D]
    (P : Subgroup G) (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hQ : pCore 2 G ≤ P) (f : P →* D) (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 G).subgroupOf P)
    (hne : pResidual 2 D ≠ ⊥) :
    Nat.card (pResidual 2 D) < Nat.card (pResidual 2 P) := by
  let R := pResidual 2 P
  let Q := (pCore 2 G).subgroupOf P
  let g := f.subgroupMap R
  have him : R.map f = pResidual 2 D := map_pResidual_of_surjective 2 f hf
  by_contra hn
  have hinj : Function.Injective g :=
    (f.subgroupMap_surjective R).bijective_of_nat_card_le (by
      rw [him]
      exact Nat.le_of_not_gt hn) |>.1
  have hdis : Disjoint R Q := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hx0 : f x = 1 := by change x ∈ f.ker; rw [hk]; exact hx.2
    have he : g ⟨x,hx.1⟩ = g 1 := by apply Subtype.ext; exact hx0.trans (map_one f).symm
    exact congrArg Subtype.val (hinj he)
  have hcomm : ⁅R,Q⁆ = ⊥ := bot_unique ((commutator_le_inf R Q).trans hdis.le_bot)
  have hRQ : R ≤ Q := by
    intro x hx
    apply hc
    intro y hy
    have hyP := hQ hy
    exact congrArg Subtype.val ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx ⟨y,hyP⟩ hy)
  have hz : R.map f = ⊥ := (Subgroup.map_eq_bot_iff R).mpr (hk.symm ▸ hRQ)
  exact hne (him.symm.trans hz)

/-- The degree-four interior is exactly the middle minimal parabolic. -/
theorem BinaryNodeGeometry.four_interior_eq_node
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(3+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a) :
    a.interior = b.node 1 := by
  rw [b.interior_marking]
  change EquivariantLift.lift _ _ (cutStabilizer b.basis _) =
    EquivariantLift.lift _ _ (cutStabilizer b.basis _)
  congr 2
  ext i
  fin_cases i <;> decide

/-- In degree four the interior satisfies the source family in either action. -/
theorem BinaryNodeGeometry.four_interior_source_parabolic
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(3+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) : d.IsSourceParabolic a.interior := by
  obtain ⟨t⟩ := b.node_quotient hK 1
  rw [←b.four_interior_eq_node] at t
  refine ⟨a.interior_proper.le,inf_le_left.trans a.normalizes_interior,
    a.interior_fitting,Or.inl ?_,?_⟩
  · exact NormalSymmetricThreeExtension.normalized_join a.interior d.sylowNormalizer
      (inf_le_left.trans a.normalizes_interior) t
      (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))
  · rw [b.four_interior_eq_node]
    exact b.interior_node_not_aThree_product 1 (by decide) (by decide)

/-- The original characteristic-two component rules out an A₃-product
residual in the degree-four endpoint, including its entire two-core kernel. -/
theorem BinaryNodeGeometry.four_endpoint_not_aThree_product
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(3+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (hE : a.endpoint = EquivariantLift.lift d.L (coreFlagMap d.L e)
      (cutStabilizer b.basis {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ)) :
    ¬ IsAThreeProduct a.endpoint := by
  let q := coreFlagMap d.L e
  let P := a.endpoint.subgroupOf d.L
  let E := BinaryLinear.parabolic (cutSpace b.basis (1 : Fin 3))
  have hflag : cutStabilizer b.basis {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ = E := by
    ext g
    rw [mem_cutStabilizer]
    constructor
    · exact fun hh => hh 1 (by decide)
    · intro hh i hi
      have he : i=1 := by fin_cases i <;> simp_all
      subst i
      exact hh
  have him : P.map q = E := by
    change (a.endpoint.subgroupOf d.L).map q = E
    rw [hE,coreFlagMap_lift_image,hflag]
  let f : P →* E := (MulEquiv.subgroupCongr him).toMonoidHom.comp (q.subgroupMap P)
  have hsurj : Function.Surjective f :=
    (MulEquiv.subgroupCongr him).surjective.comp (q.subgroupMap_surjective P)
  have hk : f.ker = (pCore 2 d.L).subgroupOf P := by
    ext x
    change (⟨q x,_⟩ : E) = 1 ↔ (x : d.L) ∈ pCore 2 d.L
    rw [←coreFlagMap_ker d.L e]
    exact Subtype.ext_iff
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  have hcore : pCore 2 d.L ≤ P := by
    intro x hx
    have hxSL : (x : G) ∈ d.S ⊓ d.L := hQ ▸ mem_map_of_mem d.L.subtype
      (pCore_isPGroup.le_sylow_of_normal Q hx)
    exact a.sylow_endpoint hxSL
  obtain ⟨h576,h144⟩ := four_endpoint_residual_data b.basis
  change Nat.card E = 576 at h576
  change 144 ≤ Nat.card (pResidual 2 E) at h144
  have hne : pResidual 2 E ≠ ⊥ := by intro he; rw [he,card_bot] at h144; omega
  have hlt := residual_card_lt_of_characteristic_core P
    (hf ▸ centralizer_generalizedFitting_le d.L) hcore f hsurj hk hne
  have hker : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.comap_subtype
  have h27 : ¬27 ∣ Nat.card P := by
    have hc := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective hsurj,card_top,h576] at hc
    obtain ⟨r,hr⟩ := hker.exists_card_eq
    rw [hr] at hc
    intro hd
    rw [←hc] at hd
    exact (by decide : ¬27 ∣ 576)
      (((by decide : Nat.Coprime 27 2).pow_right r).dvd_of_dvd_mul_left hd)
  let t : P ≃* a.endpoint := subgroupOfEquivOfLe a.endpoint_proper.le
  have hcard : Nat.card (pResidual 2 P) = Nat.card (pResidual 2 a.endpoint) := by
    have hh := congrArg (fun X : Subgroup a.endpoint => Nat.card X)
      (map_pResidual_of_surjective 2 t.toMonoidHom t.surjective)
    rw [card_map_of_injective t.injective] at hh
    exact hh
  rintro ⟨F,hF,hcomm,hgen⟩
  have hbound := ChapterC.alternatingThree_product_card_le_of_not_dvd F
    (fun A hA => (hF A hA).2) hcomm (by rwa [←Nat.card_congr t.toEquiv])
  rw [hgen] at hbound
  rw [hcard] at hlt
  omega

/-- In degree four a graph actor gives every endpoint source-family clause. -/
theorem BinaryNodeGeometry.four_graph_endpoint_source_parabolic
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(3+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (ho : ∃ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∉ MulAut.innerSubgroup _) :
    d.IsSourceParabolic a.endpoint := by
  have hE : a.endpoint = EquivariantLift.lift d.L (coreFlagMap d.L e)
      (cutStabilizer b.basis {i : Fin 3 | i.val=0 ∨ i.val=2}ᶜ) := by
    rcases b.action with hi | ⟨_,hE,_⟩
    · obtain ⟨x,hx⟩ := ho
      exact (hx (hi.1 x)).elim
    · exact hE
  refine ⟨a.endpoint_proper.le,inf_le_left.trans a.normalizes_endpoint,
    a.endpoint_fitting,?_,b.four_endpoint_not_aThree_product hK hf hE⟩
  rcases b.extension_cases hK (Or.inl rfl) with hi | hw
  · obtain ⟨x,hx⟩ := ho
    exact (hx (hi x)).elim
  · exact Or.inr hw

/-- Original source placement of both generators completes degree four
under graph action, for either original prime. -/
theorem PreExclusionSource.binary_four_graph_generated
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(3+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (ho : ∃ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∉ MulAut.innerSubgroup _) :
    (M ⊓ d.L) ⊔ d.ML = d.L := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have hplace (P : Subgroup G) (hP : d.IsSourceParabolic P) :
      P ≤ (M ⊓ d.L) ⊔ d.ML := by
    rcases s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h b.normalizes P hP with hm | hm
    · exact hm.trans le_sup_left
    · exact hm.trans le_sup_right
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  calc
    d.L = a.interior ⊔ a.endpoint := a.generated.symm
    _ ≤ (M ⊓ d.L) ⊔ d.ML := sup_le
      (hplace _ (b.four_interior_source_parabolic hK))
      (hplace _ (b.four_graph_endpoint_source_parabolic hK hf ho))

/-- Both actions on the original degree-four FF row supply the complete
linear constrained alternative, with the literal quotient marking and
generation of the two original intersections. -/
theorem PreExclusionSource.constrained_binary_four
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* SL(4,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(4,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      (M ⊓ d.L) ⊔ d.ML = d.L ∧ d.ConstrainedAlternatives := by
  obtain ⟨t,ht,hML,hM',a,ha,⟨b⟩⟩ :=
    s.constrained_binary_nodes (h := h) hG hempty hM hJ hu hf (Or.inl rfl) e
  have hg : (M ⊓ d.L) ⊔ d.ML = d.L := by
    rcases b.action with hi | ⟨ho,_⟩
    · exact s.binary_inner_generated (h := h) hG hM hJ hu hf (by decide) b hi.1
    · exact s.binary_four_graph_generated (h := h) hG hM hJ hu hf b ho
  exact ⟨t,ht,hML,hM',hg,ConstrainedAlternatives.linear 4 (Or.inl rfl) t hML hM' hg⟩

/-- The surviving binary FF rows have the full constrained linear conclusion,
including generation and both parabolics under the same original marking. -/
theorem PreExclusionSource.constrained_binary_linear
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    {n : ℕ} (hn : n=4 ∨ n=5) (e : d.normalizerImage d.L ≃* SL(n,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      (M ⊓ d.L) ⊔ d.ML = d.L ∧ d.ConstrainedAlternatives := by
  rcases hn with rfl | rfl
  · exact s.constrained_binary_four (h := h) hG hempty hM hJ hu hf e
  · exact s.constrained_binary_five (h := h) hG hempty hM hJ hu hf e

/-- Later exchanged selection consumes both actual source parabolics in the
degree-four graph branch, with the original quotient marking and seed. -/
theorem ExchangedSource.constrained_binary_four_graph_parabolics
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* SL(4,ZMod 2)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(4,ZMod 2),
      (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ a : d.BinaryGeneratingParabolics t, ∃ b : d.BinaryNodeGeometry a,
        d.IsSourceParabolic a.interior ∧
          ((∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
            d.IsSourceParabolic a.endpoint) := by
  obtain ⟨t,ht,hML,hM',a,ha,⟨b⟩⟩ :=
    s.constrained_binary_nodes hG hempty hM hJ hu h hf (Or.inl rfl) e
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  refine ⟨t,ht,hML,hM',a,b,b.four_interior_source_parabolic hK,?_⟩
  rcases b.action with hi | ⟨ho,_⟩
  · exact Or.inl hi.1
  · exact Or.inr (b.four_graph_endpoint_source_parabolic hK hf ho)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open BinaryLinear.InvariantNodeActions
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker receives the full degree-four and degree-five linear alternatives for
both original primes. Original 15.1.14 remains explicit for its independent
producer and the final source assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_linear
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
        ∀ (n : ℕ), n=4 ∨ n=5 → ∀ e : d.normalizerImage d.L ≃* SL(n,ZMod 2),
        ∃ t : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2),
          (∀ x : d.L, t (QuotientGroup.mk' (pCore 2 d.L) x) = e (d.toNormalizerImage d.L x)) ∧
          d.ConstrainedLinearParabolic t d.ML ∧
          d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
          (M ⊓ d.L) ⊔ d.ML = d.L ∧ d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf n hn e =>
    s.constrained_binary_linear (h := h) hG hempty hM hJ hu hf hn e⟩
end CFSG.Quasithin.Chapter15.Section01
