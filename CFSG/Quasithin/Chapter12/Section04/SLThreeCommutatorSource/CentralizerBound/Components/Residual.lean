module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.PlaneModels
public import Theory.GroupAction.CubicInnerShift
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.Comparison

/-!
# The plane-centralizer component and its three-residual

Every component has a prime-field PSL₂ model, with trivial center, two-group
outer automorphism group, and nontrivial three-rank. Each is a component of the
plane normalizer and is normalized by the faithful cubic. Two distinct ones
commute, so the rank-two obstruction would put the cubic inside their join,
which centralizes the plane. This contradicts its faithful plane action.
Uniqueness identifies the whole ordinary layer; its centerless quasisimple
model has order divisible by three, so its prime-to-three residual is the
whole layer. The concluding equality retains both original subtype maps.
Source: Aschbacher--Smith 12.4.8, printed p.815.
-/
public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a,ha⟩ | ⟨a,ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

/-- Model facts actually used by the three-rank and residual arguments. -/
theorem Configuration.plane_component_center_outer_three (c : Configuration T L V U)
    {K U₀ : Subgroup G} (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
    (hK : IsComponentIn K (centralizer (U₀ : Set G)))
    {x : G} (hx : orderOf x = 3) (hxN : x ∈ normalizer (U₀ : Set G))
    (hxC : x ∉ centralizer (U₀ : Set G)) :
    center K = ⊥ ∧ IsPGroup 2 (MulAut.Outer K) ∧
      1 ≤ primeRank 3 K ∧ 3 ∣ Nat.card K := by
  obtain ⟨p,hp,F,_,_,hF,⟨e⟩⟩ := c.plane_component_fermatMersenne hU₀U hcor hK hx hxN hxC
  have ho := fermatMersenne_odd hp
  obtain ⟨hz,hout⟩ := Theory.PSL2.primeField_center_outer_of_equiv hp.1 ho hF e
  exact ⟨hz,hout,Theory.PSL2.prime_model_three_rank_pos hp.1 ho hF e,
    Theory.PSL2.prime_model_three_dvd_card hp.1 ho hF e⟩

omit [Finite G] in
private theorem component_in_subspace_normalizer {K A : Subgroup G}
    (hK : IsComponentIn K (centralizer (A : Set G))) :
    IsComponentIn K (normalizer (A : Set G)) := by
  let := normal_subgroupOf_centralizer_normalizer (A : Set G)
  exact hK.of_subnormal (Subgroup.centralizer_le_normalizer _)
    (inferInstance : ((centralizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))).Normal).isSubnormal

/-- The actual plane centralizer has at most one ordinary component. -/
theorem Configuration.plane_component_unique (c : Configuration T L V U)
    {K J U₀ : Subgroup G} (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
    (hK : IsComponentIn K (centralizer (U₀ : Set G)))
    (hJ : IsComponentIn J (centralizer (U₀ : Set G)))
    {x : G} (hx : orderOf x = 3) (hxN : x ∈ normalizer (U₀ : Set G))
    (hxC : x ∉ centralizer (U₀ : Set G)) : K = J := by
  by_contra hne
  let N := normalizer (U₀ : Set G)
  let K' := K.subgroupOf N
  let J' := J.subgroupOf N
  have hKN := component_in_subspace_normalizer hK
  have hJN := component_in_subspace_normalizer hJ
  let eK : K' ≃* K := subgroupOfEquivOfLe hKN.1
  let eJ : J' ≃* J := subgroupOfEquivOfLe hJN.1
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_le (hU₀U.trans c.le_module)
  have hg := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 U₀ hU₀U hcor
  have hn : U₀ ≠ ⊥ := by intro he; have hc := hg.1; rw [he,card_bot] at hc; omega
  have hN : IsSQTK KnownSimple.IsKnownSimple N := c.hypothesis.simpleQTKE.twoLocal_sqtk
    ⟨U₀,hn,IsElementaryAbelian.isPGroup 2 U₀,rfl⟩
  have hfacts (D : Subgroup G) (hD : IsComponentIn D (centralizer (U₀ : Set G)))
      (hDN : D ≤ N) : center (D.subgroupOf N) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (D.subgroupOf N)) ∧ 1 ≤ primeRank 3 (D.subgroupOf N) := by
    obtain ⟨p,hp,F,_,_,hF,⟨e⟩⟩ := c.plane_component_fermatMersenne hU₀U hcor hD hx hxN hxC
    let d := (subgroupOfEquivOfLe hDN).trans e
    have ho := fermatMersenne_odd hp
    obtain ⟨hz,hout⟩ := Theory.PSL2.primeField_center_outer_of_equiv hp.1 ho hF d
    exact ⟨hz,hout,Theory.PSL2.prime_model_three_rank_pos hp.1 ho hF d⟩
  obtain ⟨hzK,houtK,hrK⟩ := hfacts K hK hKN.1
  obtain ⟨hzJ,houtJ,hrJ⟩ := hfacts J hJ hJN.1
  have hcomm : K' ≤ centralizer (J' : Set N) := by
    intro k hk j hj
    exact Subtype.ext (commutator_eq_bot_iff_le_centralizer.mp
      (hK.commutator_eq_bot_of_ne hJ hne) hk j hj)
  let a : N := ⟨x,hxN⟩
  have ha : a ^ 3 = 1 := Subtype.ext (by rw [←hx]; exact pow_orderOf_eq_one x)
  have haK := hKN.2.cubic_normalizes hN.stronglyQuasithin ha
  have haJ := hJN.2.cubic_normalizes hN.stronglyQuasithin ha
  have hmem := Theory.GroupAction.cubic_mem_join_of_commuting_centerless K' J'
    hzK hzJ houtK houtJ hcomm hrK hrJ
    (hN.stronglyQuasithin 3 Nat.prime_three (by decide)) haK haJ ha
  have hle : K' ⊔ J' ≤ (centralizer (U₀ : Set G)).subgroupOf N :=
    sup_le (fun _ hk => hK.1 hk) (fun _ hj => hJ.1 hj)
  exact hxC (hle hmem)
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The residual equality retains both literal subtype maps and the original
component; all comparison and rank hypotheses are discharged from c. -/
theorem Configuration.component_eq_plane_layer_residual (c : Configuration T L V U)
    {K U₀ : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
    {x : G} (hx : orderOf x = 3) (hxN : x ∈ normalizer (U₀ : Set G))
    (hxC : x ∉ centralizer (U₀ : Set G)) :
    K = ((primeToResidual 3 (componentLayer (centralizer (U₀ : Set G)))).map
      (componentLayer (centralizer (U₀ : Set G))).subtype).map
        (centralizer (U₀ : Set G)).subtype := by
  let H := centralizer (U₀ : Set G)
  have hK₀ := c.component_in_plane_centralizer hK hU₀U hcor hx hxN hxC
  have hE : componentLayer H = K.subgroupOf H := by
    apply le_antisymm _ (show K.subgroupOf H ≤ componentLayer H from le_sSup hK₀.2)
    apply sSup_le
    intro J hJ
    have hJ' : IsComponentIn (J.map H.subtype) H := by
      refine ⟨map_subtype_le _,?_⟩
      rwa [show (J.map H.subtype).subgroupOf H = J from
        comap_map_eq_self_of_injective H.subtype_injective J]
    have he := c.plane_component_unique hU₀U hcor hJ' hK₀ hx hxN hxC
    intro j hj
    exact he ▸ mem_map_of_mem H.subtype hj
  obtain ⟨hz,_,_,hd⟩ := c.plane_component_center_outer_three hU₀U hcor hK₀ hx hxN hxC
  let := hK.quasisimple
  have hR : primeToResidual 3 K = ⊤ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (primeToResidual 3 K) with hc | ht
    · have hb : primeToResidual 3 K = ⊥ := le_bot_iff.mp (hc.trans_eq hz)
      have hcop := primeToResidual_index_coprime (G := K) 3
      rw [hb,index_bot] at hcop
      exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop hd).elim
    · exact ht
  change K = ((primeToResidual 3 (componentLayer H)).map (componentLayer H).subtype).map H.subtype
  rw [hE]
  have hm := congrArg (Subgroup.map K.subtype)
    (map_primeToResidual (p := 3) (subgroupOfEquivOfLe hK₀.1))
  rw [hR,←MonoidHom.range_eq_map,range_subtype] at hm
  have hf : K.subtype.comp (subgroupOfEquivOfLe hK₀.1).toMonoidHom =
      H.subtype.comp (K.subgroupOf H).subtype := by
    ext k
    rfl
  simpa only [map_map,hf] using hm.symm
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
