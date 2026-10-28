module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components.Classification
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Layer
public import Theory.GroupTheory.GeneralizedFitting.CentralizerLayerContainment
public import Theory.SpecificGroups.PSL2.PerfectCentralizerComparison
public import Theory.GroupAction.CubicInnerShift
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer

/-!
# Component comparison in the actual G₂ cover sections

A faithful cubic forces each ordinary component to be a prime-field PSL₂.
The source I.3.1 ordinary-layer theorem lifts a hyperplane component into a
smaller section centralizer. Its Sylow centralization puts it inside a single
component, and the exact PSL₂ embedding comparison identifies the two.
Two components of the smaller section would give excess three-rank together
with the same faithful cubic, so this component is unique.

These are the two symmetric applications used to compare K and K conjugated
by a cubic-normalizing mover; no square condition on that mover is needed.
Source: Aschbacher--Smith, 12.4.8, printed p.815, I.3.1 and A.3.18.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {V U U₀ : Subgroup G}

private theorem fermatMersenne_odd {p : ℕ} (hp : IsFermatOrMersennePrime p) : Odd p := by
  apply hp.1.odd_of_ne_two
  rintro rfl
  rcases hp.2 with ⟨a,ha⟩ | ⟨a,ha⟩
  · have hlow : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
    omega
  · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
    omega

omit [Finite G] in
private theorem component_in_subspace_normalizer {K A : Subgroup G}
    (hK : IsComponentIn K (centralizer (A : Set G))) :
    IsComponentIn K (normalizer (A : Set G)) := by
  let := normal_subgroupOf_centralizer_normalizer (A : Set G)
  exact hK.of_subnormal (Subgroup.centralizer_le_normalizer _)
    (inferInstance : ((centralizer (A : Set G)).subgroupOf
      (normalizer (A : Set G))).Normal).isSubnormal

/-- The actual plane centralizer has at most one ordinary component. -/
theorem LocalData.component_unique (c : LocalData T V U₀)
    {K J : Subgroup G}
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
  let _ := c.hypothesisE.elementary
  let _ : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_le c.member.1
  have hN : IsSQTK KnownSimple.IsKnownSimple N := c.hypothesisE.simpleQTKE.twoLocal_sqtk
    ⟨U₀,c.member.2.1,IsElementaryAbelian.isPGroup 2 U₀,rfl⟩
  have hfacts (D : Subgroup G) (hD : IsComponentIn D (centralizer (U₀ : Set G)))
      (hDN : D ≤ N) : center (D.subgroupOf N) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (D.subgroupOf N)) ∧ 1 ≤ primeRank 3 (D.subgroupOf N) := by
    obtain ⟨p,hp,F,_,_,hF,⟨e⟩⟩ := c.component_fermatMersenne hD hx hxN hxC
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
theorem LocalData.component_in_section_centralizer
    (c : LocalData T V U) (d : LocalData T V U₀)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    (hU₀U : U₀ ≤ U)
    (hS : Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
      (centralizer (U₀ : Set G)))
    {x : G} (hx : orderOf x = 3) (hxN : x ∈ normalizer (U₀ : Set G))
    (hxC : x ∉ centralizer (U₀ : Set G))
    (hxU : x ∈ normalizer (U : Set G)) :
    IsComponentIn K (centralizer (U₀ : Set G)) := by
  let _ := c.hypothesisE.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.member.1
  let H := centralizer (U₀ : Set G)
  have hUH : U ≤ H := by
    intro u hu v hv
    exact congrArg V.subtype (mul_comm (⟨v,c.member.1 (hU₀U hv)⟩ : V) ⟨u,c.member.1 hu⟩)
  obtain ⟨p,hp,hm⟩ := c.component_fermatMersenne hK hx hxU
    (fun hc => hxC ((centralizer_le hU₀U) hc))
  have hlayer :=
    (SLThreeCommutatorSource.CentralizerBound.seed_layer_of_fermatMersenne
      c.hypothesisE.simpleQTKE U U₀ K (IsElementaryAbelian.isPGroup 2 U)
      hU₀U d.member.2.1 hK hp hm).2
  obtain ⟨S,hS⟩ := hS
  have hUS : U ≤ centralizer ((S : Subgroup H).map H.subtype : Set G) := by
    rw [hS]
    intro u hu q hq
    exact (hq.2 u (c.member.1 hu)).symm
  obtain ⟨J,hJ,hKJ,hUJ⟩ :=
    hK.exists_containing_component_of_centralizes_sylow hUH hlayer S hUS
  obtain ⟨p,hp,hmodel⟩ := d.component_fermatMersenne hJ hx hxN hxC
  obtain ⟨F,hfield,hfinite,hF,⟨eJ⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp.1⟩
  have hp3 : p ≠ 3 := by
    intro he
    let := hJ.quasisimple
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
      (hF.trans he) inferInstance
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) (fermatMersenne_odd hp)
  have hplarge : 3 < p := by have := hp.1.two_le; omega
  have he := Theory.PSL2.component_eq_of_normalized_prime_model hU₀U hK hJ hKJ hUJ
    hplarge hF eJ
  exact he.symm ▸ hJ


end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components
