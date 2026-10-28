module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.ConjugatorGeometry
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Components.PlaneModels
public import Theory.GroupTheory.GeneralizedFitting.CentralizerLayerContainment
public import Theory.SpecificGroups.PSL2.PerfectCentralizerComparison

/-!
# Comparison with the containing plane-centralizer component

The original hyperplane centralizes a full Sylow two-subgroup of the plane
centralizer. Hence its component orbit consists of one component, normalized
by the hyperplane. The same faithful cubic gives the containing component a
prime-field PSL₂ model. The perfect-centralizer comparison makes the whole
containing component centralize the hyperplane, and component maximality gives
equality. All groups remain embedded by the original centralizer subtype.
Source: Aschbacher--Smith A.3.12(8), applied in 12.4.8, printed p.815.
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

/-- The source seed is itself an ordinary component of the plane centralizer,
not just a subgroup of its layer or an abstract model of a component. -/
theorem Configuration.component_in_plane_centralizer (c : Configuration T L V U)
    {K U₀ : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1)
    {x : G} (hx : orderOf x = 3) (hxN : x ∈ normalizer (U₀ : Set G))
    (hxC : x ∉ centralizer (U₀ : Set G)) :
    IsComponentIn K (centralizer (U₀ : Set G)) := by
  let _ := c.chosen.elementary
  let H := centralizer (U₀ : Set G)
  have hU₀ne : U₀ ≠ ⊥ := by
    intro he
    have hc := ((escaping_subspaces c.hypothesis c.structural c.extension
      c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.2 U₀ hU₀U hcor).1
    norm_num [he] at hc
  have hUH : U ≤ H := by
    intro u hu v hv
    exact congrArg V.subtype (mul_comm (⟨v,c.le_module (hU₀U hv)⟩ : V) ⟨u,c.le_module hu⟩)
  have hlayer := (c.component_le_plane_layer hK U₀ hU₀U hU₀ne).2
  obtain ⟨S,hS⟩ := c.sylow_centralizers.2 U₀ hU₀U hcor
  have hUS : U ≤ centralizer ((S : Subgroup H).map H.subtype : Set G) := by
    rw [hS]
    intro u hu q hq
    exact (hq.2 u (c.le_module hu)).symm
  obtain ⟨J,hJ,hKJ,hUJ⟩ :=
    hK.exists_containing_component_of_centralizes_sylow hUH hlayer S hUS
  obtain ⟨p,hp,hmodel⟩ := c.plane_component_fermatMersenne hU₀U hcor hJ hx hxN hxC
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

/-- The actual plane constructed with the original conjugator retains K as
an ordinary component, through the same cubic action used in model reduction. -/
theorem Configuration.component_in_conjugate_plane_centralizer (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    {l x : G} (hl : l ∈ L) (hm : l ∉ normalizer (U : Set G))
    (hsq : l ^ 2 ∈ normalizer (U : Set G))
    (hxL : x ∈ L) (hx : orderOf x = 3) (hxN : x ∈ normalizer (U : Set G))
    (hxC : x ∉ centralizer (U : Set G)) (hlX : l ∈ normalizer (zpowers x : Set G)) :
    IsComponentIn K (centralizer (U ⊓ U.map (MulAut.conj l).toMonoidHom : Set G)) := by
  have hg := c.conjugate_plane_geometry hl hm hsq
  have ha := c.cubic_on_conjugate_plane hl hm hsq hxL hxN hxC hlX
  exact c.component_in_plane_centralizer hK inf_le_left hg.2.2.1 hx ha.1 ha.2
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
