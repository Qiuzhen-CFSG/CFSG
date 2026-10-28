module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.CubicAction
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.ModelAlternatives
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound.Components.Preparation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The ordinary PSL₂ seed in the original L₃ centralizer argument

This is the same-G,T version of the corresponding CentralizerBound proof.
Its configuration carries only Structural1222At at the original Sylow;
every subgroup, action and relative component map is unchanged.

The chosen module constructs a faithful order-three subgroup of N_L(U).
The centralizer C_G(U) is normal in N_G(U), so its ordinary component is
still a component in that literal two-local normalizer. The full E.6.8
model list and the proved A.3.18 specializations force every cubic into
any remaining rank-two component, contradicting its nontrivial action on U.
Thus the component is PSL₂(p), for a Fermat or Mersenne prime p.

The final application removes the model premise from the existing ordinary
layer theorem for C_G(U₀). The later conjugator comparison and component
exclusion remain with their source owners; they are not assumed here.
Source: Aschbacher–Smith, Lemma 12.4.8, printed p.815 (`refs/quasithin.pdf`).
-/

public section
open CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels.AlternatingCubics
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The source actor as a literal subgroup of order three, with its faithful
conjugation homomorphism on U. -/
theorem Configuration.exists_faithful_cubic_subgroup (c : Configuration T L V U) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X = 3 ∧
      ∃ hXU : X ≤ normalizer (U : Set G),
        Function.Injective (U.normalizerMonoidHom.comp (inclusion hXU)) := by
  obtain ⟨x,hxL,hx,hxN,hxU⟩ := c.exists_cubic_hyperplane_actor
  let X := zpowers x
  have hc : Nat.card X = 3 := (Nat.card_zpowers x).trans hx
  have hn : X ≤ normalizer (U : Set G) := zpowers_le.mpr hxN
  refine ⟨X,zpowers_le.mpr hxL,hc,hn,?_⟩
  let f := U.normalizerMonoidHom.comp (inclusion hn)
  let : Fact (Nat.card X).Prime := ⟨hc ▸ Nat.prime_three⟩
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases f.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · have he : f ⟨x,mem_zpowers x⟩ = 1 := by
      exact (show (⟨x,mem_zpowers x⟩ : X) ∈ f.ker from h ▸ mem_top _)
    apply (hxU ?_).elim
    intro u hu
    have hh := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : G)) he
    change x * u * x⁻¹ = u at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The normalizer used in A.3.18 is a genuine two-local subgroup. -/
theorem Configuration.hyperplane_normalizer_sqtk (c : Configuration T L V U) :
    IsSQTK KnownSimple.IsKnownSimple (normalizer (U : Set G)) := by
  let _ := c.chosen.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le c.le_module
  have hn : U ≠ ⊥ := by
    intro he
    have hc := hyperplane_card c.extension c.fixed_nontrivial c.le_module c.corank
    rw [he,card_bot] at hc
    omega
  exact c.hypothesis.simpleQTKE.twoLocal_sqtk
    ⟨U,hn,IsElementaryAbelian.isPGroup 2 U,rfl⟩

omit [Finite G] in
/-- Subnormal ascent to N_G(U) preserves the literal ordinary component. -/
private theorem component_in_subspace_normalizer {K : Subgroup G}
    (hK : IsComponentIn K (centralizer (U : Set G))) :
    IsComponentIn K (normalizer (U : Set G)) := by
  let := normal_subgroupOf_centralizer_normalizer (U : Set G)
  exact hK.of_subnormal (Subgroup.centralizer_le_normalizer _)
    (inferInstance : ((centralizer (U : Set G)).subgroupOf
      (normalizer (U : Set G))).Normal).isSubnormal

/-- E.6.8 and the actual faithful cubic actor leave precisely the
Fermat/Mersenne PSL₂ seed of the ordinary-component branch of 12.4.8. -/
theorem Configuration.component_fermatMersenne (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G))) :
    ∃ p, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL K 2 p := by
  let N := normalizer (U : Set G)
  have hKN := component_in_subspace_normalizer hK
  let J := K.subgroupOf N
  let e : J ≃* K := subgroupOfEquivOfLe hKN.1
  have hJ : IsComponent N J := hKN.2
  have hN := c.hyperplane_normalizer_sqtk
  have hr : primeRank 3 N ≤ 2 := hN.stronglyQuasithin 3 Nat.prime_three (by decide)
  obtain ⟨x,hxL,hx,hxN,hxU⟩ := c.exists_cubic_hyperplane_actor
  let a : N := ⟨x,hxN⟩
  have ha : orderOf a = 3 := (orderOf_coe a).symm.trans hx
  have hnot : a ∉ J := fun haJ => hxU (hK.1 haJ)
  rcases c.component_model_list hK with hm | hm | hm | hm | hm | hm
  · exact hm
  · exact (hnot (cubic_mem_of_alternating_component hJ (by decide : 6 ≤ 6)
      ⟨e.trans hm.some⟩ hr ha)).elim
  · obtain ⟨F,_,_,hc,⟨d⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc
    let d' := ((e.trans d).trans (Atlas.fieldEquivPSL 4 (FiniteField.ringEquivOfCardEq hcard))).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    exact (hnot (cubic_mem_of_alternating_component hJ (by decide : 6 ≤ 8) ⟨d'⟩ hr ha)).elim
  · rcases hm with hm | hm
    · exact (hnot (cubic_mem_of_alternating_component hJ (by decide : 6 ≤ 7)
        ⟨e.trans hm.some⟩ hr ha)).elim
    · exact (hnot (cubic_mem_of_alternating_cover_component hJ e hm hr ha)).elim
  · obtain ⟨F,_,_,hc,⟨d⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
      simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc
    let d' := (e.trans d).trans (Atlas.fieldEquivPSL 3 (FiniteField.ringEquivOfCardEq hcard))
    have he := (ChapterA.Section03.OddPrime.SourceModels.SmallComponents.component_eq_cubic_residual
      hN hJ (Or.inl ⟨d'⟩)).2
    apply (hnot ?_).elim
    rw [he]
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one,ha] using pow_orderOf_eq_one a
  · have he := (ChapterA.Section03.OddPrime.SourceModels.SmallComponents.component_eq_cubic_residual
      hN hJ (Or.inr ⟨e.trans hm.some⟩)).2
    apply (hnot ?_).elim
    rw [he]
    apply mem_primeToResidual_of_pow (n := 1)
    simpa only [pow_one,ha] using pow_orderOf_eq_one a

/-- The model reduction discharges the exact model premise in the existing
ordinary-layer consumer, with the original embedded component and plane. -/
theorem Configuration.component_le_plane_layer (c : Configuration T L V U)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer (U : Set G)))
    (U₀ : Subgroup G) (hU₀U : U₀ ≤ U) (hU₀ : U₀ ≠ ⊥) :
    IsSQTK KnownSimple.IsKnownSimple (centralizer (U₀ : Set G)) ∧
      K ≤ (componentLayer (centralizer (U₀ : Set G))).map
        (centralizer (U₀ : Set G)).subtype := by
  obtain ⟨p,hp,hm⟩ := c.component_fermatMersenne hK
  exact c.seed_layer_of_fermatMersenne K hK U₀ hU₀U hU₀ hp hm

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.At.CentralizerBound
