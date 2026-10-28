module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.CoreImage
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.PrimeTo
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.RankReduction.Models
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# Three-rank and model reduction for an external component

Suppose H = KL₁T, K is a relatively normal C-component, and L₁ is not
contained in K. The earlier identity L₁ = θ(H ∩ M) reduces containment to
order-three elements. For every quotient on the input list except L₃(2),
the proved centerless-component index theorem makes |H:K| prime to three.
Every theta generator must then belong to K, a contradiction. The remaining
quotient is L₃(2); its order gives three-rank one, and the two-core kernel
comparison produces the actual equivalence K* ≃ L₃(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.21(1),
printed p.956, the paragraph beginning “We next prove (1)”. This uses the
source normality 13.8.16(1) and theta identity 13.7.3(9), uniformly for the
ordinary and triple-cover A₆ cases. `primeToResidual` below is O^{3′}, never
O₃ or O³, and all component assertions are relative to H.

The exact list 13.8.21(2) is an input. The proved full-group conjugation
coverage of the concrete G₂(2)' discharges its outer-order premise in
`rank_one_and_model` and `starEquiv`. Thus these assembled reductions need
only the displayed earlier-source setup and the input list, in either A₆
branch. The older conditional model interfaces are preserved. Ordinary
centralization, action geometry and the final containment L₁ ≤ K belong to
the parent external-component action task.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.RankReduction
/-- Normalize the binary fields in the earlier source list through actual
entrywise projective matrix equivalences. This accepts the same linear
predicate as the component list used by the later Section 13.8 consumers. -/
theorem smallQuotient_of_source_list {A : Type*} [Group A]
    (h : (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL A n 2) ∨
      Nonempty (A ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (A ≃* commutator (Atlas.G2.Model (ZMod 2)))) : SmallQuotient A := by
  rcases h with ⟨n, hn, hn', F, hF, hfin, hcard, ⟨e⟩⟩ | h
  · let := hF
    let := hfin
    exact Or.inl ⟨n, hn, hn', ⟨e.trans (Atlas.fieldEquivPSL n
      (Atlas.G2.binaryFieldEquiv hcard))⟩⟩
  · exact Or.inr h

universe u
variable {G : Type u} [Group G] [Finite G]
/-- The standing local setup and only the earlier conclusions consumed here.
`normal` is 13.8.16(1), relative to H; `theta` is 13.7.3(9). The latter holds
for both L/O₂(L) ≃ A₆ and L/O₂(L) ≃ Â₆, so no restriction to either branch
is imposed. The Sylow subgroup and the literal source family are retained. -/
structure SourceSetup (κ : GroupClass.{u}) (H K L₁ M G₁ : Subgroup G)
    (T : Sylow 2 G) : Prop where
  sqtk : IsSQTK κ H
  local_overgroup : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M
  generated : K ⊔ L₁ ⊔ (T : Subgroup G) = H
  component : (K.subgroupOf H).IsCComponent
  normal : (K.subgroupOf H).Normal
  external : ¬ K ≤ M
  theta : L₁ = closure {x | x ∈ H ⊓ M ∧ orderOf x = 3}

variable {κ : GroupClass.{u}} {H K L₁ M G₁ : Subgroup G} {T : Sylow 2 G}
omit [Finite G] in
private theorem component_le (d : SourceSetup κ H K L₁ M G₁ T) : K ≤ H := by
  rw [← d.generated]
  exact le_sup_left.trans le_sup_left

/-- The direct ordinary-index argument behind the use of A.3.18. A rank-two,
centerless component quotient with three-prime outer order forces every
order-three generator of the actual H ∩ M into K. This is a conditional
model-independent deduction, not an assumption of source containment. -/
theorem theta_le_component_of_model_facts (d : SourceSetup κ H K L₁ M G₁ T)
    (hz : center (K ⧸ pCore 2 K) = ⊥)
    (hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K))
    (ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K)))) : L₁ ≤ K := by
  let D := K.subgroupOf H
  let e := QuotientGroup.congr (pCore 2 D) (pCore 2 K)
    (subgroupOfEquivOfLe (component_le d)) (pCore_map_iso 2 _)
  have hzD : center (D ⧸ pCore 2 D) = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz'
    have he := (centerCongr e ⟨z,hz'⟩).property
    change e z ∈ center (K ⧸ pCore 2 K) at he
    rw [hz, mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hrD : 2 ≤ primeRank 3 (D ⧸ pCore 2 D) := by rwa [primeRank_congr 3 e]
  have hoD : Nat.Coprime 3 (Nat.card (MulAut.Outer (D ⧸ pCore 2 D))) := by
    rwa [Nat.card_congr (MulAut.outerCongr e).toEquiv]
  let : D.Normal := d.normal
  have hi := cComponent_index_coprime_three_of_quotient D d.component hzD hrD
    (d.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide)) hoD
  rw [d.theta, closure_le]
  intro x hx
  have hp : (⟨x,hx.1.1⟩ : H) ^ (3 ^ 1) = 1 := by
    apply Subtype.ext
    simpa [hx.2] using pow_orderOf_eq_one x
  exact primeToResidual_le D hi (mem_primeToResidual_of_pow hp)

private theorem rank_of_quotient
    (hr : primeRank 3 Matrix.PSL3Two.PSL = 1)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL) : primeRank 3 K = 1 := by
  have hq : primeRank 3 (K ⧸ pCore 2 K) = 1 := (primeRank_congr 3 e).trans hr
  have hc : Nat.Coprime 3 (Nat.card (pCore 2 K)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hz : primeRank 3 (pCore 2 K) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  have hl := primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup
  have hu := primeRank_le_ker_add (p := 3) (QuotientGroup.mk' (pCore 2 K))
  rw [QuotientGroup.ker_mk', hz, hq] at hu
  rw [hq] at hl
  omega

open Atlas.G2.LieAutomorphismExtensions

/-- The external-component reduction with the minimal explicit model
input: the outer order of the actual G₂(2)' is prime to three. All other
model facts, the rank lift, and the equivalence on the literal star image
are proved here. This statement treats both source A₆ branches uniformly. -/
theorem rank_one_and_model_of_outer_coprime
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : SmallQuotient (K ⧸ pCore 2 K))
    (houter : Nat.Coprime 3 (Nat.card (MulAut.Outer BinaryDerived))) :
    primeRank 3 K = 1 ∧ Nonempty (Source.starImage H K ≃* Matrix.PSL3Two.PSL) := by
  rcases small_quotient_alternative_of_outer_coprime houter models with hmodel | hfacts
  · obtain ⟨e⟩ := hmodel
    exact ⟨rank_of_quotient rank_psl3 e,
      ⟨(quotientStarEquiv H K (component_le d) d.component.subnormal).symm.trans e⟩⟩
  · exact False.elim (hout (theta_le_component_of_model_facts d hfacts.1 hfacts.2.1 hfacts.2.2))

/-- With L₁ outside K, the exact list leaves only the actual L₃(2) quotient.
The G₂ automorphism premise is intrinsic to that fixed concrete carrier;
it asserts neither source containment nor a rank bound. -/
theorem quotient_model_of_external
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : SmallQuotient (K ⧸ pCore 2 K))
    (hcover : Function.Surjective binaryConjugation) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL) := by
  rcases small_quotient_alternative hcover models with h | ⟨hz,hr,ho⟩
  · exact h
  · exact False.elim (hout (theta_le_component_of_model_facts d hz hr ho))

/-- Construct the equivalence on the literal image in H/O₂(H), using the
proved intrinsic kernel calculation in `CoreImage`. Relative component
subnormality suffices; no ambient normality or quotient identification is
silently assumed. -/
noncomputable def starEquiv_of_coverage
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : SmallQuotient (K ⧸ pCore 2 K))
    (hcover : Function.Surjective binaryConjugation) :
    Source.starImage H K ≃* Matrix.PSL3Two.PSL :=
  (quotientStarEquiv H K (component_le d) d.component.subnormal).symm.trans
    (Classical.choice (quotient_model_of_external d hout models hcover))

/-- The conditional first external-component reduction of 13.8.21(1),
retaining intrinsic G₂(2)' automorphism coverage as an explicit parameter.
It applies in both A₆ and Â₆ source branches. The assembled theorem
`rank_one_and_model` below discharges this model premise. -/
theorem rank_one_and_model_of_coverage
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : SmallQuotient (K ⧸ pCore 2 K))
    (hcover : Function.Surjective binaryConjugation) :
    primeRank 3 K = 1 ∧ Nonempty (Source.starImage H K ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨e⟩ := quotient_model_of_external d hout models hcover
  exact ⟨rank_of_quotient rank_psl3 e, ⟨starEquiv_of_coverage d hout models hcover⟩⟩

/-- The first external-component reduction on printed p.956: the genuine
earlier setup and exact list force three-rank one and the actual L₃(2)
star image. The proved conjugation coverage of the octonion-derived G₂(2)'
discharges the last intrinsic model premise. No A.3.18 specialization or
additional rank, containment or automorphism assumption remains. -/
theorem rank_one_and_model
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : SmallQuotient (K ⧸ pCore 2 K)) :
    primeRank 3 K = 1 ∧ Nonempty (Source.starImage H K ≃* Matrix.PSL3Two.PSL) :=
  rank_one_and_model_of_coverage d hout models binaryConjugation_surjective

/-- An actual multiplicative equivalence for the parent action construction,
with the G₂ model premise discharged. Its domain is the literal image of K
in H/O₂(H), identified with K/O₂(K) by the intrinsic kernel calculation. -/
noncomputable def starEquiv
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : SmallQuotient (K ⧸ pCore 2 K)) :
    Source.starImage H K ≃* Matrix.PSL3Two.PSL :=
  starEquiv_of_coverage d hout models binaryConjugation_surjective

/-- Apply the reduction directly to the source list with arbitrary binary
fields in its linear entries. Each entry is an actual model equivalence;
`smallQuotient_of_source_list` transports those fields to ZMod 2. -/
theorem rank_one_and_model_of_source_list
    (d : SourceSetup κ H K L₁ M G₁ T) (hout : ¬ L₁ ≤ K)
    (models : (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    primeRank 3 K = 1 ∧ Nonempty (Source.starImage H K ≃* Matrix.PSL3Two.PSL) :=
  rank_one_and_model d hout (smallQuotient_of_source_list models)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalComponentAction.RankReduction
