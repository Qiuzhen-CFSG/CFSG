module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.CoveredSource
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918.Actors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OrdinaryAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Inverter
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.DualBounds
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility

/-!
# Original ordinary A₆ containment and the field-sieve consumers

The marked ordinary local action supplies an element of T inverting the
cubic quotient of L₁. Cubes vanish in that quotient, and inversion puts
squares in [L₁,T]O₂(L₁); two-perfectness then gives [L₁,T] = L₁.
The earlier residual and solvable-overgroup theorems supply the Fitting
alternative and component quasisimplicity. F.9 constructs the faithful
literal U_H/V₁ action and its quadratic actor. The Steinberg dimension bound
and the combined natural/dual offender bound discharge the paired-module
exclusion, proving L₁ ≤ K in the ordinary local case.

Combining this with the covered comparison gives H = KT and U_H = [U_H,K]
for either local quotient. The concrete catalogue sieve feeds these same
consumers, and the whole-quotient exclusion supplies the binary automorphism
clause. The remaining list, or the field and cover exclusions producing it,
remains explicit. The generated-overgroup reduction H = KL₁T is the one
in SourceContext; passage to arbitrary H is not asserted here.

The field-sieve owner qt-d-138-fields-source retains the exclusions and
unrestricted-overgroup assembly. The original section owner qt-d-1381-source
supplies the earlier SourceContext, including the component catalogue.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(1),(3),(4), printed pp.956–957, using 13.8.13–18, pp.950–953.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
open LinearThree LinearThree.Geometry LinearThree.Geometry.ExternalComponentAction
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open HigherFieldReduction.LocalBorel.CentralizingCalculation
open SourceCompletion

private theorem cubic_inversion_commutator {G : Type*} [Group G] [Finite G]
    (X T : Subgroup G) (hp : IsPPerfect 2 X)
    (hn : T ≤ normalizer (X : Set G))
    (hc : Nat.card (X ⧸ pCore 2 X) = 3)
    (t : G) (ht : t ∈ T) (hi : InvertsTwoCoreQuotient X t) : ⁅X,T⁆ = X := by
  let C := ⁅X,T⁆
  have hCX : C ≤ X := le_normalizer_iff_commutator_le_left.mp hn
  let N := C.subgroupOf X
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hCX).mpr
    (normalizer_commutator_ge_left X T)
  have hsup : (⊤ : Subgroup X) ≤ N ⊔ pCore 2 X := by
    intro x _
    have h3 : x ^ 3 ∈ pCore 2 X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (pCore 2 X) x) ^ 3 = 1
      rw [← hc]
      exact pow_card_eq_one'
    have hinv : (⟨t * (x:G) * t⁻¹ * (x:G), X.mul_mem
      ((mem_normalizer_iff.mp (hn ht) x).mp x.property) x.property⟩ : X) ∈ pCore 2 X := by
      obtain ⟨y,hy,he⟩ := hi.2 x x.property
      have he' : y = (⟨t * (x:G) * t⁻¹ * (x:G), X.mul_mem
          ((mem_normalizer_iff.mp (hn ht) x).mp x.property) x.property⟩ : X) :=
        Subtype.ext he
      exact he' ▸ hy
    have hcomm : ⁅t,(x:G)⁆ ∈ C := by
      change ⁅t,(x:G)⁆ ∈ ⁅X,T⁆
      rw [commutator_comm]
      exact commutator_mem_commutator ht x.property
    let z : X := ⟨⁅t,(x:G)⁆, hCX hcomm⟩
    have h2 : x ^ 2 ∈ N ⊔ pCore 2 X := by
      have hz : z ∈ N ⊔ pCore 2 X := mem_sup_left hcomm
      have hs := (N ⊔ pCore 2 X).mul_mem ((N ⊔ pCore 2 X).inv_mem hz) (mem_sup_right hinv)
      convert hs using 1
      apply Subtype.ext
      change (x:G)^2 = ⁅t,(x:G)⁆⁻¹ * (t * (x:G) * t⁻¹ * (x:G))
      simp only [commutatorElement_def, pow_two]
      group
    have hm := (N ⊔ pCore 2 X).mul_mem ((N ⊔ pCore 2 X).inv_mem h2) (mem_sup_right h3)
    convert hm using 1
    group
  have htop : IsPPerfect 2 (⊤ : Subgroup X) := hp.of_surjective
    (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm.toMonoidHom Subgroup.topEquiv.symm.surjective
  have hh := le_normal_of_isPPerfect_of_le_sup_pGroup ⊤ N (pCore 2 X) htop pCore_isPGroup hsup
  exact le_antisymm hCX (fun x hx => hh (mem_top (⟨x,hx⟩:X)))

private theorem steinberg_rank_bound (A : Subgroup BinaryLinearThree.Group)
    (hA : IsElementaryTwo A) : rank A < fixedCodim BinaryLinearThree.S A := by
  by_contra! hb
  let : IsIrreducible BinaryLinearThree.S := BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
  have hne : BinaryLinearThree.S ≠ 1 := by
    intro he
    have hall : Function.Injective (1 : Representation (ZMod 2) BinaryLinearThree.Group BinaryLinearThree.Steinberg) :=
      he ▸ BinaryLinearThree.steinberg_injective
    have : Subsingleton BinaryLinearThree.Group := ⟨fun a b => hall (by rfl)⟩
    have hc : Nat.card BinaryLinearThree.Group = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨this, inferInstance⟩
    rw [Matrix.PSL3Two.card_SL] at hc
    omega
  have hd := BinaryLinearThree.ResidualFFForms.ConstituentBudget.finrank_le_six_of_irreducible
    BinaryLinearThree.S hne ⟨A,hA,hb⟩
  rw [BinaryLinearThree.finrank_steinberg] at hd
  omega

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Original ordinary containment in the reduced overgroup, with all local
commutator, action, Fitting and representation inputs discharged. The exact
remaining list is supplied independently by the field and cover sieve. -/
theorem ordinary_source_containment
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (models : RemainingQuotient (K ⧸ pCore 2 K))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) : one L T V₁ ≤ K := by
  have hH := c.component.local_overgroup
  have hF9 := c.f9 H hH
  have hex := SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  have horder := LocalFitting.ordinary_core_card c.localSetup ⟨eL⟩
  have ha : Nonempty (AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.NaturalSetup
      L (T : Subgroup G) V V₁) := by
    rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
    · exact LocalFitting.ordinary_natural c.localSetup e he
    · have hc := Nat.card_congr (centerCongr (e.symm.trans eL)).toEquiv
      rw [Representation.Hexacode.even_center_card,
        alternatingGroup.center_eq_bot (by simp),card_bot] at hc
      omega
  obtain ⟨a⟩ := ha
  obtain ⟨t,ht,_,hinv⟩ := Ordinary.Inverter.exists_marked_inverter a
  have hfull := cubic_inversion_commutator (one L T V₁) (T : Subgroup G)
    (residual_isPPerfect _) (T_normalizes_one L T V₁ c.localSetup.line_stable) horder t ht hinv
  have hfit : fittingPreimageResidual H = ⊥ ∨ fittingPreimageResidual H = one L T V₁ := by
    have hr := LocalFitting.whole_residual c.localSetup hH c.earlier1339 hex
    have he : fittingPreimageResidual H = Components.Fitting.twoFittingResidual H := by
      unfold fittingPreimageResidual CoveredProduct.ResidualPlacement.residual Components.Fitting.twoFittingResidual
        Components.Fitting.twoFittingResidualIn Components.Fitting.twoFitting
      exact (map_embedded_pResidual 2
        ((fittingSubgroup (Source.Hstar H)).comap (QuotientGroup.mk' (pCore 2 H))) H.subtype).symm
    rw [he]
    rcases hr with hb | ⟨_,hb⟩ | ⟨hm,hb⟩
    · exact Or.inl hb
    · exact Or.inr hb
    · have hc := Nat.card_congr (centerCongr eL).toEquiv
      rw [hm.2.1, alternatingGroup.center_eq_bot (by simp), card_bot] at hc
      omega
  let : IsElementaryAbelian 2 (Source.UH H V₃) := c.localSetup.uh_elementary hH
  obtain ⟨star,B,_,hq⟩ := F918.exists_edge_quadratic_actor c.localSetup hF9
  let act : LinearThree.SourceAction H V₃ V₁ := {
    line_le := c.localSetup.line_le_uh H
    seed_le := hF9.plus_le_H
    representation := SolvableExclusion.Three.Supercritical.Offenders.linearAction star
    conjugation := star.conjugation }
  have hfaith : Function.Injective act.representation :=
    f9_section_faithful _ hF9 (Comparison.sourceSection act hF9.H_centralizes)
  have hk : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H := by
    intro h hh
    have he : act.representation (QuotientGroup.mk' (pCore 2 H) h) = 1 := by
      ext v
      obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
      change act.representation _ (Additive.ofMul (QuotientGroup.mk' _ u)) = Additive.ofMul (QuotientGroup.mk' _ u)
      rw [act.conjugation]
      exact congrArg Additive.ofMul (hh u)
    exact (QuotientGroup.eq_one_iff h).mp (hfaith (he.trans (map_one act.representation).symm))
  apply L₁_le_of_ordinary_source KnownSimple.IsKnownSimple H K L (one L T V₁) M G₁ V₁ V₃ T
    c.maximal.simpleQTKE c.component (RankReduction.smallQuotient_of_source_list models) eL
    rfl c.localSetup.line_stable horder hfull
    (Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup c.localSetup))
    hex hfit hqs act hk
  · intro A hA _
    exact steinberg_rank_bound A hA
  · intro A hA _
    change rank A < fixedCodim (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) A
    rw [fixedCodim_prod]
    exact BinaryLinearThree.ResidualFFForms.ConstituentBudget.rank_lt_natural_add_dual_fixedCodim A hA
  · exact (quadraticRatio_le_two_iff act.representation).mpr ⟨Source.starImage H B,hq⟩

/-- The ordinary branch supplies the product and moved-space clauses once
its independently produced remaining quotient list is available. -/
theorem ordinary_source_consequences
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (models : RemainingQuotient (K ⧸ pCore 2 K))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    one L T V₁ ≤ K ∧ H = K ⊔ (T : Subgroup G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hle := ordinary_source_containment c models eL
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp c.component.normal
  refine ⟨hle, ?_, ?_⟩
  · rw [← c.component.generated, sup_eq_left.mpr hle]
  · exact (Section07.ModelExclusions.span_commutator_of_containing_normal_component
      (localNaturalSetup c.localSetup) hKH hn hle).symm

/-- Both genuine local quotient cases of 13.8.21(1),(3),(4), conditional
only on the earlier SourceContext and the independent list (2). -/
theorem source_consequences_of_remainingQuotient
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (models : RemainingQuotient (K ⧸ pCore 2 K)) :
    one L T V₁ ≤ K ∧ H = K ⊔ (T : Subgroup G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  rcases local_quotient_alternatives c.localSetup with ⟨e,_⟩ | ⟨e,_⟩
  · exact ordinary_source_consequences c models e
  · exact covered_source_consequences c (RankReduction.smallQuotient_of_source_list models) ⟨e⟩

/-- Apply the field and cover sieve to both local A₆ cases. The exclusions
remain obligations of this field-sieve owner; this is not their discharge. -/
theorem source_consequences_of_exclusions
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hfield : ¬ HigherFieldAlternative (K ⧸ pCore 2 K))
    (hsix : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.A6Triple))
    (hmathieu : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22))
    (hcover : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.M22Triple)) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) ∧
      H = K ⊔ (T : Subgroup G) ∧ Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hlist := remainingQuotient_of_exclusions c.catalogue hfield hsix hmathieu hcover
  have hc := source_consequences_of_remainingQuotient c hlist
  exact ⟨hc.1,hlist,hc.2⟩

/-- The automorphism clause applies to either local A₆ case. The outstanding
13.8.19 input excludes H* itself, while K* remains the binary component. -/
theorem source_binary_automorphism
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)
    (hnot : ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL)) :
    Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have models : RemainingQuotient (K ⧸ pCore 2 K) :=
    Or.inl ⟨3, le_rfl, by decide, ZMod 2, inferInstance, inferInstance, by simp, ⟨eK⟩⟩
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  let eStar := (Components.componentStarEquiv H K hKH c.component.component).symm.trans eK
  have hH := (source_consequences_of_remainingQuotient c models).2.1
  obtain ⟨e,_⟩ := binary_automorphism_of_supplement H K T hH T.isPGroup' eStar hnot
  exact ⟨e⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
