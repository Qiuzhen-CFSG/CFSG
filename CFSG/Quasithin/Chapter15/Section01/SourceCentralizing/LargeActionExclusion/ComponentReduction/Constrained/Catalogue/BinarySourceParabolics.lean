module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryWreath
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.Products
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FiveEndpointResidual
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The degree-five graph endpoint is a source parabolic

The degree-five endpoint two-residual contains a product of incident roots
whose sixth power is nonidentity. A central product of A₃ blocks has exponent
dividing six, so the actual original endpoint cannot have that residual form.
Surjectivity of its literal two-core marking transports the obstruction.
Combined with wreath selection and characteristic two, this supplies every
clause of the source parabolic family in the degree-five graph branch.

Both original source primes and the exchanged selection retain the same
component, quotient marking and generating pair. Source placement remains
with the existing original 15.1.22 placement producer. This does not settle
the interior branch or other node A₃ exclusions, small-block recognition,
general Borel placement, or constrained-catalogue exhaustiveness.

Source: Aschbacher--Smith 15.1.22 (*), (3), printed pp.1098--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem not_aThreeProduct_of_residual_image
    (P : Subgroup G) {H : Type*} [Group H]
    (f : P →* H) (hf : Function.Surjective f)
    (hH : ∃ y ∈ pResidual 2 H, y^6 ≠ 1) : ¬ IsAThreeProduct P := by
  rintro ⟨F,hF,hc,hgen⟩
  obtain ⟨y,hy,hy6⟩ := hH
  rw [←map_pResidual_of_surjective 2 f hf] at hy
  obtain ⟨x,hx,rfl⟩ := hy
  apply hy6
  rw [←map_pow,ChapterC.alternatingThree_product_pow_six F
    (fun A hA => (hF A hA).2) hc (hgen.symm ▸ hx),map_one]

/-- The actual degree-five endpoint cannot have an A₃-product two-residual. -/
theorem BinaryNodeGeometry.five_endpoint_not_aThree_product
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hE : a.endpoint = EquivariantLift.lift d.L (coreFlagMap d.L e)
      (cutStabilizer b.basis {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ)) :
    ¬ IsAThreeProduct a.endpoint := by
  let q := coreFlagMap d.L e
  let P := a.endpoint.subgroupOf d.L
  let E := cutStabilizer b.basis {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ
  have hi : P.map q = E := by
    change (a.endpoint.subgroupOf d.L).map q = E
    rw [hE]
    exact coreFlagMap_lift_image d.L e E
  let t : P ≃* a.endpoint := subgroupOfEquivOfLe a.endpoint_proper.le
  let f : a.endpoint →* E := ((MulEquiv.subgroupCongr hi).toMonoidHom.comp
    (q.subgroupMap P)).comp t.symm.toMonoidHom
  have hf : Function.Surjective f := (MulEquiv.subgroupCongr hi).surjective.comp
    ((q.subgroupMap_surjective P).comp t.symm.surjective)
  exact not_aThreeProduct_of_residual_image a.endpoint f hf
    (five_endpoint_residual_not_exponent_six b.basis)

/-- In degree five the actual graph endpoint satisfies every clause of the
source parabolic family; no block-exclusion or quotient premise is added. -/
theorem BinaryNodeGeometry.five_endpoint_source_parabolic
    {d : CaseIComponentData T M Mc V}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(4+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) :
    (∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _) ∨
      d.IsSourceParabolic a.endpoint := by
  rcases b.action with hi | ⟨ho,hE,_⟩
  · exact Or.inl hi.1
  · right
    have hw := b.extension_cases hK (Or.inr rfl)
    refine ⟨a.endpoint_proper.le,?_,a.endpoint_fitting,?_,?_⟩
    · rw [a.sylowNormalizer_eq]
      exact a.normalizes_endpoint
    · rcases hw with hi | hw
      · obtain ⟨x,hx⟩ := ho
        exact (hx (hi x)).elim
      · exact Or.inr hw
    · exact b.five_endpoint_not_aThree_product hE
/-- Both original primes yield an actual member of the source parabolic family
in the degree-five graph branch, retaining the common quotient marking. -/
theorem PreExclusionSource.constrained_binary_five_source_parabolic
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
        d.BinaryEndpointExtension a.endpoint ∧
          ∃ b : d.BinaryNodeGeometry a,
            (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
              d.IsSourceParabolic a.endpoint := by
  obtain ⟨t,ht,hML,hM',a,ha,b,_⟩ :=
    s.constrained_binary_wreath (h := h) hG hempty hM hJ hu hf (Or.inr rfl) e
  exact ⟨t,ht,hML,hM',a,ha,b,b.five_endpoint_source_parabolic
    ⟨d.L_component.1,s.local_component⟩⟩

/-- The exchanged component uses the same degree-five source parabolic. -/
theorem ExchangedSource.constrained_binary_five_source_parabolic
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
        d.BinaryEndpointExtension a.endpoint ∧
          ∃ b : d.BinaryNodeGeometry a,
            (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
              d.IsSourceParabolic a.endpoint := by
  obtain ⟨t,ht,hML,hM',a,ha,b,_⟩ :=
    s.constrained_binary_wreath hG hempty hM hJ hu h hf (Or.inr rfl) e
  exact ⟨t,ht,hML,hM',a,ha,b,b.five_endpoint_source_parabolic
    ⟨d.L_component.1,s.local_component⟩⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open BinaryLinear.InvariantNodeActions
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies degree-five endpoint source-family membership
in the graph branch, without an extra residual or block hypothesis. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_five_source_parabolic
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
            d.BinaryEndpointExtension a.endpoint ∧
              ∃ b : d.BinaryNodeGeometry a,
                (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
                  d.IsSourceParabolic a.endpoint) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binary_five_source_parabolic (h := h) hG hempty hM hJ hu hf e⟩
end CFSG.Quasithin.Chapter15.Section01
