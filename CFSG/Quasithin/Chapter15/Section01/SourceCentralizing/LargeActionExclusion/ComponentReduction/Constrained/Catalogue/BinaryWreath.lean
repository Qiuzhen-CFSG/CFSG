module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryNodes
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.EndpointExtension

/-!
# The wreath endpoint in the original graph-action branch

For the same binary generating pair and quotient marking, a graph actor
forces the endpoint Sylow extension to have the literal S₃ ≀ C₂ quotient.
The source local-family hypothesis supplies the original Sylow intersection;
the model argument rules out the product quotient using its action on the
first endpoint flag. Both original primes and the later exchanged selection
retain the original component and all existing parabolic markings.

This discharges wreath selection in 15.1.22(3). Membership in the source
parabolic family still requires the A₃-product exclusion, and source placement
must still put the generators in opposite original intersections. Small-block
recognition and general Borel placement remain with this catalogue owner.
The original 15.1.14 premise retains its existing producer and final assembly.

Source: Aschbacher--Smith 15.1.22(3), printed pp.1099--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original graph branch has the wreath quotient over the actual
endpoint extension's own two-core. The original node geometry is retained. -/
theorem BinaryNodeGeometry.extension_cases
    {d : CaseIComponentData T M Mc V} {m : ℕ}
    {e : (d.L ⧸ pCore 2 d.L) ≃* SL(m+1,ZMod 2)}
    {a : d.BinaryGeneratingParabolics e} (b : d.BinaryNodeGeometry a)
    (hK : d.L ∈ Chapter1.LIn d.G1 d.S) (hm : m=3 ∨ m=4) :
    (∀ x : d.S, coreFlagAction d.L d.S b.normalizes e x ∈ MulAut.innerSubgroup _) ∨
      Nonempty (((a.endpoint ⊔ d.sylowNormalizer : Subgroup G) ⧸
        pCore 2 (a.endpoint ⊔ d.sylowNormalizer : Subgroup G)) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  rcases b.action with hi | ⟨ho,hE,_⟩
  · exact Or.inl hi.1
  · right
    rw [a.sylowNormalizer_eq]
    obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
    obtain ⟨eE⟩ := a.endpoint_quotient
    exact endpoint_extension_wreath d.L d.S b.normalizes
      (T.isPGroup'.to_le d.S_le_T) Q hQ hm e b.basis b.sylow_image
      a.endpoint hE a.normalizes_endpoint eE ho

/-- Both original primes retain the common quotient marking, with the wreath
quotient proved whenever the original Sylow action is not inner. -/
theorem PreExclusionSource.constrained_binary_wreath
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
        d.BinaryEndpointExtension a.endpoint ∧
          ∃ b : d.BinaryNodeGeometry a,
            (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
              Nonempty (((a.endpoint ⊔ d.sylowNormalizer : Subgroup G) ⧸
                pCore 2 (a.endpoint ⊔ d.sylowNormalizer : Subgroup G)) ≃*
                RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  obtain ⟨t,ht,hML,hM',a,ha⟩ :=
    s.constrained_binary_extensions (h := h) hG hempty hM hJ hu hf (by omega) e
  obtain ⟨b⟩ := d.constrained_binary_node_geometry hG hempty hM hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hm t a
  exact ⟨t,ht,hML,hM',a,ha,b,b.extension_cases
    ⟨d.L_component.1,s.local_component⟩ hm⟩

/-- Exchanged selection consumes the same graph-to-wreath calculation on both planes. -/
theorem ExchangedSource.constrained_binary_wreath
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
        d.BinaryEndpointExtension a.endpoint ∧
          ∃ b : d.BinaryNodeGeometry a,
            (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
              Nonempty (((a.endpoint ⊔ d.sylowNormalizer : Subgroup G) ⧸
                pCore 2 (a.endpoint ⊔ d.sylowNormalizer : Subgroup G)) ≃*
                RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) := by
  obtain ⟨t,ht,hML,hM',a,ha⟩ :=
    s.constrained_binary_extensions hG hempty hM hJ hu h hf (by omega) e
  obtain ⟨b⟩ := d.constrained_binary_node_geometry hG hempty hM hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple hm t a
  exact ⟨t,ht,hML,hM',a,ha,b,b.extension_cases
    ⟨d.L_component.1,s.local_component⟩ hm⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open BinaryLinear.InvariantNodeActions
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]

/-- The original marker now supplies the resolved graph extension, preserving
its component, prime, seed, quotient map and generating pair. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binary_wreath
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
            d.BinaryEndpointExtension a.endpoint ∧
              ∃ b : d.BinaryNodeGeometry a,
                (∀ x : d.S, coreFlagAction d.L d.S b.normalizes t x ∈ MulAut.innerSubgroup _) ∨
                  Nonempty (((a.endpoint ⊔ d.sylowNormalizer : Subgroup G) ⧸
                    pCore 2 (a.endpoint ⊔ d.sylowNormalizer : Subgroup G)) ≃*
                    RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull marker hres
  exact ⟨d,hZ,hr,s,fun hf _ hm e =>
    s.constrained_binary_wreath (h := h) hG hempty hM hJ hu hf hm e⟩
end CFSG.Quasithin.Chapter15.Section01
