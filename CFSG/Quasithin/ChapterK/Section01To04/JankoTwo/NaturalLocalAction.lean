module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.CubicActors
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.LongRootApplications

/-!
# The local natural-module calculation and cubic witness for J₂

The actual native involution centralizer E₄ × A₅ acts on its literal displacement
module W as a trivial field line plus the natural SL₂(4) plane. This identifies
all four source fixed/commutator spaces and derives their binary dimension six.
Elementary actors of rank at least three containing the noncentral involution
have fixed dimension four, codimension eight, cubic action and nonquadratic
action. The concrete rank-four actor supplies an attaining witness in the
marked source group. LongRootApplications also supplies the actual long-root
fixer data and rank-two exclusion for the 2-central representative.

The particular embedding comparisons and all these actor calculations are
proved. Universal B.4.6 root facts and its long-root displacement/fixer clauses
remain named earlier-source inputs, owned by qt-b-04-g2 and discharged in
qt-k-01-04. Recognition, involution membership geometry, and the final K.4.5
ratio and FF-exclusion assembly remain with their independent owners.
Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

/-- K.4.5's W is the actual displacement/fixed space and has the indicated
natural SL₂(4) coordinates for the full native E₄ × A₅ centralizer. -/
theorem localW_natural_SL2_structure (h : InvolutionImages.B46RootFacts K) :
    ∃ φ : A5 ≃* SL(2,K), ∃ E : D.localW.toSubmodule ≃ₗ[K] K × (Fin 2 → K),
      (∀ (c : E4) (e : A5) (w : D.localW.toSubmodule),
        E (D.localW.toRepresentation (c,e) w) = ((E w).1, (φ e).val *ᵥ (E w).2)) ∧
      Module.finrank (ZMod 2) D.localW.toSubmodule = 6 ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        fixedSpace D.naturalCarrierAction (zpowers a) ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        fixedSpace D.naturalCarrierAction centralFour ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        subspaceCommutator D.naturalCarrierAction ⊤ centralFour ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        subspaceCommutator D.naturalCarrierAction ⊤ (zpowers a) := by
  obtain ⟨g,r,hr,he⟩ := D.carrierEmbedding_a_isShortRootElement h
  obtain ⟨φ,E,hE,-,ha,hC,hVC⟩ := D.localW_shortRoot_comparison g r hr he
  refine ⟨φ,E,hE,D.localW_binary_finrank h,ha,hC,hVC,?_⟩
  apply le_antisymm
  · rintro w ⟨v,hv⟩
    exact Submodule.subset_span ⟨a,mem_zpowers a,v,Submodule.mem_top,hv.symm⟩
  · rw [hVC]
    apply Submodule.span_mono
    rintro w ⟨x,hx,v,hv,rfl⟩
    exact ⟨x,(zpowers_le.mpr a_mem_centralFour) hx,v,hv,rfl⟩

/-- The noncentral involution's fixed and displacement dimensions are both six. -/
theorem carrier_noncentral_dimensions (h : InvolutionImages.B46RootFacts K) :
    fixedCodim D.naturalCarrierAction (zpowers a) = 6 ∧
      Module.finrank (ZMod 2) (fixedSpace D.naturalCarrierAction (zpowers a)) = 6 := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  let : Module.Finite (ZMod 2) (Atlas.G2.Natural.Space K) := Module.Finite.trans K _
  obtain ⟨φ,E,hE,hW,ha,-⟩ := D.localW_natural_SL2_structure h
  have hdim : Module.finrank (ZMod 2) (fixedSpace D.naturalCarrierAction (zpowers a)) = 6 := by
    rw [← ha,((D.localW.toSubmodule.restrictScalarsEquiv (ZMod 2)).restrictScalars
      (ZMod 2)).finrank_eq,hW]
  refine ⟨?_,hdim⟩
  have hc := fixedCodim_add_finrank D.naturalCarrierAction (zpowers a)
  rw [hdim,D.finrank_space] at hc
  omega

/-- The local calculation transported to the actual marked source group.
The parent supplies the actor and its specified noncentral involution. -/
theorem source_noncentral_actor_calculation [FiniteDimensional (ZMod 2) V]
    (h : InvolutionImages.B46RootFacts K)
    (A : Subgroup Carrier) (hA : IsElementaryTwo A) (ha : a ∈ A) (hr : 3 ≤ rank A) :
    Module.finrank (ZMod 2) (fixedSpace ρ (A.map D.carrierMap)) = 4 ∧
      fixedCodim ρ (A.map D.carrierMap) = 8 ∧
      IsCubic ρ (A.map D.carrierMap) ∧ ¬ IsQuadratic ρ (A.map D.carrierMap) := by
  let : Module.Finite (ZMod 2) K := Module.finite_of_finrank_eq_succ D.fieldDegree
  have hd : fixedCodim ρ (A.map D.carrierMap) = 8 :=
    (D.carrier_fixedCodim A).trans (D.noncentral_actor_fixedCodim h A hA ha hr)
  refine ⟨?_,hd,(D.carrier_cubic_iff A).mpr (D.noncentral_actor_cubic h A hA ha),?_⟩
  · have hc := fixedCodim_add_finrank ρ (A.map D.carrierMap)
    rw [hd,D.finrank] at hc
    omega
  · exact fun hq => D.noncentral_actor_not_quadratic h A hA ha hr
      ((D.carrier_quadratic_iff A).mp hq)

end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
