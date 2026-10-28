module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Kernel
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Forms
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Assembly
/-!
# The early local theorem applied to the actual source center calculation

This application discharges the Frattini, square, commutator, irreducibility,
span, local-kernel and marked-form inputs to the proved parabolic assembly.
The output retains the original external conjugator and the original antecedent
Z(U)^g ≤ U, and constructs the multiplication equivalence for the internal
product. No claim that g is internal or involutory is made or needed.

The actual LT action/core identity, case-dependent full L action, and the
original flag/setup inputs are the earlier 12.8.1--3 consequences supplied by
qt-12-08-setup and assembled by qt-12-08-preliminary. In dimension two the
source S₃ action belongs to LT; no full L action is required.

Source: Aschbacher--Smith, Lemmas 12.8.4(1--4), 12.8.8(2,3,6), and
12.8.10(5), printed pp.850--854.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Source 12.8.10(5) with all early local and form inputs constructed. -/
theorem localKernel_source_center_product
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    {K : GroupClass} (hG : IsSimpleQTKE K G)
    (L M : Subgroup G) (hn : 2 ≤ n ∧ n ≤ 5)
    (hVT : V ≤ (T : Subgroup G)) (hLV : L ≤ normalizer (V : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hres : pResidual 2 L = ⊤)
    (hnatural : 3 ≤ n → Nonempty (AmbientNaturalMarking L hLV n))
    (hM : M = normalizer (L : Set G))
    (hunique : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} = {M})
    (hCV : centralizer (V : Set G) ≤ M)
    (hCL : L ⊓ centralizer (V : Set G) = L.pCoreIn 2)
    (hescape : ¬ F.H ≤ M)
    (hfullLT : Function.Surjective (F.binarySeedAction L hLV))
    (hfullL : 3 ≤ n → ∀ a : MulAut V,
      ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (hnaturalCore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ≤ F.U →
      (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  have hJ := F.H_mem_Hz (by omega) L M hescape
  have htwo := F.localKernel_UH_isPGroup hG L M F.H hn.1 hVT hLV hTL hres hnatural hJ
  have hphi := F.localKernel_frattini_eq_point hG L M hn.1 hVT hLV hTL hres hnatural hescape hne
  obtain ⟨hcomm, hsquare⟩ :=
    F.localKernel_commutator_squares hG L M hn.1 hVT hLV hTL hres hnatural hescape
  have hirr := F.localKernel_irreducible L hn.1 hLV hnatural
  have hcenter := F.seed_inf_center_eq_point L (by omega) hLV hirr hne
  have hspan := F.U_eq_plane_span L hn.1 hLV hirr
  have hcore := F.localKernel_eq_pCore hG L M F.H hn.1 hVT hLV hTL hres hnatural
    hM hunique hCV hCL hJ
  let : IsElementaryAbelian 2 F.Uhat := F.uhat_elementary_of_point (by omega) htwo hphi
  let B : F.UhatCommutatorForm hcomm := F.localKernel_markedForm (by omega) htwo hphi hcomm
  exact (F.binary_source_center_calculations hn.1 L hLV ((pResidual_eq_top_iff 2 L).mp hres)
    hTL hfullLT hfullL hnaturalCore hcenter hcomm hsquare hspan hne g hgP hgH hcore B).2.2.2.2.1
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
