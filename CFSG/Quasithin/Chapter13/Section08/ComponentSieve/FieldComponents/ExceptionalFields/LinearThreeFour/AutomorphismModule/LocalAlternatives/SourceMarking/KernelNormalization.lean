module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.MarkedBorel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.QuotientMarks

/-!
# Normalizing the source central residual

The source identity O₂,Z(L) = C_L(V), together with 13.2.2(3), sandwiches
C_{L₁}(V) between L₀ and O₂,Z(L). Taking two-residuals therefore gives
L₀ = O²(C_{L₁}(V)). The two overlap identities from 13.7.3(6),(9) make
Q_H normalize both V and L₁, hence this centralizer and its residual.
Only the printed earlier identities are inputs; no equality M = N_G(L₀)
or normality of L₀ in H is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.2.2 proof, printed p.878; 13.7.3(6),(9), p.936; application p.955.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- The residual of the relative centralizer is exactly the source central residual. -/
theorem zero_eq_centralizer_residual (L T V V₁ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hcentral : centralPreimage L = L ⊓ centralizer (V : Set G)) :
    zero L = residual (one L T V₁ ⊓ centralizer (V : Set G)) := by
  have hz : zero L ≤ one L T V₁ ⊓ centralizer (V : Set G) :=
    le_inf (zero_le_one_of_factorization L T V₁ hfactor)
      ((residual_le _).trans (hcentral.le.trans inf_le_right))
  apply le_antisymm
  · have he : residual (zero L) = zero L := by
      unfold LinearThree.Geometry.CoveredProduct.ResidualPlacement.residual
      rw [(pResidual_eq_top_iff 2 _).mpr (zero_isPPerfect L),
        ← MonoidHom.range_eq_map, range_subtype]
    rw [← he]
    exact embedded_pResidual_mono 2 hz
  · apply embedded_pResidual_mono 2
    rw [hcentral]
    exact inf_le_inf (one_le_L_of_factorization L T V₁ hTL hfactor) le_rfl

/-- The two overlap clauses of 13.7.3 force Q_H to normalize the source L₀. -/
theorem kernel_normalizes_zero (H L T M V V₁ V₃ : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hcentral : centralPreimage L = L ⊓ centralizer (V : Set G))
    (hcomm : ⁅V, Source.QH H⁆ = V₃) (hV₃ : V₃ ≤ V)
    (hoverlap : H ⊓ M = H ⊓ normalizer (V : Set G))
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}) :
    Source.QH H ≤ normalizer (zero L : Set G) := by
  have hQV : Source.QH H ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm ▸ hV₃)
  have hQHM : Source.QH H ≤ H ⊓ M := by
    rw [hoverlap]
    exact le_inf (pCoreIn_le 2 H) hQV
  have hQone : Source.QH H ≤ normalizer (one L T V₁ : Set G) := by
    rw [htheta]
    apply hQHM.trans
    apply le_normalizer_closure_iff.mpr
    intro g hg x hx
    exact subset_closure ⟨(H ⊓ M).mul_mem ((H ⊓ M).mul_mem hg hx.1)
      ((H ⊓ M).inv_mem hg), ((MulAut.conj g).orderOf_eq x).trans hx.2⟩
  rw [zero_eq_centralizer_residual L T V V₁ hTL hfactor hcentral]
  exact ((le_inf hQone (hQV.trans ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (V : Set G))).mp inferInstance))).trans
    inf_normalizer_le_normalizer_inf).trans (normalizer_le_residual_normalizer _)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
