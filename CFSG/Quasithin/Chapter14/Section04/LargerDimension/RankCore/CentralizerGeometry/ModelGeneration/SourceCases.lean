module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration.Products
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration.Components
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration.Transport
/-!
# The model-generation step in 14.4.7

`SourceAlternative` retains precisely the group and component markings from
14.4.2(3)–(6) that generation uses. Its dimension index is eight for the
orthogonal, symmetric and product cases and twelve for the genuine triple
M₂₂ extension. The separate source rank clause is retained literally as
`|X| = 2^(d/2−1)`, together with elementary abelianness.

The permutation calculations identify the actual residuals. In the triple
cover case, the literal generalized Fitting subgroup is quasisimple and has
two-group quotient, so it is the residual; its centralizer is too small for
an order-thirty-two actor. The orthogonal case uses the actual embedded
factors and the source element interchanging them by right conjugation.
No generation or projection conclusion is part of the model interface.

The final application supplies the exact `hstar` argument in
`EarlierGeometry.centralizer_eq_bot_of_star_generation`. It invokes the
earlier source alternative at `g⁻¹` and transports its marking through the
quotient equivalence to Hᵍ/O₂(Hᵍ). The earlier 12.8/14.3 geometry, genuine
14.4.2 alternatives, moved-rank calculation and uniqueness are retained as
source inputs; their final discharge belongs to the parent source assembly.

Source: Aschbacher–Smith, 14.4.2 and the first paragraph of 14.4.7,
printed pp.1006 and 1008–1009.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration
open CFSG.Quasithin.ChapterH.Section10To12
variable {Q : Type*} [Group Q]

/-- The generation-relevant literal alternatives, indexed by the source dimension. -/
inductive SourceAlternative (X : Subgroup Q) : ℕ → Prop
  | orthogonal
      (e : pResidual 2 Q ≃*
        ClassicalOrthogonal.OmegaPlus 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F)
      (swap : ∃ x : X,
        conjugate (orthogonalLeftFactor (pResidual 2 Q) e) (x : Q) =
          orthogonalRightFactor (pResidual 2 Q) e) : SourceAlternative X 8
  | symmetricSeven (e : Q ≃* Equiv.Perm (Fin 7)) : SourceAlternative X 8
  | symmetricProduct (e : Q ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)) :
      SourceAlternative X 8
  | alternatingProduct (e : Q ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5)) :
      SourceAlternative X 8
  | tripleM22 (model : IsTripleM22 (generalizedFitting Q))
      (extension : Nat.card (Q ⧸ generalizedFitting Q) = 2) : SourceAlternative X 12

private theorem generation_of_equiv {R : Type*} [Group R] (e : Q ≃* R)
    (X : Subgroup Q)
    (h : ⁅pResidual 2 R,X.map e.toMonoidHom⁆ = pResidual 2 R) :
    ⁅pResidual 2 Q,X⁆ = pResidual 2 Q := by
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rwa [map_commutator,map_pResidual]

/-- The genuine triple-cover extension has full residual commutator with X. -/
theorem triple_residual_generation [Finite Q] (X : Subgroup Q)
    (hm : IsTripleM22 (generalizedFitting Q))
    (hq : Nat.card (Q ⧸ generalizedFitting Q) = 2) (hc : Nat.card X = 32) :
    ⁅pResidual 2 Q,X⁆ = pResidual 2 Q := by
  let : IsQuasisimple (generalizedFitting Q) := hm.quasisimple
  have hp : IsPGroup 2 (Q ⧸ generalizedFitting Q) :=
    IsPGroup.of_card (n := 1) (by simpa using hq)
  rw [(SimpleSocle.layer_residuals (generalizedFitting Q) hp).2.1]
  exact triple_M22_generation _ X hm rfl hp hc

/-- Every literal alternative gives residual generation at the exact source rank. -/
theorem SourceAlternative.generation [Finite Q] {X : Subgroup Q} {d : ℕ}
    (h : SourceAlternative X d) (he : IsElementaryAbelian 2 X)
    (hc : Nat.card X = 2 ^ (d / 2 - 1)) :
    ⁅pResidual 2 Q,X⁆ = pResidual 2 Q := by
  cases h with
  | orthogonal e hs => exact orthogonal_residual_generation X e hs
  | symmetricSeven e =>
    apply generation_of_equiv e
    apply symmetric_seven_residual_generation
    rw [card_map_of_injective e.injective,hc]
    norm_num
  | symmetricProduct e =>
    apply generation_of_equiv e
    apply symmetric_product_residual_generation _ _ (he.map e.toMonoidHom)
    rw [card_map_of_injective e.injective,hc]
    norm_num
  | alternatingProduct e =>
    apply generation_of_equiv e
    apply alternating_product_residual_generation _ _ (he.map e.toMonoidHom)
    rw [card_map_of_injective e.injective,hc]
    norm_num
  | tripleM22 hm hq => exact triple_residual_generation X hm hq (by simpa using hc)
/-- Generation for the actual residual image under the two-core quotient map. -/
theorem SourceAlternative.quotient_generation [Finite Q] (B : Subgroup Q) {d : ℕ}
    (h : SourceAlternative (B.map (QuotientGroup.mk' (pCore 2 Q))) d)
    (he : IsElementaryAbelian 2 (B.map (QuotientGroup.mk' (pCore 2 Q))))
    (hc : Nat.card (B.map (QuotientGroup.mk' (pCore 2 Q))) = 2 ^ (d / 2 - 1)) :
    (pResidual 2 Q).map (QuotientGroup.mk' (pCore 2 Q)) =
      ⁅(pResidual 2 Q).map (QuotientGroup.mk' (pCore 2 Q)),
        B.map (QuotientGroup.mk' (pCore 2 Q))⁆ := by
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  exact (h.generation he hc).symm
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.ModelGeneration

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup ModelGeneration
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

/-- The model calculation supplies the literal `hstar` required by the source
centralizer argument. The earlier 14.4.2 statement is used at `g⁻¹`, including
its exact elementary rank. Its model alternatives and the earlier rank and
uniqueness inputs remain source theorem parameters for the parent assembly. -/
theorem EarlierGeometry.centralizer_eq_bot_of_source_models
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (h1442 : ∀ t ∈ L, t ∈ normalizer (V₂ : Set G) → t ∉ H →
      let X := ((conjugate (W U V₂) t).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
      SourceAlternative X (Module.finrank (ZMod 2) V) ∧ IsElementaryAbelian 2 X ∧
        Nat.card X = 2 ^ (Module.finrank (ZMod 2) V / 2 - 1))
    (T M : Subgroup G) (hTH : T ≤ H) (hTL : T ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ conjugate T g ≤ N → N = M)
    (hKM : ¬ conjugate ((pResidual 2 H).map H.subtype) g ≤ M) :
    conjugate ((pResidual 2 H).map H.subtype) g ≤
        centralizer (D H U g : Set G) ∧
      D H U g ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨hm, he, hc⟩ := h1442 g⁻¹ (L.inv_mem d.g_mem_L)
    ((normalizer (V₂ : Set G)).inv_mem d.g_normalizes)
    (fun h => d.g_not_mem_H (by simpa only [inv_inv] using H.inv_mem h))
  exact d.centralizer_eq_bot_of_star_generation hrank T M hTH hTL
    (star_generation_transport H (W U V₂) g (hm.generation he hc)) hunique hKM

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
