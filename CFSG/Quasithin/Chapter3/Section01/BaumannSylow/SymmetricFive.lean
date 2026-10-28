module
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow.SpanApplication
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.A5Source

/-!
# The natural S₅ branch on the original qrc module

The original Hypothesis 3.1.5 inputs construct the reduced H-orbit of
Ω₁(Z(T)), its minimal parabolic and the moving Thompson subgroup.
The genuine residual-equivariant natural S₅ theorem supplies its Sylow
extension in the exact maximal-subgroup conjugate span. The original
span adapter then proves O₂(M₀) Sylow in O²(H)O₂(M₀).

Only the single-image natural marking remains for E.2.3 recognition.
No Sylow, index-two lifting, or placement conclusion is assumed.
Source: Aschbacher–Smith E.2.3 and 3.1.7, pp.216–217 and 575–576.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}
open BinaryOffender BinaryPermutation BinaryPermutation.FiveCentralExtension

theorem QrcHypotheses.residual_sylow_of_natural_symmetric_five
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ X : Subgroup G, IsMaximalTwoLocal X → M₀ ≤ X → X = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU : IsPReduced 2 U := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI : U.Normal := hU.normal
    letI : IsElementaryAbelian 2 U := hU.elementary
    ∀ (q : H →* Sym) (hq : Function.Surjective q)
      (hker : q.ker = centralizer (U : Set H))
      (p : Additive U →ₗ[ZMod 2] core (Fin 5)) (_hp : Function.Surjective p)
      (_heK : ∀ k ∈ pResidual 2 H, ∀ v,
        p (NormalElementaryQuotient.representation U q hq hker (q k) v) =
          coreRepresentation (Fin 5) (q k) (p v))
      (_hk : p.ker = fixedSpace
        (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 H).map q)),
      Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
        ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU : IsPReduced 2 U := h.sylowOmega_reduced (hG.evenCharacteristic T)
  let : U.Normal := hU.normal
  let : IsElementaryAbelian 2 U := hU.elementary
  dsimp only
  intro q hq hker p hp heK hk
  have hh := h.e23_hypotheses hG hM hu hJ hZ
  obtain ⟨_,_,_,S₁,hS₁,hBS,_,hspan⟩ :=
    ChapterC.SymmetricFive.source_residual_quotient_conclusions
      (T.subtype h.right_mem.1.1.2) hh.2.2.1 U hU q hq hker p hp hh.2.2.2.2 heK hk
  exact h.residual_sylow_of_baumann_span hJ hh.2.2.1 S₁ hS₁ hBS hspan
end CFSG.Quasithin.Chapter3
