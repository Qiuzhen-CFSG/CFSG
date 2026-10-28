module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann
public import CFSG.Quasithin.Chapter3.Section01.E23Input
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow

/-!
# The natural SL₂ input in the original Chapter 3 configuration

The source Qrc hypotheses construct the actual reduced conjugate-span module
inside H. A faithful natural SL₂ image with its fixed-kernel marker then gives
the Baumann Sylow conclusion, which lifts to the original subgroup O₂(M₀).
This is the single-image application of B.6.10 used in E.2.3 and Chapter 3;
the full subnormal-factor and field-automorphism reductions remain separate.
Source: Aschbacher–Smith, B.6.10, E.2.3, and 3.1.7.
-/

open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u v
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}
  {F : Type v} [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)

public theorem QrcHypotheses.residual_sylow_of_natural_sl2
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ X : Subgroup G, IsMaximalTwoLocal X → M₀ ≤ X → X = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU : IsPReduced 2 U := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI : U.Normal := hU.normal
    letI : IsElementaryAbelian 2 U := hU.elementary
    ∀ (q : H →* D) (hq : Function.Surjective q)
      (hker : q.ker = centralizer (U : Set H))
      (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (_hf : Function.Surjective f)
      (_he : ∀ a w, f (NormalElementaryQuotient.representation U q hq hker a w) = N a (f w))
      (_hk : f.ker = BinaryOffender.fixedSpace
        (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 H).map q)),
      Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
        ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU : IsPReduced 2 U := h.sylowOmega_reduced (hG.evenCharacteristic T)
  let : U.Normal := hU.normal
  let : IsElementaryAbelian 2 U := hU.elementary
  dsimp only
  intro q hq hker f hf he hk
  have hh := h.e23_hypotheses hG hM hu hJ hZ
  apply h.residual_sylow_of_baumann_sylow hJ
  exact (ChapterB.RankOneBaumann.natural_baumann_sylow_and_alpha
    (T.subtype h.right_mem.1.1.2) hh.2.2.1 U hU hh.2.2.2.2
      q hq hker f hf he hk).1
end CFSG.Quasithin.Chapter3
