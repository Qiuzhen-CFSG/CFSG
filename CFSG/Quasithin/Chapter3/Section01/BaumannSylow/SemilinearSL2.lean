module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SemilinearMoved
public import CFSG.Quasithin.Chapter3.Section01.E23Input
public import CFSG.Quasithin.Chapter3.Section01.BaumannSylow

/-!
# The semilinear moved-module input in the original Chapter 3 configuration

The Qrc hypotheses construct the reduced omega-center conjugate span U
inside H. Its literal moved subgroup [U,O²(H)] has the same centralizer.
A normal SL₂ natural marker on that moved subgroup therefore suffices for
the Baumann theorem even when the whole action includes field automorphisms.
The original Chapter 3 lifting theorem then makes O₂(M₀) Sylow in the
required residual product. The B.6.9 factor marker remains an honest earlier
input; neither whole-U splitting nor a Baumann conclusion is assumed.
Source: Aschbacher–Smith, B.6.10, E.2.3 and 3.1.7.
-/

open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u v w
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}
  {A : Type w} [Group A] [Finite A]
  {F : Type v} [Field F] [Finite F] [Algebra (ZMod 2) F]

public theorem QrcHypotheses.residual_sylow_of_semilinear_sl2_moved
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE K G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ X : Subgroup G, IsMaximalTwoLocal X → M₀ ≤ X → X = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let hU : IsPReduced 2 U := h.sylowOmega_reduced (hG.evenCharacteristic T)
    letI : U.Normal := hU.normal
    letI : IsElementaryAbelian 2 U := hU.elementary
    let W := ⁅U,pResidual 2 H⁆
    letI : IsElementaryAbelian 2 W := (hU.moved U).elementary
    ∀ (q : H →* A) (_hq : Function.Surjective q)
      (_hker : q.ker = centralizer (U : Set H))
      (L : Subgroup A) [L.Normal]
      (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
      (ρ : Representation (ZMod 2) A (Fin 2 → F)) (_hfaith : Function.Injective ρ)
      (_hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : A) v = Matrix.mulVec (e g).val v)
      (_hF : 2 < Nat.card F)
      (f : Additive W →ₗ[ZMod 2] (Fin 2 → F)) (_hf : Function.Surjective f)
      (_he : ∀ (g : H) (v : Additive W),
        f (Additive.ofMul (MulAut.conjNormal g v.toMul)) = ρ (q g) (f v))
      (_hk : ∀ v : Additive W, f v = 0 ↔
        (v.toMul : H) ∈ centralizer (pResidual 2 H : Set H)),
      Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
        ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  have hU : IsPReduced 2 U := h.sylowOmega_reduced (hG.evenCharacteristic T)
  let : U.Normal := hU.normal
  let : IsElementaryAbelian 2 U := hU.elementary
  dsimp only
  intro q hq hker L hL e ρ hfaith hnat hF f hf he hk
  have hh := h.e23_hypotheses hG hM hu hJ hZ
  apply h.residual_sylow_of_baumann_sylow hJ
  exact (ChapterB.RankOneBaumann.semilinear_moved_baumann_sylow_and_alpha
    (T.subtype h.right_mem.1.1.2) hh.2.2.1 U hU hh.2.2.2.2
      q hq hker L e ρ hfaith hnat hF f hf he hk).1
end CFSG.Quasithin.Chapter3
