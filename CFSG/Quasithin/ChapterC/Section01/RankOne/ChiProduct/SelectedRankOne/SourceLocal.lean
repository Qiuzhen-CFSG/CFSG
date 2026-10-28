module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Natural
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
/-!
# C.1.18 applied to the original selected natural rank-one group

The given reduced omega-span and genuine natural-layer coordinates supply
all four C.1.17 hypotheses for Baum(T) inside O²(G) Baum(T). The single
characteristic pair is fixed before applying its universal property to this
actual subgroup. Its original universe and subgroup inclusion are retained.

Source: Aschbacher–Smith C.1.26, p.132, using C.1.18.
-/
public section
universe u v
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
variable {G : Type u} {H : Type v} {F : Type} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem normal_layer_selected_localClass
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D) (hF : 2 < Nat.card F)
    (f : Additive (⁅U,pResidual 2 G⁆ : Subgroup G) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : Function.Surjective f)
    (he : ∀ (g : G) (hg : q g ∈ L) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) = N (e ⟨q g,hg⟩) (f v))
    (hk : ∀ (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G))
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G) :
    InLocalClass (inclusion (show baumann (T : Subgroup G) ≤
      pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) := by
  obtain ⟨hs,hfit',_,_,_⟩ := normal_layer_selected_geometry T hP U hU hJ q hq hker L e hF
    f hf he hk hspan hfit
  have hn : 1 ≤ Module.finrank (ZMod 2) F := by
    by_contra! hn
    have hz : Module.finrank (ZMod 2) F = 0 := by omega
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    simp only [hz,pow_zero] at hc
    omega
  exact ⟨inclusion_injective _,hs,hfit',Module.finrank (ZMod 2) F,hn,F,inferInstance,
    inferInstance,inferInstance,by simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)),
    normal_layer_selected_natural T hP U hU hJ q hq hker L e hF f hf he hk hspan⟩
theorem normal_layer_characteristicPair_alternatives
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D) (hF : 2 < Nat.card F)
    (f : Additive (⁅U,pResidual 2 G⁆ : Subgroup G) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : Function.Surjective f)
    (he : ∀ (g : G) (hg : q g ∈ L) (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) = N (e ⟨q g,hg⟩) (f v))
    (hk : ∀ (v : Additive (⁅U,pResidual 2 G⁆ : Subgroup G)),
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G))
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G)
    (P : CharacteristicPair (baumann (T : Subgroup G))) (hD : P.Universal.{u,u}) :
    Alternatives P.first P.second (inclusion (show baumann (T : Subgroup G) ≤
      pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) := by
  let e0 := inclusion (show baumann (T : Subgroup G) ≤
      pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)
  exact hD _ e0 (normal_layer_selected_localClass T hP U hU hJ q hq hker L e hF
    f hf he hk hspan hfit)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
