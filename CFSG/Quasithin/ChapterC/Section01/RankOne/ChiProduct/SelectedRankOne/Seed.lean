module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.BlockSelection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Movement
/-!
# The genuine outside moved χ-block in the normal rank-one source branch

The actual local-class constructor and a single uniform characteristic pair
produce the residual block outside characteristic-normalizer control. The
original action supplies its Thompson movement through the Frattini kernel.
Its nonzero commutator with the given reduced module is exactly the block
module, so its source support is a proved conclusion.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–133.
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
theorem normal_layer_outside_moved_chi
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
    (P : CharacteristicPair (baumann (T : Subgroup G))) (hD : P.Universal.{u,u})
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hM : M ≠ ⊤) :
    ¬ pResidual 2 G ≤ M ∧ IsChiBlockIn (pResidual 2 G) ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ := by
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  have hTM : (T : Subgroup G) ≤ M := T.toSubgroup.le_normalizer.trans
    ((normalizer_le_characteristicNormalizerClosure_self (T : Subgroup G) hTne).trans hcpu)
  have hXM : ¬ pResidual 2 G ≤ M := by
    intro hx
    exact hM (top_unique ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le hx hTM)))
  let X := pResidual 2 G
  let B := baumann (T : Subgroup G)
  let A := X ⊔ B
  have hout : ¬ A ≤ M := fun ha => hXM (le_sup_left.trans ha)
  have hlocal := normal_layer_selected_localClass T hP U hU hJ q hq hker L e hF
    f hf he hk hspan hfit
  have hb := blockAlternative_of_selected_outside (T : Subgroup G) A M le_sup_right hcpu hout P hD hlocal
  have hblock := chi_residual_of_selected_block T hb
  have hWne : ⁅U,X⁆ ≠ ⊥ := by
    intro heq
    apply hJ
    rw [←hU.centralizer_moved_eq U]
    intro j hj w hw
    have hw1 : w = 1 := mem_bot.mp (heq ▸ hw)
    rw [hw1]
    simp
  have hsupport := blockU_eq_nontrivial_normal_module_commutator X U hblock.1 hWne
  have hr := RankOneBaumann.residual_image_eq_normal_natural_layer T hP q hq L e hF
  let c := (MulEquiv.subgroupCongr hr).trans e
  have hcard : Nat.card F = 2 ^ Module.finrank (ZMod 2) F := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F))
  have hn : 2 ≤ Module.finrank (ZMod 2) F := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show Module.finrank (ZMod 2) F ≤ 1 by omega)
    rw [←hcard] at hp
    norm_num at hp
    omega
  have hlarge : 3 < Nat.card F := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    rw [←hcard] at hp
    norm_num at hp
    omega
  let : Group.IsPerfect D := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : IsQuasisimple D := ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  have hqs : IsQuasisimple (X.map q) := IsQuasisimple.of_mulEquiv c.symm
  have hz : center (X.map q) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hm := (centerCongr c ⟨x,hx⟩).property
    change c x ∈ center D at hm
    rw [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot] at hm
    exact c.injective ((mem_bot.mp hm).trans (map_one c.toMonoidHom).symm)
  have him := normal_layer_moved_baumann_image T hP U hU hJ q hq hker L e hF f hf he hk
  have hJL : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ X.map q := by
    rw [hr]
    exact (map_mono (elementaryAbelianMaxJ_le_baumann (T : Subgroup G))).trans
      (him.le.trans inf_le_right)
  exact ⟨hXM,hblock,residual_moved_of_quasisimple_image T hP U hU hJ q hq hker hqs hJL hz,hsupport⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
