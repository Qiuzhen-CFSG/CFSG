module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ModelTransport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Star
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Moved
public import GorensteinWalter.SL2ProjectiveCover
/-!
# The selected rank-one local group has its actual natural module

The original layer-equivariant quotient identifies the selected action image
with SL₂ and the literal moved group with [U,O²(G)]. Its coordinate kernel
is exactly the fixed subgroup required by C.1.17. This constructs the
natural model, preserving the full centralizer quotient and actual lifts.

Source: Aschbacher–Smith C.1.26, p.132, natural branch.
-/
public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
variable {G H : Type*} {F : Type} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem normal_layer_selected_natural
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
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let X := pResidual 2 G ⊔ baumann (T : Subgroup G)
    let b := inclusion (show baumann (T : Subgroup G) ≤ X from le_sup_right)
    Nonempty (NaturalModel b F) := by
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
  let X := pResidual 2 G
  let A := X ⊔ baumann (T : Subgroup G)
  let b := inclusion (show baumann (T : Subgroup G) ≤ A from le_sup_right)
  obtain ⟨c,hc⟩ := normal_layer_selectedStar_equiv T hP U hU hJ q hq hker L e hF f hf he hk hspan
  let d := c.trans e
  let : IsQuasisimple (LocalStar b) := IsQuasisimple.of_mulEquiv d.symm
  have hactor : actorLift b = ⊤ := by
    unfold actorLift
    rw [generalizedFitting_eq_top_of_quasisimple,comap_top]
  obtain ⟨_,ha⟩ := RankOneBaumann.normal_layer_moved_baumann_sylow_and_alpha
    T hP U hU hJ q hq hker L e hF f hf he hk
  have ha' : thompsonAlpha (T : Subgroup G) ≤ ⁅U,X⁆ ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)) :=
    ha.le.trans (sup_le_sup_right inf_le_left _)
  have hm : (moved b).map A.subtype = ⁅U,X⁆ := by
    unfold moved
    rw [hactor]
    exact localV_selected_full_commutator (T : Subgroup G) U
      (pResidual_sup_sylow_eq_top T) hspan ha'
  have hB := normal_layer_moved_baumann_image T hP U hU hJ q hq hker L e hF f hf he hk
  have hr := RankOneBaumann.residual_image_eq_normal_natural_layer T hP q hq L e hF
  have hA : A.map q = L := by
    change (X ⊔ baumann (T : Subgroup G)).map q = L
    rw [Subgroup.map_sup,hr,hB,sup_eq_left.mpr inf_le_right]
  let fg : (⁅U,X⁆ : Subgroup G) →* Multiplicative (Fin 2 → F) := f.toAddMonoidHom.toMultiplicativeRight
  have hfg : Function.Surjective fg := by
    intro w
    obtain ⟨v,hv⟩ := hf w.toAdd
    exact ⟨v.toMul,congrArg Multiplicative.ofAdd hv⟩
  apply naturalModel_of_original_moved_coordinates U X A b q hq hker (hA.trans hr.symm)
    hm F d fg hfg
  · intro w
    exact hk (Additive.ofMul w)
  · intro n w
    have hnL : q (n:G) ∈ L := hA ▸ mem_map_of_mem q n.property
    have hc' : c (QuotientGroup.mk' (localKernel b) n) = ⟨q n,hnL⟩ := Subtype.ext (hc n)
    change f (Additive.ofMul (MulAut.conjNormal (n:G) w)) =
      specialLinearNatural 2 (e (c (QuotientGroup.mk' (localKernel b) n)))
        (f (Additive.ofMul w))
    rw [hc']
    exact he n hnL (Additive.ofMul w)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
