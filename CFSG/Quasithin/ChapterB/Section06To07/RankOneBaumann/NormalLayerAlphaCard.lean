module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayerSource
/-!
# Alpha cardinality for a single natural layer

When the prescribed Sylow has trivial residual centralizer, the natural
coordinate map is injective. The module has binary dimension twice the
field degree and its Thompson fixed codimension is the field degree.
The source alpha decomposition therefore gives alpha the field order.
The moved version uses the original commutator and its exact centralizer,
without assuming a splitting of the original module.

Source: Aschbacher--Smith B.6.10 and E.2.3(1), used on printed p.746.
-/
public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)
set_option backward.isDefEq.respectTransparency false
theorem normal_layer_alpha_card_of_trivial_sylow_residual_centralizer
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D) (hF : 2 < Nat.card F)
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ (g : L) v,
      f (NormalElementaryQuotient.representation U q hq hker (g : H) v) = N (e g) (f v))
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q))
    (hz : (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) = ⊥) :
    Nat.card (thompsonAlpha (T : Subgroup G)) = Nat.card F := by
  have hres := residual_image_eq_normal_natural_layer T hP q hq L e hF
  have hcore : pCore 2 H = ⊥ := by
    let k := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 k,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hL : centralizer (L : Set H) ≤ L := by
    rw [←hres,map_pResidual_of_surjective 2 q hq]
    exact centralizer_pResidual_le_of_pCore_eq_bot hcore
  have hfaith : Function.Injective (MonoidHom.comp N e.toMonoidHom) := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact LinearMap.congr_fun hab v
  obtain ⟨ρ,hρ,heρ,hρL⟩ := BinaryOffender.exists_faithful_action_of_normal_layer_quotient
    (NormalElementaryQuotient.representation U q hq hker) L hL
    (MonoidHom.comp N e.toMonoidHom) hfaith f hf (hk.trans (congrArg _ hres)) he
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hαT : thompsonAlpha (T : Subgroup G) ≤ T := by
    intro x hx
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    exact hJT ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hcentral : thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hαT).trans_eq hz)
  have hα := (semilinear_baumann_sylow_and_alpha T hP U hU hJ q hq hker L e
    ρ hρ hρL hF f hf heρ hk).2
  rw [hcentral,bot_sup_eq] at hα
  let α := NormalElementaryQuotient.representation U q hq hker
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hvc := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker (pResidual 2 G) v).mp
      (hk ▸ hv)
    have heq := mem_bot.mp (hz ▸ (show (v.toMul:G) ∈
      (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) from ⟨hUT v.toMul.property,hvc⟩))
    change v = 0
    exact Additive.toMul.injective (Subtype.ext heq)
  have hdim : Module.finrank (ZMod 2) (Additive U) = 2 * Module.finrank (ZMod 2) F := by
    calc
      _ = Module.finrank (ZMod 2) (Fin 2 → F) := (LinearEquiv.ofBijective f ⟨hinj,hf⟩).finrank_eq
      _ = _ := by simp [Module.finrank_pi_fintype]
  have hcod : BinaryOffender.fixedCodim α ((elementaryAbelianMaxJ (T : Subgroup G)).map q) =
      Module.finrank (ZMod 2) F := by
    rw [←fixedCodim_eq_centralizer_quotient U q hq hker]
    exact thompson_fixedCodim_of_semilinear_quotient T U q hq hker hUT hJ L e ρ hρ hρL hF f hf heρ
  have hrank : Module.finrank (ZMod 2)
      (BinaryOffender.fixedSpace α ((elementaryAbelianMaxJ (T : Subgroup G)).map q)) =
      Module.finrank (ZMod 2) F := by
    have hh := BinaryOffender.fixedCodim_add_finrank α ((elementaryAbelianMaxJ (T : Subgroup G)).map q)
    rw [hcod,hdim] at hh
    omega
  rw [hα,←Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q hq hker
    (elementaryAbelianMaxJ (T : Subgroup G)))]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hrank]
  simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm

attribute [local instance] semilinear_moved_elementary

theorem normal_layer_moved_alpha_card_of_trivial_sylow_residual_centralizer
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
    (hz : (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G) = ⊥) :
    Nat.card (thompsonAlpha (T : Subgroup G)) = Nat.card F := by
  let W := ⁅U,pResidual 2 G⁆
  have hCW : centralizer (W : Set G) = centralizer (U : Set G) := hU.centralizer_moved_eq U
  have hkerW : q.ker = centralizer (W : Set G) := hker.trans hCW.symm
  have hJW : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) :=
    fun h => hJ (h.trans_eq hCW)
  have heW : ∀ (a : L) v,
      f (NormalElementaryQuotient.representation W q hq hkerW (a : H) v) = N (e a) (f v) := by
    intro a v
    obtain ⟨g,hga⟩ := hq a
    have hgaL : q g ∈ L := hga.symm ▸ a.property
    have hv : NormalElementaryQuotient.representation W q hq hkerW (a : H) v =
        Additive.ofMul (MulAut.conjNormal g v.toMul) := by
      rw [←hga]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact NormalElementaryQuotient.representation_apply W q hq hkerW g v
    rw [hv]
    have hh := he g hgaL v
    have haa : (⟨q g,hgaL⟩ : L) = a := Subtype.ext hga
    rwa [haa] at hh
  have hkW : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation W q hq hkerW) ((pResidual 2 G).map q) := by
    ext v
    rw [NormalElementaryQuotient.mem_fixedSpace_image W q hq hkerW]
    exact hk v
  exact normal_layer_alpha_card_of_trivial_sylow_residual_centralizer T hP W (hU.moved U) hJW
    q hq hkerW L e hF f hf heW hkW hz

end CFSG.Quasithin.ChapterB.RankOneBaumann
