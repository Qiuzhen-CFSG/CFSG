module
public import Theory.Representation.BinaryOffender.NormalLayerQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedAssembly
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
/-!
# Actual paired action and fixed-space lift from layer equivariance

The source's natural quotient need only intertwine its normal product layer.
The kernel is the original residual fixed space and is therefore invariant
under the full group. Reduced minimal-parabolic structure puts the residual
image in the offender layer and makes that layer self-centralizing. Descending
the action along the given quotient constructs the full faithful action,
including the original factor exchange, and proves the paired Baumann
Sylow conclusion and alpha identity.
No ambient representation or whole-group equivariance is an extra premise.
The genuine earlier B.6.9 layer, natural quotient and exchange remain explicit.
Source: Aschbacher–Smith B.6.10 and E.2.3(2), pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
open BaumannArgument
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "V" => Fin 2 → F
theorem paired_layer_action_and_fixedSpace
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D × D)
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ (g : L) v, f (NormalElementaryQuotient.representation U q hq hker (g : H) v) =
      SL2NaturalOffenders.naturalPair (F := F) (e g) (f v))
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q))
    (hY : BinaryOffender.offenderSubgroup
      (NormalElementaryQuotient.representation U q hq hker) ≤ L)
    (hexchange : ∃ t ∈ (T : Subgroup G),
      ((((⊤ : Subgroup D).prod ⊥).map (L.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊥ : Subgroup D).prod ⊤).map (L.subtype.comp e.symm.toMonoidHom)) ∧
      ((((⊥ : Subgroup D).prod ⊤).map (L.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊤ : Subgroup D).prod ⊥).map (L.subtype.comp e.symm.toMonoidHom))) :
    ∃ ρ : Representation (ZMod 2) H (V × V), Function.Injective ρ ∧
      (∀ (g : L) v, ρ (g : H) v = SL2NaturalOffenders.naturalPair (F := F) (e g) v) ∧
      (∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v)) ∧
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L ∧
        (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L) ∧
      BinaryOffender.fixedSpace (NormalElementaryQuotient.representation U q hq hker)
        ((elementaryAbelianMaxJ (T : Subgroup G)).map q) =
        (BinaryOffender.fixedSpace ρ ((elementaryAbelianMaxJ (T : Subgroup G)).map q)).comap f := by
  let α := NormalElementaryQuotient.representation U q hq hker
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hJL := thompson_image_le_offender_layer T U q hq hker hUT L hY
  have hres := residual_image_le_normal_thompson_layer T hP U hU hJ q hq hker L hJL
  have hcore : pCore 2 H = ⊥ := by
    let k := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 k,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hL : centralizer (L : Set H) ≤ L := by
    rw [map_pResidual_of_surjective 2 q hq] at hres
    exact (centralizer_le hres).trans ((centralizer_pResidual_le_of_pCore_eq_bot hcore).trans hres)
  have hstable : ∀ g, f.ker ≤ f.ker.comap (α g) := by
    let : ((pResidual 2 G).map q).Normal := Normal.map inferInstance q hq
    intro g
    rw [hk]
    exact fun v hv => (BinaryOffender.fixedSpace_stable_of_normalizes α
      (le_normalizer_of_normal : (⊤ : Subgroup H) ≤ normalizer ((pResidual 2 G).map q : Set H))
      (mem_top g) v).mpr hv
  let τ := (SL2NaturalOffenders.naturalPair (F := F)).comp e.toMonoidHom
  have hfaith : Function.Injective τ := by
    intro a b hab
    apply e.injective
    apply Prod.ext
    · apply Subtype.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      exact congrArg Prod.fst (LinearMap.congr_fun hab (v,0))
    · apply Subtype.ext
      apply Matrix.ext_iff_mulVec.mpr
      intro v
      exact congrArg Prod.snd (LinearMap.congr_fun hab (0,v))
  obtain ⟨ρ,hρ,heρ,hρL⟩ := BinaryOffender.exists_faithful_action_of_normal_layer_stable_quotient
    α L hL τ hfaith f hf hstable he
  refine ⟨ρ,hρ,hρL,heρ,?_⟩
  exact paired_images_and_fixedSpace T U q hq hker hUT hJ L e ρ hρ
    (fun a v w => hρL a (v,w)) f hf heρ hY hexchange
end CFSG.Quasithin.ChapterB.RankOneBaumann
