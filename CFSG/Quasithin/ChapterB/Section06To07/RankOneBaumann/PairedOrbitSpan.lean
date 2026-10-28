module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedLayerSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.OrbitSpan
/-!
# Alpha orbit span on a paired natural quotient

The original paired action gives the sharp Thompson and residual
codimensions and a residual conjugator generating both factor images.
The two fixed spaces therefore span U. The genuine source decomposition
will identify U plus the fixed alpha summand with the corresponding moved
subgroup plus that same summand. No ambient action or fixed-space lift is
assumed in the layer-equivariant version.
Source: Aschbacher–Smith B.6.10 and E.2.3(2), printed pp.117 and216–217.
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

theorem paired_thompsonAlpha_orbit_span
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D × D)
    (ρ : Representation (ZMod 2) H (V × V)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
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
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  obtain ⟨⟨hJq,hBq⟩,hfix⟩ := paired_images_and_fixedSpace
    T U q hq hker hUT hJ L e ρ hfaith hnat f hf he hY hexchange
  have hres := residual_image_le_normal_thompson_layer T hP U hU hJ q hq hker L
    (hJq.le.trans inf_le_right)
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_thompson_images_sup_eq_pair T q hq
    L e (elementaryAbelianMaxJ (T : Subgroup G)) hJq
  have hgenJ : (pResidual 2 G).map q ≤
      (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [hgen]
    exact hres
  have hJcod : fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) =
      2 * Module.finrank (ZMod 2) F := by
    rw [fixedCodim_eq_centralizer_quotient U q hq hker]
    rw [SL2NaturalOffenders.fixedCodim_eq_of_fixedSpace_comap
      (NormalElementaryQuotient.representation U q hq hker) ρ f hf _ hfix,hJq]
    obtain ⟨P,hPa⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal L
    change (P : Subgroup L).map L.subtype = (T : Subgroup G).map q ⊓ L at hPa
    rw [←hPa]
    exact SL2NaturalOffenders.paired_sylowImage_fixedCodim L e ρ
      (fun a v => hnat a v.1 v.2) P
  have hRcod : fixedCodim U (pResidual 2 G) = 4 * Module.finrank (ZMod 2) F := by
    rw [fixedCodim_eq_centralizer_quotient U q hq hker,BinaryOffender.fixedCodim,←hk]
    exact (f.quotKerEquivOfSurjective hf).finrank_eq.trans (by
      simp [Module.finrank_prod,Module.finrank_pi_fintype]
      omega)
  have hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G) := by rw [hJcod,hRcod]; omega
  have halpha := (paired_baumann_sylow_and_alpha T hP U hU hJ q hq hker
    L e ρ hfaith hnat f hf he hk hY hexchange).2
  exact thompsonAlpha_span_of_two_conjugates T U q hq hker g hg hgenJ hcod
    (halpha.trans (sup_comm _ _))

theorem paired_layer_thompsonAlpha_orbit_span
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
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
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
  exact paired_thompsonAlpha_orbit_span T hP U hU hJ q hq hker L e ρ hρ
    (fun a v w => hρL a (v,w)) f hf heρ hk hY hexchange
end CFSG.Quasithin.ChapterB.RankOneBaumann
