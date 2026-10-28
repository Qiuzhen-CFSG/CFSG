module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedImages
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayer
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
public import Theory.Representation.SL2NaturalOffenders.NaturalPair.Dimensions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
/-!
# The paired natural Baumann source assembly

Two normal natural SL₂ factors, permuted by the original Sylow subgroup,
have Thompson and Baumann image equal to the Sylow intersection with the
layer. The sharp fixed-space lift gives Thompson codimension 2n; the actual
residual-fixed kernel gives residual codimension 4n. One original residual
conjugator generates the whole layer from the two Thompson images, including
F₂ where that layer is not itself the residual.

These facts discharge all four hypotheses of B.2.18. Its alpha decomposition
and the original centralizer Sylow lift prove the Baumann Sylow conclusion.
Only the genuine earlier B.6.9 marked layer, natural quotient and permutation
remain as inputs; no image, fixed-lift, generation, Frattini or Sylow premise
is assumed. The solvable E.2.3 factor producer supplies these source markers.
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

theorem paired_baumann_sylow_and_alpha
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
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
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
  have heL : ∀ (a : L) v,
      f (NormalElementaryQuotient.representation U q hq hker (a : H) v) =
        SL2NaturalOffenders.naturalPair (F := F) (e a) (f v) := by
    intro a v
    exact (he a v).trans (hnat a (f v).1 (f v).2)
  have hno := noStrong_of_naturalPair_source_layer U q hq hker L hY
    e.toMonoidHom e.injective f hf heL (T : Subgroup G)
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
  have halpha := (two_conjugate_alpha_and_saturation T hP U hU hJ q hker
    (residual_centralizer_le_coreFrattini T hP U hU hJ) hno g hg hgenJ hcod).2.1
  refine ⟨?_,halpha⟩
  apply sylow_lift_of_decomposition U (T : Subgroup G) (pResidual 2 G)
    T.isPGroup' halpha (centralizer_sylow T U)
  let k : (G ⧸ centralizer (U : Set G)) →* H := QuotientGroup.lift _ q hker.symm.le
  have hki : Function.Injective k :=
    (QuotientGroup.injective_lift_iff (centralizer (U : Set G)) q hker.symm.le).mpr hker.symm
  have hmap (A : Subgroup G) : (A.map (actionMap U)).map k = A.map q := by
    rw [map_map]
    rfl
  apply (Chapter1.IsSylowIn.map_iff k hki).mp
  rw [Subgroup.map_sup,hmap,hmap,hBq]
  have hsmall : (pResidual 2 G).map q ⊔ ((T : Subgroup G).map q ⊓ L) ≤ L :=
    sup_le hres inf_le_right
  have hs : Chapter1.IsSylowIn 2 ((T : Subgroup G).map q ⊓ L) L := by
    obtain ⟨P,hPa⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal L
    exact ⟨P,hPa⟩
  exact Chapter1.IsSylowIn.restrict hs le_sup_right hsmall
end CFSG.Quasithin.ChapterB.RankOneBaumann
