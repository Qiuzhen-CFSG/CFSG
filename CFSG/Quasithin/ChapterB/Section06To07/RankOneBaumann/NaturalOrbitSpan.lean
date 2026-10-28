module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.NormalLayerSource
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Source
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.OrbitSpan
/-!
# The natural source's exact alpha orbit span

The sharp two-conjugate dimension calculation makes the two Thompson-fixed
subgroups generate the original module. Applying it to the literal moved
subgroup gives the orbit-span conclusion of E.2.3(2), without splitting U
or replacing its two-closed centralizer by a two-group.
The normal-layer version constructs the full ambient action from the
source's layer-equivariant quotient and its exact residual-fixed kernel.
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
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := F)

theorem natural_thompsonAlpha_orbit_span
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = N g (f v))
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  obtain ⟨hJq,hBq⟩ := thompson_baumann_images_of_natural_quotient T U q hq hker hUT hJ f hf he
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_thompson_images_sup_eq_top T q hq hJq
  have hgenJ : (pResidual 2 G).map q ≤
      (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := hgen.symm ▸ le_top
  have hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G) := by
    rw [thompson_fixedCodim_of_natural_quotient T U q hq hker hUT hJ f hf he,
      residual_fixedCodim_of_natural_kernel U q hq hker f hf hk]
  have halpha := (natural_baumann_sylow_and_alpha T hP U hU hJ q hq hker f hf he hk).2
  exact thompsonAlpha_span_of_two_conjugates T U q hq hker g hg hgenJ hcod
    (halpha.trans (sup_comm _ _))

theorem semilinear_thompsonAlpha_orbit_span
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (hF : 2 < Nat.card F)
    (f : Additive U →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
    (hk : f.ker = BinaryOffender.fixedSpace
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hres := residual_image_eq_normal_natural_layer T hP q hq L e hF
  obtain ⟨hJq,hBq⟩ := thompson_baumann_images_of_semilinear_quotient
    T U q hq hker hUT hJ L e ρ hfaith hnat hF f hf he
  obtain ⟨g,hg,hgen⟩ := exists_residual_conjugate_thompson_images_sup_eq_layer
    T q hq L e hres (elementaryAbelianMaxJ (T : Subgroup G)) hJq
  have hgenJ : (pResidual 2 G).map q ≤
      (elementaryAbelianMaxJ (T : Subgroup G)).map q ⊔
      ((elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom).map q := by
    rw [hres,hgen]
  have hcod : 2 * fixedCodim U (elementaryAbelianMaxJ (T : Subgroup G)) ≤
      fixedCodim U (pResidual 2 G) := by
    rw [thompson_fixedCodim_of_semilinear_quotient T U q hq hker hUT hJ L e ρ hfaith hnat hF f hf he,
      residual_fixedCodim_of_marked_kernel U q hq hker f hf hk]
  have halpha := (semilinear_baumann_sylow_and_alpha T hP U hU hJ q hq hker
    L e ρ hfaith hnat hF f hf he hk).2
  exact thompsonAlpha_span_of_two_conjugates T U q hq hker g hg hgenJ hcod
    (halpha.trans (sup_comm _ _))

theorem normal_layer_thompsonAlpha_orbit_span
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
      (NormalElementaryQuotient.representation U q hq hker) ((pResidual 2 G).map q)) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
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
  exact semilinear_thompsonAlpha_orbit_span T hP U hU hJ q hq hker L e
    ρ hρ hρL hF f hf heρ hk


attribute [local instance] semilinear_moved_elementary

theorem normal_layer_moved_thompsonAlpha_orbit_span
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
      f v = 0 ↔ (v.toMul : G) ∈ centralizer (pResidual 2 G : Set G)) :
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
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
  exact normal_layer_thompsonAlpha_orbit_span T hP W (hU.moved U) hJW
    q hq hkerW L e hF f hf heW hkW
end CFSG.Quasithin.ChapterB.RankOneBaumann
