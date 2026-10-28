module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.Orders
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# From central-class fusion to embedded J₂ Sylow centers

Conjugate the fixed actual J₂ Sylow subgroup, then transport it through the
supplied full carrier equivalence and the ambient subgroup inclusion. The
injective-image center theorem preserves equality with the entire center.
Cauchy's theorem supplies a generator for each ambient order-two subgroup.

The element-fusion premise is an explicit remaining model calculation. These
transport lemmas do not assert it. Source: Aschbacher–Smith, proof of 16.3.4,
printed p.1178 / PDF p.1195.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory ClassificationModels
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G] {L K : Subgroup G}

omit [Finite G] in
/-- Conjugacy into the checked central class gives an exact ambient Sylow center. -/
theorem j2_sylowCenterEmbedding_of_isConj
    (eK : K ≃* SporadicName.j2.Carrier) (v : K)
    (hv : IsConj FirstFusion.t (eK v)) : SylowCenterEmbedding K (zpowers (v : G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hv
  let e : Carrier ≃* K := (MulAut.conj g).trans eK.symm
  let S₀ := SecondParabolic.sylow FirstParabolic.card_l₁
  let S := S₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : e FirstFusion.t = v := by
    change eK.symm (g * FirstFusion.t * g⁻¹) = v
    rw [hg, eK.symm_apply_apply]
  refine ⟨S, ?_⟩
  change (center (((S₀ : Subgroup Carrier).map e.toMonoidHom).map K.subtype)).map
    (((S₀ : Subgroup Carrier).map e.toMonoidHom).map K.subtype).subtype = _
  rw [Subgroup.map_map]
  rw [map_center_image_of_injective (S₀ : Subgroup Carrier) (K.subtype.comp e.toMonoidHom)
    (K.subtype_injective.comp e.injective), ← Subgroup.map_map]
  change ((center Seed.s).map Seed.s.subtype).map (K.subtype.comp e.toMonoidHom) = _
  rw [SecondParabolic.center_s, MonoidHom.map_zpowers]
  change zpowers (e FirstFusion.t : G) = _
  rw [he]

/-- Element fusion suffices for every order-two subgroup in a component Sylow center. -/
theorem j2_involutionCenterLifting_of_element_fusion
    (eK : K ≃* SporadicName.j2.Carrier) (hLK : L ≤ K)
    (fusion : ∀ v : L, orderOf v = 2 →
      IsConj FirstFusion.t (eK (Subgroup.inclusion hLK v))) :
    InvolutionCenterLifting L K := by
  intro P V hV hcard
  have hVL : V ≤ L := by
    rintro x hx
    obtain ⟨l, _, rfl⟩ := hV hx
    exact l.property
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hcard])
  let l : L := ⟨v, hVL v.property⟩
  let k : K := Subgroup.inclusion hLK l
  have hl : orderOf l = 2 := (orderOf_coe l).symm.trans ((orderOf_coe v).trans hv)
  have hline : zpowers (v : G) = V := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr v.property)
    rw [Nat.card_zpowers, orderOf_coe, hv, hcard]
  rw [← hline]
  exact j2_sylowCenterEmbedding_of_isConj eK k (fusion l hl)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
