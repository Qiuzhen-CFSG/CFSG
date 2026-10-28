module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Xi
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.XiPrime

/-!
# The actual ambient cubic automizer of the selected residual

The intrinsic odd quotient of the ambient residual is identified with the
selected subgroup in H/O₂(H). This equivalence intertwines the literal
normalizer action with conjugation. The constructed SL₂(3) action therefore
supplies an element of order three in the ambient quotient automizer.

Source: Aschbacher–Smith 13.3.14(d), printed p.892.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def ambientResidualCoreEquiv
    (H : Subgroup G) (D : Subgroup (Star H)) (hp : Odd p) (hD : IsPGroup p D) :
    Chapter1.XiQuotient ((starResidual H D).map H.subtype) ≃* D := by
  let e := (starResidual H D).equivMapOfInjective H.subtype H.subtype_injective
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    (oddStarResidualCoreEquiv H D hp hD)

theorem ambientResidualCoreEquiv_mk (H : Subgroup G) (D : Subgroup (Star H))
    (hp : Odd p) (hD : IsPGroup p D) (v : starResidual H D) :
    (ambientResidualCoreEquiv H D hp hD (QuotientGroup.mk' _
      ((starResidual H D).equivMapOfInjective H.subtype H.subtype_injective v)) : Star H) =
      QuotientGroup.mk' (pCore 2 H) (v : H) := by
  let e := (starResidual H D).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  change (oddStarResidualCoreEquiv H D hp hD (q.symm (q (QuotientGroup.mk' _ v))) : Star H) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

@[expose] noncomputable def residualAmbientNormalizer (H : Subgroup G)
    (D : Subgroup (Star H)) [D.Normal] : H →* normalizer ((starResidual H D).map H.subtype : Set G) := by
  let : (starResidual H D).Normal := starResidual_normal H D
  exact inclusion (by
    have hm := (map_mono (f := H.subtype) (show (⊤ : Subgroup H) ≤ normalizer (starResidual H D : Set H) from
      le_normalizer_of_normal)).trans ((starResidual H D).le_normalizer_map H.subtype)
    intro g hg
    exact hm ⟨⟨g, hg⟩, trivial, rfl⟩)

theorem ambientResidualCoreEquiv_equivariant
    (H : Subgroup G) (D : Subgroup (Star H)) [D.Normal]
    (hp : Odd p) (hD : IsPGroup p D) (h : H)
    (v : Chapter1.XiQuotient ((starResidual H D).map H.subtype)) :
    ambientResidualCoreEquiv H D hp hD
      (Chapter3.xiQuotientNormalizerAction _ (residualAmbientNormalizer H D h) v) =
    MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) h)
      (ambientResidualCoreEquiv H D hp hD v) := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ v
  obtain ⟨v, rfl⟩ := ((starResidual H D).equivMapOfInjective H.subtype H.subtype_injective).surjective v
  let : (starResidual H D).Normal := starResidual_normal H D
  have he : ((starResidual H D).map H.subtype).normalizerMonoidHom
      (residualAmbientNormalizer H D h)
      ((starResidual H D).equivMapOfInjective H.subtype H.subtype_injective v) =
    (starResidual H D).equivMapOfInjective H.subtype H.subtype_injective
      (MulAut.conjNormal h v) := by apply Subtype.ext; rfl
  apply Subtype.ext
  simp only [Chapter3.xiQuotientNormalizerAction, MonoidHom.comp_apply,
    quotientAut_apply_mk, he, ambientResidualCoreEquiv_mk]
  change QuotientGroup.mk' (pCore 2 H) (h * v.val * h⁻¹) = _
  change _ = QuotientGroup.mk' (pCore 2 H) h *
    (ambientResidualCoreEquiv H D hp hD (QuotientGroup.mk' _
      ((starResidual H D).equivMapOfInjective H.subtype H.subtype_injective v)) : Star H) *
      (QuotientGroup.mk' (pCore 2 H) h)⁻¹
  rw [ambientResidualCoreEquiv_mk]
  simp only [map_mul, map_inv]

theorem star_residual_cubic_automizer (H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (D : Subgroup (Star H)) [D.Normal] (hp : Odd p) (hD : IsPGroup p D)
    (hmodel : Nonempty (((MulAut.conjNormal : Star H →* MulAut D).comp
      (starMap H Lplus hLH)).range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    3 ∣ Nat.card (Chapter3.xiQuotientAutomizer ((starResidual H D).map H.subtype)) := by
  let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
  obtain ⟨em⟩ := hmodel
  have hc : Nat.card a.range = 24 := (Nat.card_congr em.toEquiv).trans (by
    rw [Nat.card_eq_fintype_card]; decide)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := a.range) 3 (hc ▸ (by decide))
  obtain ⟨l, hl⟩ := a.rangeRestrict_surjective z
  let x := residualAmbientNormalizer H D (inclusion hLH l)
  apply Chapter3.three_dvd_xiQuotientAutomizer_of_actor _ x
  let E := ambientResidualCoreEquiv H D hp hD
  have he : MulAut.congr E (Chapter3.xiQuotientNormalizerAction _ x) = a l := by
    apply MulEquiv.ext
    intro v
    obtain ⟨v, rfl⟩ := E.surjective v
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change E (Chapter3.xiQuotientNormalizerAction _ x v) =
      MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) (inclusion hLH l)) (E v)
    exact ambientResidualCoreEquiv_equivariant H D hp hD (inclusion hLH l) v
  rw [← (MulAut.congr E).orderOf_eq, he]
  rw [← Subgroup.orderOf_coe] at hz
  exact (congrArg (fun y : a.range => orderOf (y : MulAut D)) hl).trans hz

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
