module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Classes
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CorePreimage
public import Theory.GroupTheory.DoubleCoverInvolutionLifting

/-!
# Lifting the two-central HS class through its literal double cover

The concrete elementary eight has fixed letters for each of its elements.
Exhaustive HS involution coverage therefore puts every nonidentity element
in the two-central class: the other class is fixed-point-free. The elementary
subgroup double-cover theorem produces an involution above this eight, and
lifting conjugators gives an involution above every two-central element.
No residual, orbit, or square-lifting hypothesis is required.

Source: Aschbacher–Smith I.2.2(ii), (5a), printed pp.410–412 / PDF pp.421–423.
The finite check uses the existing degree-100 ATLAS carrier conventions.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.BlockNormalizer
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal

theorem twoCentral_of_fixed_letter (x : Carrier) (hx : orderOf x = 2)
    (p : Fin 100) (hp : inclusion x p = p) : TwoCentral x := by
  apply (twoCentral_iff_isConj_e0 x hx).mpr
  rcases ClassCoverage.involution_classes x hx with h | h
  · exact h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    have he : x * g = g * ClassCoverage.t :=
      ((mul_inv_eq_iff_eq_mul).mp hg).symm
    have h := congrArg (fun a : Carrier => inclusion a (inclusion g⁻¹ p)) he
    apply False.elim
    apply ClassCoverage.t_fixedPointFree (inclusion g⁻¹ p)
    apply (inclusion g).injective
    simpa only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply,
      hp] using h.symm

set_option maxRecDepth 10000 in
private theorem small_fixed_letter (j : Fin 8) :
    ∃ p : Fin 100, inclusion (SylowCatalogueData.small j) p = p := by
  have h : ∀ j : Fin 8, ∃ p : Fin 100,
      inclusion (SylowCatalogueData.small j) p = p := by
    apply ClassCoverage.Certificate.allFin
    decide +kernel
  exact h j

theorem baseElementary_twoCentral (x : Carrier) (hx : x ∈ baseElementary)
    (hx2 : orderOf x = 2) : TwoCentral x := by
  let : IsElementaryAbelian 2 baseElementary := elementary_isElementaryAbelian 2
  obtain ⟨j, hj⟩ := SylowCatalogueData.small_of_normal_elementary_element x
    (elementary_le_subgroup 2 hx) (by simpa [hx2] using pow_orderOf_eq_one x) (by
      intro g hg
      have hm : g * x * g⁻¹ ∈ baseElementary :=
        baseElementary_normal.conj_mem ⟨x, elementary_le_subgroup 2 hx⟩ hx ⟨g, hg⟩
      exact setLike_mul_comm hx hm)
  obtain ⟨p, hp⟩ := small_fixed_letter j
  exact twoCentral_of_fixed_letter x hx2 p (hj ▸ hp)

theorem twoCentral_involutions_lift {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (t : Carrier) (ht : orderOf t = 2) (htc : TwoCentral t) :
    ∃ u : K, modelMap e u = t ∧ orderOf u = 2 := by
  have hf : Function.Surjective (modelMap e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center K))
  have hk : Nat.card (modelMap e).ker = 2 := by rw [modelMap_ker, hZ]
  let : IsElementaryAbelian 2 baseElementary := elementary_isElementaryAbelian 2
  obtain ⟨x, hx, hxE, hxne⟩ :=
    Theory.GroupTheory.DoubleCoverInvolutionLifting.exists_involution_above_elementary_subgroup
      (modelMap e) hf hk baseElementary (by rw [baseElementary_card]; decide)
  have hx2 : orderOf (modelMap e x) = 2 := orderOf_eq_prime
    (by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]) hxne
  have hxc := (twoCentral_iff_isConj_e0 _ hx2).mp (baseElementary_twoCentral _ hxE hx2)
  exact Theory.GroupTheory.DoubleCoverInvolutionLifting.involution_lift_of_isConj
    (modelMap e) hf hx (hxc.symm.trans ((twoCentral_iff_isConj_e0 t ht).mp htc))

/-- Every representative above a two-central involution is itself an involution:
changing a lift by the central element of order two preserves its square. -/
theorem order_two_of_twoCentral_image {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    orderOf u = 2 := by
  obtain ⟨v, hv, hv2⟩ := twoCentral_involutions_lift e hZ _ hu hc
  have hs : u ^ 2 = v ^ 2 := square_eq_of_quotient_eq hZ (e.injective hv.symm)
  apply orderOf_eq_prime
  · rw [hs, ← hv2, pow_orderOf_eq_one]
  · intro h
    simp [h] at hu

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
